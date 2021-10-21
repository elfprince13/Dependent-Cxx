#include <array>
#include <iostream>
#include <optional>
#include <string_view>
#include <tuple>
#include <typeinfo>
#include <type_traits>
#include <utility>
#include <variant>

#include <boost/preprocessor/stringize.hpp>

template<char ...Cs> struct CharList {};
template<class CL, class ...TPs>
struct TypeParamCharList {
	template<size_t ...VPs>
	struct ValueParamCharList {};
};

template<char ...Cs>
std::ostream& operator<<(std::ostream& out, CharList<Cs...>) {
	constexpr static const std::array<const char, sizeof...(Cs)> data{Cs...};
	static_assert(data.back() == 0, "Must be null terminated");
	return (out << data.data());
}

template<class CL, class ...TPs, size_t ...VPs>
std::ostream& operator<<(std::ostream& out, typename TypeParamCharList<CL, TPs...>::template ValueParamCharList<VPs...>) {
	out << "<" << CL{};
	(... , (out << ", " << typeid(TPs).name()));
	out << ">::<";
	(... , (out << VPs << ","));
	return out << ">";
}

template<class Root, class ...Trail> struct ContextTag {};
template<class Root, class ...Trail>
constexpr auto makeContext(Root, Trail...) {
	return ContextTag<Root, Trail...>{};
}

namespace detail {
	template<class CT>
	struct is_context_tag { constexpr static const bool value = false; };
	template<class Root, class ...Tail>
	struct is_context_tag<ContextTag<Root, Tail...>>  { constexpr static const bool value = true; };
	
	template<class CT>
	struct fixed_point {};
	
	template<class CL>
	struct is_fixed_point { constexpr static const bool value = false; };
	template<class CL>
	struct is_fixed_point<fixed_point<CL>> {
		constexpr static const bool value = true;
		//static_assert(is_context_tag<CL>::value, "fixed_point should only be used on context tags");
	};
}

template<class Root, class ...Trail>
std::ostream& operator<<(std::ostream& out, ContextTag<Root, Trail...>) {
	out << "Context<" << Root{};
	(... , (out << ", " << Trail{}));
	return out << ">";
}

template<class CompareContext, class Left, class Right>
struct Equivalent {
	static_assert(detail::is_context_tag<CompareContext>::value, "CompareContext must be a context tag");
	static_assert(detail::is_context_tag<Left>::value, "Left must be a context tag");
	static_assert(detail::is_context_tag<Right>::value, "Right must be a context tag");
};

template<class RootC, class ...TrailC,
         class RootL, class ...TrailL,
         class RootR, class ...TrailR>
class Equivalent<ContextTag<RootC, TrailC...>, ContextTag<RootL, TrailL...>, ContextTag<RootR, TrailR...>> {
	constexpr static const bool SameRoot = std::is_same_v<RootC, RootL> && std::is_same_v<RootC, RootR>;
	constexpr static const bool SameComps = std::is_same_v<ContextTag<RootL, TrailL...>, ContextTag<RootR, TrailR...>>;
	constexpr static const bool AnyRecursion = ((... || detail::is_fixed_point<TrailL>::value) ||
												(... || detail::is_fixed_point<TrailR>::value));
public:
	constexpr static const bool value = SameRoot && SameComps;
	static_assert(SameRoot, "Cannot compare contexts which do not share a root and/or which are being inspected outside their root context. Consider calling RefreshType on Left and Right within the CompareContext");
	static_assert(!AnyRecursion || !SameComps, "Left and Right tags are equivalent but contain recursive fixed points and thus cannot be guaranteed unique. Consider re-rooting in a fresh context");
};


namespace detail {
	/*
	template<size_t N> using CharArrayRef = const char(&)[N];
	template<size_t N>
	class String {
		template<typename Indices, CharArrayRef<N> Literal>
		struct Helper {};
		template<size_t ...I, CharArrayRef<N> Literal>
		struct Helper<std::index_sequence<I...>, Literal> {
			using type = CharList<Literal[I]...>;
		};
	public:
		template<CharArrayRef<N> Literal>
		struct apply {
			using type = typename Helper<std::make_index_sequence<N>, Literal>::type;
		};
	};
	*/
	
	template<class StringHolder, size_t ...I>
	constexpr auto StrToCharListImpl(StringHolder holder, std::index_sequence<I...>) {
		constexpr std::string_view text{holder()};
		return CharList<text[I] ...>();
	}
	
	template<class StringHolder>
	constexpr auto StrToCharList(StringHolder holder) {
		return StrToCharListImpl(holder,
								 std::make_index_sequence<std::string_view{holder()}.length() + 1>{});
	}
}

#define StrToCharList(X) detail::StrToCharList([]() constexpr { return (X); })

namespace detail {
	
	template<class CT>
	std::ostream& operator<<(std::ostream& out, fixed_point<CT>) {
		return out << "fixed_point{" << CT{} << "}";
	}
	
	template<class CTIn, class CTOut, class FP>
	struct CutFixedPoint {};
	
	template<class ...Outs, class FP>
	struct CutFixedPoint<std::tuple<>, std::tuple<Outs...>, FP> {
		using type = ContextTag<Outs...>; // no fixed-point encountered;
	};
	
	template<class ...Ins, class ...Outs, class FP>
	struct CutFixedPoint<std::tuple<fixed_point<FP>, Ins...>, std::tuple<Outs...>, FP> {
		using type = ContextTag<Outs...,fixed_point<FP>>;
	};
	
	template<class In, class ...Ins, class ...Outs, class FP>
	struct CutFixedPoint<std::tuple<In, Ins...>, std::tuple<Outs...>, FP> {
		using type = typename CutFixedPoint<std::tuple<Ins...>, std::tuple<Outs...,In>, FP>::type;
	};
	
	template<class CT, class P>
	struct PushContext {
		static_assert(is_context_tag<CT>::value, "CT must be a context tag");
	};
	
	template<class Root, class ...Tail, class P>
	struct PushContext<ContextTag<Root, Tail...>, P> {
		constexpr static const bool AnyRecursion = (std::is_same_v<Root, P> || ... || std::is_same_v<Tail, P>);
		constexpr static const bool KnownRecursion = (std::is_same_v<Root, fixed_point<P>> || ... || std::is_same_v<Tail, fixed_point<P>>);
		//using type = ContextTag<Root, Tail..., P>;
		//*
		using type = std::conditional_t<AnyRecursion,
		                                std::conditional_t<KnownRecursion,
		                                                   typename CutFixedPoint<std::tuple<Root,Tail...>,std::tuple<>,P>::type,
														   ContextTag<Root, Tail..., fixed_point<P>>>,
		                                ContextTag<Root, Tail..., P>>;
		 //*/
	};
	/*
	template<class ...Front, class ...Back, class P>
	struct PushContext<ContextTag<Front..., P, Back...>, P> {
		using type = ContextTag<Front..., P, Back..., fixed_point<P>>;
	};
	
	template<class ...Front, class ...Back, class P>
	struct PushContext<ContextTag<Front..., fixed_point<P>, Back...>, P> {
		using type = ContextTag<Back..., fixed_point<P>>;
	};
	 */
}
template<class CT, class P>
constexpr auto pushContext(CT context, P p) {
	return typename detail::PushContext<CT, P> ::type{};
}

template<class Tag, class V> struct Fresh : Tag {
	const V v;
};

template<class Tag, class V> Fresh(Tag, V) -> Fresh<Tag, V>;

template<class C>
struct is_fresh { constexpr static const bool value = false; };
template<class Tag, class V>
struct is_fresh<Fresh<Tag,V>> { constexpr static const bool value = true; };

template<auto V> struct Constant {
	const decltype(V) v;
};

template<class C>
struct is_constant { constexpr static const bool value = false; };
template<auto V>
struct is_constant<Constant<V>> { constexpr static const bool value = true; };

template<class Tag, class V>
std::ostream& operator<<(std::ostream& out, const Fresh<Tag, V>& fresh) {
	return out << "Fresh{" << (Tag)fresh << ", " << fresh.v << "}";
}

template<auto V>
std::ostream& operator<<(std::ostream& out, const Constant<V>) {
	return out << "Constant{" << V << "}";
}



namespace detail {
	template<class CContext, class LContext, class LV, class RContext, class RV>
	constexpr bool dependEquiv(Fresh<LContext,LV>, Fresh<RContext,RV>) {
		return Equivalent<CContext, LContext, RContext>::value;
	}
}

#define DEPEND_EQUIV(Left, Right) (detail::dependEquiv<Context>(Left, Right))

#define LocCL StrToCharList(__FILE__ ":" BOOST_PP_STRINGIZE(__LINE__) "#" BOOST_PP_STRINGIZE(__COUNTER__))
#define FreshType(X) Fresh{pushContext(Context{},LocCL), X}
#define RootFrame(name) auto name = makeContext(LocCL); using Context = decltype(name)
#define FreshFrame(name) auto name = pushContext(ParentContext{},LocCL); using Context = decltype(name)

#define RefreshType(X) Fresh{pushContext(Context{},LocCL), X.v}

template<typename UniqueContext, typename V>
class Return {
	template<typename V_, typename ParentContext>
	friend auto makeReturn(ParentContext);
	Return() = default;
public:
	Fresh<UniqueContext, V> operator()(V v) && {
		return Fresh{UniqueContext{}, v};
	}
};

template<typename V_, typename ParentContext>
auto makeReturn(ParentContext) {
	FreshFrame(context);
	return Return<Context, V_>{};
}

#define MakeReturn(V) makeReturn<V>(pushContext(Context{},LocCL))


namespace algebra {
	template<class Op>
	struct is_binary_operator { constexpr static const bool value = false; };
	template<template<class L, class R> class Deriving, class L, class R>
	struct is_binary_operator<Deriving<L,R>> { constexpr static const bool value = true; };
	
	template<class Op>
	struct is_unary_operator { constexpr static const bool value = false; };
	template<template<class A> class Deriving, class A>
	struct is_unary_operator<Deriving<A>> { constexpr static const bool value = true; };
	
	template<class Deriving>
	struct commutative {
		static_assert(is_binary_operator<Deriving>::value, "commutative subclass must be a binary operator");
	};
	
	template<template<class L, class R> class Deriving, class L, class R>
	struct commutative<Deriving<L,R>> {
		constexpr operator Deriving<R,L> () const { return Deriving<R,L> {}; };
	protected:
		commutative() = default;
	};
	
	template<class Op>
	struct is_commutative { constexpr static const bool value = false; };
	
	template<class Deriving>
	struct is_commutative<commutative<Deriving>> { constexpr static const bool value = true; };
	
	
	template<class Deriving>
	struct transitive {
		static_assert(is_binary_operator<Deriving>::value, "transitive subclass must be a binary operator");
	};
	
	template<template<class L, class R> class Deriving, class L, class R>
	struct transitive<Deriving<L,R>> {
		template<typename LL>
		constexpr Deriving<LL,R> operator()(Deriving<LL,L>) const { return Deriving<LL,R>{}; }
		template<typename RR>
		constexpr Deriving<L,RR> operator()(Deriving<R,RR>) const { return Deriving<L,RR>{}; }
	protected:
		constexpr transitive() = default;
	};
	
	template<class Op>
	struct is_transitive { constexpr static const bool value = false; };
	
	template<class Deriving>
	struct is_transitive<transitive<Deriving>> { constexpr static const bool value = true; };
	
	
	enum Dir {
		Decreasing,
		Increasing
	};
	
	template<class Deriving, Dir = Increasing>
	struct strict_monotonic {
		static_assert(is_unary_operator<Deriving>::value, "strict_monotonic subclass must be a binary operator");
	};
	
	template<class Left, class Right>
	struct less_than
	: protected transitive<less_than<Left, Right>> {
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only compare fresh variables and constants");
	protected:
		using Self = less_than<Left, Right>;
		constexpr less_than() = default;
	public:
		using transitive<Self>::operator();
		
		constexpr static std::optional<Self> apply(const Left& left, const Right& right) {
			if(left.v < right.v) {
				return Self{};
			} else {
				return std::nullopt;
			}
		}
	};
	
	template<class Left, class Right>
	struct equal_to
	: protected transitive<equal_to<Left, Right>>
	, protected commutative<equal_to<Left, Right>>{
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only compare fresh variables and constants");
	protected:
		using Self = equal_to<Left, Right>;
		constexpr equal_to() = default;
	public:
		using transitive<Self>::operator();
		using commutative<Self>::operator equal_to<Right, Left>;
		
		constexpr static std::optional<Self> apply(const Left& left, const Right& right) {
			if(left.v == right.v) {
				return Self{};
			} else {
				return std::nullopt;
			}
		}
	};
	
	template<template<class A> class Deriving, class A, Dir dir>
	struct strict_monotonic<Deriving<A>, dir> {
		template<class LT> using LTTransform = less_than<Deriving<LT>,Deriving<A>>;
		template<class GT> using GTTransform = less_than<Deriving<A>,Deriving<GT>>;
		template<template<class B> class T, template<class Bp> class Tp, class B>
		using Swap = std::conditional<dir == Increasing, T<B>, Tp<B>>;
		static_assert((dir == Increasing) || (dir == Decreasing), "Incomplete case analysis");
		
		template<typename Eq>
		constexpr equal_to<Deriving<A>,Deriving<Eq>> operator()(equal_to<A,Eq>) const {
			return equal_to<Deriving<A>,Deriving<Eq>>{};
		}
		template<typename LT>
		constexpr Swap<LTTransform,GTTransform,LT> operator()(less_than<LT,A>) const {
			return {};
		}
		template<typename GT>
		constexpr Swap<GTTransform,LTTransform,GT> operator()(less_than<A,GT>) const {
			return {};
		}
	protected:
		constexpr strict_monotonic() = default;
	};
	
	template<class Context, class Left, class Right>
	struct PositiveDivision;
	
	template<template<class ...Args> class Functor, class Arg>
	struct CurryL {
		template<typename ...RemArgs> using type = Functor<Arg, RemArgs...>;
	};
	
	template<template<class ...Args> class Functor, class Arg>
	struct CurryR {
		template<typename ...RemArgs> using type = Functor<RemArgs..., Arg>;
	};
	
	template<class Context, class Left, class Right>
	struct PositiveDivision
	: strict_monotonic<typename CurryR<PositiveDivision, Right>::template type<Left>, Increasing>
	, strict_monotonic<typename CurryL<PositiveDivision, Left>::template type<Right>, Decreasing> {
		static_assert(detail::is_context_tag<Context>::value, "Context must be context");
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only divide fresh variables and constants");
		using strict_monotonic<typename CurryR<PositiveDivision, Right>::template type<Left>, Increasing>::operator();
		using strict_monotonic<typename CurryL<PositiveDivision, Left>::template type<Right>, Decreasing>::operator();
		
		//FreshType(result);
		
		//constexpr PositiveDivision(Context, less_than<Constant<0>, Left>,less_than<Constant<0>, Right>)
		//: result() {}
	};
	
	using TwoThirds = PositiveDivision<ContextTag<CharList<'D','u','m','m','y','\0'>>, Constant<2>, Constant<3>>;
}

template<class ParentContext, class VarContext>
auto inc(Fresh<VarContext, int> var) {
	FreshFrame(context);
	return FreshType(var.v + 1);
}

auto bad() {
	RootFrame(context);
	return FreshType(2);
}

template<class ParentContext, class ReturnContext, class VarContext>
constexpr Fresh<ReturnContext, int> log2(Return<ReturnContext, int> rGen, Fresh<VarContext, int> var, algebra::less_than<Constant<0>,decltype(var)> gt0) {
	FreshFrame(context);
	if(auto maybeProof = algebra::less_than<Constant<1>,decltype(var)>::apply(Constant<1>{}, var);
	   std::nullopt == maybeProof) {
		return std::move(rGen)(0);
	} else {
		auto gt1 = *maybeProof;
		auto nextArg = FreshType(var.v / 2);
		//auto nextReturn = log2<Context>(MakeReturn(int), nextArg, gt0);
		//return std::move(rGen)(1 + nextReturn.v);
		return std::move(rGen)(0);
	}
}

int main(int argc, const char* argv[]) {
	RootFrame(context);
	auto foo = FreshType(0);
	auto bar = FreshType(1);
	auto baz = inc<Context>(foo);
	std::cout << foo << ", " << foo.v << std::endl;
	std::cout << bar << ", " << bar.v << std::endl;
	std::cout << baz << ", " << baz.v << std::endl;
	std::cout << DEPEND_EQUIV(foo, foo) << std::endl;
	std::cout << DEPEND_EQUIV(foo, bar) << std::endl;
	std::cout << DEPEND_EQUIV(foo, baz) << std::endl;
	//std::cout << DEPEND_EQUIV(bad(), bad()) << std::endl;
	std::cout << DEPEND_EQUIV(RefreshType(bad()), RefreshType(bad())) << std::endl;
	auto v32 = FreshType(32);
	if(auto proofPositive = algebra::less_than<Constant<0>,decltype(v32)>::apply(Constant<0>{}, v32);
	   std::nullopt == proofPositive) {
		auto logOf32 = log2<Context>(MakeReturn(int),v32,*proofPositive);
		std::cout << "log_2(" << v32 << ") = " << logOf32 << std::endl;
	} else {
		std::cerr << "Can't take log of negative number" << std::endl;
	}
	return 0;
}
