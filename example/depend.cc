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

namespace detail {
	template<size_t ...Nums>
	struct Unique {};

	/*
	template<class CL, class ...TPs>
	struct TypeParamCharList {
		template<size_t ...VPs>
		struct ValueParamCharList {};
	};
	*/

	template<size_t ...Nums>
	std::ostream& operator<<(std::ostream& out, Unique<Nums...>) {
		out <<"Unique<";
		(..., (out << Nums << ","));
		return out << ">";
	}
	/*
	template<class CL, class ...TPs, size_t ...VPs>
	std::ostream& operator<<(std::ostream& out, typename TypeParamCharList<CL, TPs...>::template ValueParamCharList<VPs...>) {
		out << "<" << CL{};
		(... , (out << ", " << typeid(TPs).name()));
		out << ">::<";
		(... , (out << VPs << ","));
		return out << ">";
	}
	 */
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
	};
}

template<class Root, class ...Trail>
std::ostream& operator<<(std::ostream& out, ContextTag<Root, Trail...>) {
	out << "Context<" << Root{};
	(... , (out << ", " << Trail{}));
	return out << ">";
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
	constexpr Constant() : v(V) {}
};

template<class C>
struct is_constant { constexpr static const bool value = false; };
template<auto V>
struct is_constant<Constant<V>> { constexpr static const bool value = true; };

using Zero = Constant<0>;
using One = Constant<1>;
using Two = Constant<2>;

template<class Tag, class V>
std::ostream& operator<<(std::ostream& out, const Fresh<Tag, V>& fresh) {
	return out << "Fresh{" << (Tag)fresh << ", " << fresh.v << "}";
}

template<auto V>
std::ostream& operator<<(std::ostream& out, const Constant<V>) {
	return out << "Constant{" << V << "}";
}

template<class Validator, class Term>
class CanValidate {
	static_assert(detail::is_context_tag<Validator>::value, "Validator must be a context tag");
	static_assert(is_fresh<Term>::value || is_constant<Term>::value, "Term must be a context tag");
};

template<class Validator, auto V>
class CanValidate<Validator, Constant<V>> {
public:
	constexpr static const bool value = true;
};


template<class RootV, class ...TrailV,
         class RootT, class ...TrailT, class TV>
class CanValidate<ContextTag<RootV, TrailV...>, Fresh<ContextTag<RootT, TrailT...>, TV>> {
protected:
	constexpr static const bool SameRoot = std::is_same_v<RootV, RootT>;
	constexpr static const bool AnyRecursion = (... || detail::is_fixed_point<TrailT>::value);
public:
	constexpr static const bool value = SameRoot && !AnyRecursion;
};

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
}
template<class CT, class P>
constexpr auto pushContext(CT context, P p) {
	return typename detail::PushContext<CT, P> ::type{};
}

namespace detail {
	template<class CContext, class LContext, class LV, class RContext, class RV>
	constexpr bool dependEquiv(Fresh<LContext,LV>, Fresh<RContext,RV>) {
		return Equivalent<CContext, LContext, RContext>::value;
	}
}

#define DEPEND_EQUIV(Left, Right) (detail::dependEquiv<Context>(Left, Right))

#define UNIQUE detail::Unique<__LINE__, __COUNTER__>
#define FreshType(X) Fresh{pushContext(Context{},UNIQUE{}), X}
#define RootFrame() using Context = ContextTag<UNIQUE>
#define FreshFrame() using Context = typename detail::PushContext<ParentContext,UNIQUE>::type

#define RefreshType(X) Fresh{pushContext(Context{},UNIQUE{}), X.v}

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
	FreshFrame();
	return Return<Context, V_>{};
}

#define MakeReturn(V) makeReturn<V>(pushContext(Context{},UNIQUE{}))

template <template <typename...> class OP, typename...Ts>
struct tbind;

template<size_t N>
struct _TP {};

namespace _detail {
	template <template <typename...> class OP, typename PARAMS, typename...Ts>
	struct tbind_impl;
	
	template <template <typename...> class OP, typename...Ss>
	struct tbind_impl<OP, std::tuple<Ss...>>
	{
		template<typename...Us>
		using ttype = OP<Ss...>;
	};
	
	template <template <typename...> class OP, typename T, typename...Ts, typename...Ss>
	struct tbind_impl<OP, std::tuple<Ss...>, T, Ts...>
	{
		template<typename...Us>
		using ttype = typename tbind_impl<
		OP
		, std::tuple<Ss..., T>
		, Ts...
		>::template ttype<Us...>;
	};
	
	template <template <typename...> class OP, size_t I, typename ...Ts, typename...Ss>
	struct tbind_impl<OP, std::tuple<Ss...>, _TP<I>, Ts...>
	{
		template<typename...Us>
		using ttype = typename tbind_impl<
		OP
		, typename std::tuple<
		Ss...
		, typename std::tuple_element<
		I
		, typename std::tuple<Us...>
		>::type
		>
		, Ts...
		>::template ttype<Us...>;
	};
}

template <template <typename...> class OP, typename...Ts>
struct tbind : _detail::tbind_impl<OP, std::tuple<>, Ts...>
{};

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
		using commuted = Deriving<R,L>;
		
		template<class Validator>
		constexpr Deriving<R,L> operator()(Validator) const {
			static_assert(CanValidate<Validator, L>::value && CanValidate<Validator, R>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return Deriving<R,L> {};
		}
		
		constexpr operator commuted() const {
			return commuted {};
		}
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
		template<class LL,class Validator>
		constexpr Deriving<LL,R> operator()(Deriving<LL,L>,Validator) const {
			static_assert(CanValidate<Validator, LL>::value && CanValidate<Validator, L>::value && CanValidate<Validator, R>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return Deriving<LL,R>{};
		}
		template<class RR,class Validator>
		constexpr Deriving<L,RR> operator()(Deriving<R,RR>,Validator) const {
			static_assert(CanValidate<Validator, L>::value && CanValidate<Validator, R>::value && CanValidate<Validator, RR>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return Deriving<L,RR>{};
		}
	protected:
		constexpr transitive() = default;
	};
	
	template<class Op>
	struct is_transitive { constexpr static const bool value = false; };
	
	template<class Deriving>
	struct is_transitive<transitive<Deriving>> { constexpr static const bool value = true; };
	
	enum Dir {
		Invariant,
		Decreasing,
		Increasing,
		Indeterminate
	};
	
	
	template<class Left, class Right>
	struct less_than_or_equal_to; // forward declaration
	template<class Left, class Right>
	struct equal_to; // forward declaration
	
	template<class Deriving, class EvaluatesTo>
	struct evaluates_to { protected: evaluates_to() = default; };
	
	template<template<class ...Arg> class Deriving, class ...Args>
	class function_of {
		template<class Candidate, class Current, class Replace>
		using ReplaceSame = std::conditional_t<std::is_same_v<Current, Candidate>, Replace, Candidate>;
		
		template<class Candidate, class Current, class Replace>
		using ReplaceBase = std::conditional_t<std::is_base_of_v<Current, Candidate>, Replace, Candidate>;
	public:
		template<class Validator, class Current, class Replace>
		constexpr Deriving<ReplaceSame<Args, Current, Replace> ...>  replace(equal_to<Current, Replace>, Validator) {
			return Deriving<ReplaceSame<Args, Current, Replace> ...>{};
		}
		
		template<class Func, class Result>
		constexpr Deriving<ReplaceBase<Args, evaluates_to<Func, Result>, Result> ...> replace(evaluates_to<Func, Result>) {
			return Deriving<ReplaceBase<Args, evaluates_to<Func, Result>, Result> ...>{};
		}
	};
	
	template<class Left, class Right>
	struct less_than
	: protected transitive<less_than<Left, Right>>
	, protected function_of<less_than, Left, Right> {
		/*
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value || is_evaluates_to<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value || is_evaluates_to<Right>::value)),
					  "Can only compare fresh variables, constants, and transparent functions");
		*/
		
		template<class OLeft, class ORight>
		friend class less_than;
		template<template<class ...Arg> class Deriving, class ...Args>
		friend class function_of;
	protected:
		using Self = less_than<Left, Right>;
		constexpr less_than() = default;
	public:
		using transitive<Self>::operator();
		using function_of<less_than, Left, Right>::replace;
		
		template<class Validator>
		constexpr static std::optional<Self> apply(const Left& left, const Right& right, Validator) {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			if(left.v < right.v) {
				return Self{};
			} else {
				return std::nullopt;
			}
		}
		
		template<class Left_, class Right_, std::enable_if_t<(std::is_same_v<Left_,Left> && std::is_same_v<Right_,Right> &&
															  is_constant<Left_>::value && is_constant<Right_>::value),bool> = true>
		constexpr less_than(Left_, Right_) { static_assert(Left{}.v < Right{}.v, "Definition of less_than");	}
		
		using compare_result = std::variant<less_than<Left,Right>,equal_to<Left,Right>,less_than<Right,Left>>;
		template<class Validator>
		constexpr static compare_result full_compare(const Left& left, const Right& right, Validator);
		
		template<class Validator>
		constexpr less_than_or_equal_to<Left, Right> operator()(Validator) const;
		
		// transitive properties again:
		template<class Validator, class RRight>
		constexpr less_than<Left, RRight> operator()(less_than_or_equal_to<Right, RRight>, Validator);
		
		template<class Validator, class LLeft>
		constexpr less_than<LLeft, Right> operator()(less_than_or_equal_to<LLeft, Right>, Validator);
	};
	
	template<class Deriving, class If, class Then>
	struct implies;
	
	template<class Left, class Right>
	struct equal_to
	: protected transitive<equal_to<Left, Right>>
	, protected commutative<equal_to<Left, Right>>
	, protected function_of<equal_to, Left, Right> {
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only compare fresh variables and constants");
		
		
		template<class Deriving, class If, class Then>
		friend struct implies;
		friend struct commutative<equal_to<Right, Left>>;
		template<template<class ...Arg> class Deriving, class ...Args>
		friend class function_of;
	protected:
		using Self = equal_to<Left, Right>;
		constexpr equal_to() = default;
	public:
		using transitive<Self>::operator();
		using commutative<Self>::operator();
		using commutative<Self>::operator equal_to<Right, Left>;
		using function_of<equal_to, Left, Right>::replace;
		
		template<class Validator>
		constexpr static std::optional<Self> apply(const Left& left, const Right& right, Validator) {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			if(left.v == right.v) {
				return Self{};
			} else {
				return std::nullopt;
			}
		}
		
		template<class _Right = Right, std::enable_if_t<std::is_same_v<_Right, Left> && std::is_same_v<_Right, Right>, bool> = true>
		constexpr equal_to(_Right) {}
	};
	
	
	template<class Deriving, class If, class Then>
	struct implies {
		constexpr Then operator()(If) const {
			return Then{};
		}
	protected:
		constexpr implies() = default;
	};
	
	template<typename Left, typename Right>
	class less_than_or_equal_to
	: protected transitive<less_than_or_equal_to<Left, Right>>
	, protected function_of<less_than_or_equal_to, Left, Right> {
		/*
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only compare fresh variables and constants");
		 */
		template<class Deriving, Dir ...dir> 
		friend class monotonic;
		template<template<class ...Arg> class Deriving, class ...Args>
		friend class function_of;
	protected:
		using Self = less_than_or_equal_to<Left, Right>;
		constexpr less_than_or_equal_to() = default;
	public:
		using transitive<Self>::operator();
		using function_of<less_than_or_equal_to, Left, Right>::replace;
		
		template<class Validator>
		constexpr static std::optional<Self> apply(const Left& left, const Right& right, Validator) {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			if(left.v <= right.v) {
				return Self{};
			} else {
				return std::nullopt;
			}
		}
		
		using strong = std::variant<less_than<Left, Right>, equal_to<Left, Right>>;
		
		template<class Validator>
		constexpr static Self apply(strong, Validator) {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return Self{};
		}
		
		template<class Validator, class _Left = Left, class _Right = Right,
		         std::enable_if_t<(is_constant<_Left>::value &&
								   std::is_integral_v<decltype(std::declval<_Left>().v)> &&
								   std::is_integral_v<decltype(std::declval<_Right>().v)>), bool> = true>
		constexpr static Self apply(less_than<Constant<_Left{}.v - 1>, Right>, Validator) {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return Self{};
		}
	};
	
	template<class Left, class Right>
	template<class Validator>
	constexpr less_than_or_equal_to<Left, Right> less_than<Left, Right>::operator()(Validator v) const {
		return less_than_or_equal_to<Left, Right>::apply(*this, v);
	}
	
	
	template<class Left, class Right>
	template<class Validator>
	constexpr auto less_than<Left,Right>::full_compare(const Left& left, const Right& right, Validator) -> compare_result {
		static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value,
					  "Validator must share root with terms and terms must not contain recursion");
		if(left.v < right.v) {
			return Self{};
		} else if(const auto eq_ev = equal_to<Left, Right>::apply(left, right, Validator{});
				  std::nullopt == eq_ev) {
			return *eq_ev;
		} else {
			return less_than<Right, Left>{};
		}
	}
	
	template<class Left, class Right>
	template<class Validator, class RRight>
	constexpr less_than<Left, RRight> less_than<Left,Right>::operator()(less_than_or_equal_to<Right, RRight>, Validator) {
		return {};
	}
	
	template<class Left, class Right>
	template<class Validator, class LLeft>
	constexpr less_than<LLeft, Right> less_than<Left,Right>::operator()(less_than_or_equal_to<LLeft, Right>, Validator) {
		return {};
	}
	
	namespace _detail {
		template<template<class ...As> class Deriving, class LCmp, class RCmp, Dir lCmpR, Dir result, class LeftHead, class RightHead, class LeftTail, class RightTail, Dir ...dirs>
		class monotonic_compare_impl {};

		template<template<class ...As> class Deriving, class LCmp, class RCmp, Dir lCmpR, Dir result, template<class ...As> class Buffer, class ...LeftHs, class ...RightHs,  class ...LeftTs, class ...RightTs, Dir ...dirs>
		class monotonic_compare_impl<Deriving, LCmp, RCmp, lCmpR, result, Buffer<LeftHs...>, Buffer<RightHs...>,  Buffer<LeftTs...>, Buffer<RightTs...>, dirs...> {
			static_assert(result != Indeterminate, "Unable to determine ordering");
			static_assert(result == Increasing || result == Decreasing || result == Invariant || result == Indeterminate,
						  "Incomplete case analysis");
		public:
			constexpr static const Dir value = result;
		private:
			
			template<class Left, class Right> using Swap = std::conditional_t<result == Invariant, equal_to<Left, Right>, std::conditional_t<result == Increasing, less_than_or_equal_to<Left, Right>, std::conditional_t<result == Decreasing, less_than_or_equal_to<Right, Left>, void>>>;
		public:
			using type = Swap<Deriving<LeftHs...>,Deriving<RightHs...>>;
		};
		
		template<template<class ...As> class Deriving, class LCmp,  class RCmp, Dir lCmpR, Dir result, template<class ...As> class Buffer, class ...LeftHs, class ...RightHs,  class LeftNow, class RightNow, class ...LeftTs, class ...RightTs, Dir dirNow, Dir ...dirs>
		class monotonic_compare_impl<Deriving, LCmp, RCmp, lCmpR, result, Buffer<LeftHs...>, Buffer<RightHs...>,  Buffer<LeftNow, LeftTs...>, Buffer<RightNow, RightTs...>, dirNow, dirs...> {
			static_assert(result != Indeterminate, "unable to determine ordering");
			static_assert(result == Increasing || result == Decreasing || result == Invariant || result == Indeterminate,
						  "Incomplete case analysis");
			
			constexpr static const bool identical = std::is_same_v<LeftNow, RightNow>;
			constexpr static const bool flipped = std::is_same_v<LeftNow, RCmp> && std::is_same_v<RightNow, LCmp>;
			static_assert(identical || (dirNow == Invariant) || (std::is_same_v<LeftNow, LCmp> && std::is_same_v<RightNow, RCmp>) || flipped,
						  "Mismatched arguments introduce unknown varying direction");
			
			constexpr static const Dir IncreaseDir = ((dirNow == Invariant)
													  ? Invariant
													  : ((dirNow == Increasing)
														 ? Increasing
														 : ((dirNow == Decreasing)
															? Decreasing
															: Indeterminate)));
			
			constexpr static const Dir DecreaseDir = ((dirNow == Invariant)
													  ? Invariant
													  : ((dirNow == Increasing)
														 ? Decreasing
														 : ((dirNow == Decreasing)
															? Increasing
															: Indeterminate)));
			
			constexpr static const Dir txResult = (identical
												   ? result
												   : (((result == Invariant || result == Increasing) && (lCmpR == Increasing))
													  ? (flipped ? DecreaseDir : IncreaseDir)
													  : (((result == Invariant || result == Decreasing) && (lCmpR == Decreasing))
														 ? (flipped ? IncreaseDir : DecreaseDir)
														 : ((result == Invariant && lCmpR == Invariant)
															? Invariant
															: Indeterminate))));
			
			using ResultThunk = monotonic_compare_impl<Deriving, LCmp, RCmp, lCmpR, txResult, Buffer<LeftHs...,LeftNow>,Buffer<RightHs...,RightNow>,Buffer<LeftTs...>,Buffer<RightTs...>,dirs...>;
		public:
			using type = typename ResultThunk::type;
			constexpr static const Dir value = result;
		};
	}
	
	template<class Deriving, Dir ...dir> struct monotonic {};
	
	template<template<class ...As> class Deriving, class ...Args, Dir ...dirs>
	struct monotonic<Deriving<Args...>, dirs...> {
		static_assert(sizeof...(Args) == sizeof...(dirs), "Must be one dir for each Arg");
		
		template<class LEq, class REq, class Validator, class ...OArgs, std::enable_if_t<(sizeof...(OArgs) == sizeof...(Args)), bool> = true>
		constexpr auto operator()(Deriving<OArgs...>, equal_to<LEq,REq>, Validator) const
		-> typename _detail::monotonic_compare_impl<Deriving, LEq, REq, Invariant, Invariant, std::tuple<>, std::tuple<>, std::tuple<Args...>, std::tuple<OArgs...>, dirs...>::type {
			static_assert(CanValidate<Validator, LEq>::value && CanValidate<Validator, REq>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return {};
		}
		template<class LT, class GT, class Validator, class ...OArgs, std::enable_if_t<(sizeof...(OArgs) == sizeof...(Args)), bool> = true>
		constexpr auto operator()(Deriving<OArgs...>, less_than_or_equal_to<LT,GT>, Validator) const
		-> typename _detail::monotonic_compare_impl<Deriving, LT, GT, Increasing, Invariant, std::tuple<>, std::tuple<>, std::tuple<Args...>, std::tuple<OArgs...>, dirs...>::type {
			static_assert(CanValidate<Validator, LT>::value && CanValidate<Validator, GT>::value,
						  "Validator must share root with terms and terms must not contain recursion");
			return {};
		}
	protected:
		constexpr monotonic() = default;
	};
	
	template<typename Val>
	using Positive = std::pair<Val, less_than<Zero, Val>>;
	template<typename Val>
	using Nonnegative = std::pair<Val, less_than_or_equal_to<Zero, Val>>;
	
	template<class ParentContext, class Left, class Right>
	struct NonnegativeAddition
	: monotonic<NonnegativeAddition<ParentContext, Left, Right>, Invariant, Increasing, Increasing> {
		static_assert(::detail::is_context_tag<ParentContext>::value, "Context must be context");
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only divide fresh variables and constants");
		
		using monotonic<NonnegativeAddition<ParentContext, Left, Right>, Invariant, Increasing, Increasing>::operator();
		
	private:
		FreshFrame();
		using UniqueContext = typename detail::PushContext<Context, UNIQUE>::type;
	public:
		Fresh<UniqueContext, decltype(std::declval<Left>().v + std::declval<Right>().v)> result;
		
		constexpr NonnegativeAddition(Context, Positive<Left> left, Positive<Right> right)
		: result{UniqueContext{}, left.first.v / right.first.v} {}
	};
	
	template<class ParentContext, class Left, class Right>
	struct PosDivPredef {
		using Context = typename detail::PushContext<ParentContext, UNIQUE>::type;
		using UniqueContext = typename detail::PushContext<Context, UNIQUE>::type;
		using Result = Fresh<UniqueContext, decltype(std::declval<Left>().v / std::declval<Right>().v)>;
	};
	
	template<class ParentContext, class Left, class Right>
	struct PositiveDivision
	: PosDivPredef<ParentContext, Left, Right>
	, monotonic<PositiveDivision<ParentContext, Left, Right>, Invariant, Increasing, Decreasing>
	, implies<PositiveDivision<ParentContext, Left, Right>, equal_to<Left, Zero>, equal_to<typename PosDivPredef<ParentContext, Left, Right>::Result, Zero>>
	, implies<PositiveDivision<ParentContext, Left, Right>, equal_to<Right, One>, equal_to<typename PosDivPredef<ParentContext, Left, Right>::Result, Left>>
	, implies<PositiveDivision<ParentContext, Left, Right>, equal_to<Left, Right>, equal_to<typename PosDivPredef<ParentContext, Left, Right>::Result, One>>
	, evaluates_to<PositiveDivision<ParentContext, Left, Right>, typename PosDivPredef<ParentContext, Left, Right>::Result> {
	private:
		using Predef = PosDivPredef<ParentContext, Left, Right>;
		using typename Predef::Context;
		using typename Predef::UniqueContext;
	public:
		using typename Predef::Result;
	
		static_assert(detail::is_context_tag<ParentContext>::value, "Context must be context");
		static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
					   (is_constant<Right>::value || is_fresh<Right>::value)),
					  "Can only divide fresh variables and constants");
		using Self = PositiveDivision<ParentContext, Left, Right>;
		using monotonic<PositiveDivision<ParentContext, Left, Right>, Invariant, Increasing, Decreasing>::operator();
		using implies<Self, equal_to<Left, Zero>, equal_to<Result, Zero>>::operator();
		using implies<Self, equal_to<Right, One>, equal_to<Result, Left>>::operator();
		using implies<Self, equal_to<Left, Right>, equal_to<Result, One>>::operator();
		
		constexpr PositiveDivision() {
			static_assert(CanValidate<Context, typename Nonnegative<Left>::first_type>::value &&
						  CanValidate<Context, typename Positive<Right>::first_type>::value,
						  "Validator must share root with terms and terms must not contain recursion");
		}
		
		constexpr Result operator()(Nonnegative<Left> left, Positive<Right> right) const {
			return {UniqueContext{}, left.first.v / right.first.v};
		}
		
		template<class Validator>
		constexpr less_than<Result, Left> operator()(less_than<One, Right>, Validator) const {
			return {};
		}
		
		template<class Validator>
		constexpr less_than<Zero, Result> operator()(typename less_than_or_equal_to<Right, Left>::strong lte_ev, Validator) const {
			static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value && CanValidate<Validator, Result>::value,
						  "Left, Right, and Result must share a root with Validator, and can't contain recursion");
			switch(lte_ev.index()) {
				case 0: {
					if constexpr (!std::is_same_v<Left, Right>) {
						less_than<Right, Left> lt_ev = std::get<0>(lte_ev);
						using SneakyOne = PositiveDivision<Context, Left, Left>;
						using S1R = typename SneakyOne::Result;
						less_than_or_equal_to<SneakyOne, Self> lb1 = (*this)(SneakyOne{}, lt_ev(Validator{}), Validator{});
						less_than_or_equal_to<S1R, Result> lb1_ = lb1.replace(SneakyOne{}).replace(Self{});
						equal_to<S1R, One> s1i = SneakyOne{}(equal_to<Left,Left>(Left{}));
						less_than_or_equal_to<One, Result> lb1__ = lb1_.replace(s1i, Validator{});
						less_than<Zero, One> onePos{Zero{}, One{}};
						
						return less_than<Zero, One>(Zero{}, One{})(lb1__, Validator{});
					} else {
						// Silly compiler
						[[fallthrough]];
					}
				}
				case 1: {
					equal_to<Right, Left> eq_ev = std::get<1>(lte_ev);
					equal_to<One, Result>  one_ev = (*this)(eq_ev);
					return less_than<Zero, One>(Zero{},One{}).replace(one_ev, Validator{});
				}
			}
		}
	};
}

template<class ParentContext, class VarContext>
auto inc(Fresh<VarContext, int> var) {
	FreshFrame();
	return FreshType(var.v + 1);
}

auto bad() {
	RootFrame();
	return FreshType(2);
}

template<class OldVar, class NewVar>
class SubsetVariant {};

template<class ...OldVars, class ...NewVars>
class SubsetVariant<std::variant<OldVars...>,std::variant<NewVars...>> {
	template<class Head, class ...Tail>
	inline std::variant<OldVars...> applyHelper(std::variant<NewVars...> input) {
		if(std::holds_alternative<Head>(input)) {
			return std::get<Head>(input);
		} else {
			return applyHelper<Tail...>(input);
		}
	}
	
	template<class ...N>
	inline std::variant<OldVars...> applyHelper(std::variant<NewVars...> ) {
		if constexpr (sizeof...(N) > 0) {
			throw std::invalid_argument("");
		} else {
			return std::variant<OldVars...>();
		}
	}
public:
	
	constexpr static std::variant<OldVars...> apply(std::variant<NewVars...> input) {
		
	};
};

template<class ParentContext, class ReturnContext, class VarContext>
/*struct Log2 {
	static_assert(detail::is_context_tag<ParentContext>::value, "ParentContext must be context");
	static_assert(is_constant<Arg>::value || is_fresh<Arg>::value,
				  "Can only log fresh variables and constants");
private:
	using Context = typename detail::PushContext<ParentContext, UNIQUE>::type;
	
};*/
constexpr Fresh<ReturnContext, int> log2(Return<ReturnContext, int> rGen,
										 Fresh<VarContext, int> var,
										 algebra::less_than<Zero, decltype(var)> gt0) {
	using namespace algebra;
	FreshFrame();
	if(auto compareEv = less_than<Two,decltype(var)>::full_compare(Two{}, var, Context{});
	   std::holds_alternative<less_than<decltype(var),Two>>(compareEv)) {
		// 0 < var < 2 -> var == 1
		return std::move(rGen)(0);
	} else {
		using TwoIsPositive = less_than<Zero,Two>;
		constexpr TwoIsPositive twP(Zero{}, Two{});
		
		using Divide = PositiveDivision<Context, decltype(var), Two>;
		/****************************************
		 * Given: 0 < var; 0 < 2; 1 < var
		 * r = var / 2; (2 <= var) -> (r > 0)
		 ****************************************/
		Nonnegative<decltype(var)> numerator{var, gt0(Context{})};
		Positive<Two> denominator{ Two{}, twP };
		using strong_gte2 = typename less_than_or_equal_to<Two, decltype(var)>::strong;
		auto gte2 = SubsetVariant<strong_gte2, decltype(compareEv)>::apply(compareEv);
		
		Divide nextArg;
		auto newGT0 = nextArg(gte2, Context{});
		auto nextReturn = log2<Context>(MakeReturn(int), nextArg(numerator, denominator), newGT0);
		return std::move(rGen)(1 + nextReturn.v);
	}
}

int main(int argc, const char* argv[]) {
	RootFrame();
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
	if(auto proofPositive = algebra::less_than<Zero,decltype(v32)>::apply(Zero{}, v32, Context{});
	   std::nullopt == proofPositive) {
		auto logOf32 = log2<Context>(MakeReturn(int),v32,*proofPositive);
		std::cout << "log_2(" << v32 << ") = " << logOf32 << std::endl;
	} else {
		std::cerr << "Can't take log of negative number" << std::endl;
	}
	return 0;
}
