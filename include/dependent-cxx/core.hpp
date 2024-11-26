#pragma once

#include <tuple>
#include <type_traits>

namespace dependent_cxx {

    namespace detail {
        template<size_t ...Nums>
        struct Unique {};
    }

#define TYPEOF(X) std::decay_t<decltype(X)>

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

    template<class Tag, class V> struct Fresh : Tag {
        const V v;
    };

    template<class Tag, class V> Fresh(Tag, V) -> Fresh<Tag, V>;

    template<class C>
    struct is_fresh { constexpr static const bool value = false; };
    template<class Tag, class V>
    struct is_fresh<Fresh<Tag,V>> { constexpr static const bool value = true; };

    template<auto V> struct Constant {
        const TYPEOF(V) v;
        constexpr Constant() : v(V) {}
    };

    template<class C>
    struct is_constant { constexpr static const bool value = false; };
    template<auto V>
    struct is_constant<Constant<V>> { constexpr static const bool value = true; };

    using Zero = Constant<0>;
    using One = Constant<1>;
    using Two = Constant<2>;

    template<class Validator, class Term>
    class CanValidate {
        static_assert(detail::is_context_tag<std::decay_t<Validator>>::value, "Validator must be a context tag");
        static_assert(is_fresh<std::decay_t<Term>>::value || is_constant<std::decay_t<Term>>::value, "Term must be a context tag");
    public:
        constexpr static const bool value = CanValidate<std::decay_t<Validator>, std::decay_t<Term>>::value;
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
        static_assert(SameRoot, "Cannot compare contexts which do not share a root and/or which are being "
                                "inspected outside their root context. "
                                "Consider calling RefreshType on Left and Right within the CompareContext");
        static_assert(!AnyRecursion || !SameComps, "Left and Right tags are equivalent but contain recursive fixed points "
                                                   "and thus cannot be guaranteed unique. "
                                                   "Consider re-rooting in a fresh context");
    };

    namespace detail { 
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
            using type = std::conditional_t<AnyRecursion,
                                            std::conditional_t<KnownRecursion,
                                                            typename CutFixedPoint<std::tuple<Root,Tail...>,std::tuple<>,P>::type,
                                                            ContextTag<Root, Tail..., fixed_point<P>>>,
                                            ContextTag<Root, Tail..., P>>;
        };
    }
template<class ContextTag, class Push>
constexpr auto pushContext(ContextTag, Push) {
	return typename detail::PushContext<ContextTag, Push> ::type{};
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
#define FreshTag() typename detail::PushContext<Context, UNIQUE>::type
#define FreshFrame() using Context = typename detail::PushContext<ParentContext, UNIQUE>::type

#define RefreshType(X) Fresh{pushContext(Context{},UNIQUE{}), X.v}

template<typename UniqueContext, typename V>
class Return {
	template<typename V_, typename ParentContext>
	friend constexpr auto makeReturn(ParentContext);
	Return() = default;
public:
	constexpr Fresh<UniqueContext, V> operator()(V v) && {
		return Fresh{UniqueContext{}, v};
	}
};

template<typename V_, typename ParentContext>
constexpr auto makeReturn(ParentContext) {
	FreshFrame();
	return Return<Context, V_>{};
}

#define MakeReturn(V) makeReturn<V>(pushContext(Context{},UNIQUE{}))

} //namespace dependent_cxx