#pragma once

#include <optional>
#include <tuple>
#include <type_traits>

#include <dependent-cxx/core.hpp>

namespace dependent_cxx {
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
        class less_than_or_equal_to; // forward declaration
        template<class Left, class Right>
        struct equal_to; // forward declaration
        template<class VarN, class VarNp1>
        struct inductive_shift; // forward declaration
        
        template<class Deriving, class EvaluatesTo>
        struct evaluates_to { protected: evaluates_to() = default; };
        
        template<template<class ...Arg> class Deriving, class ...Args>
        class function_of {
            template<class Candidate, class Current, class Replace>
            using ReplaceSame = std::conditional_t<std::is_same_v<Current, Candidate>, Replace, Candidate>;
            
            template<class Candidate, class Current, class Replace>
            using ReplaceBase = std::conditional_t<std::is_base_of_v<Current, Candidate>, Replace, Candidate>;
        public:
            template<class Current, class Replace, class Validator>
            constexpr Deriving<ReplaceSame<Args, Current, Replace> ...>  replace(equal_to<Current, Replace>, Validator) const {
                static_assert(CanValidate<Validator, Current>::value && CanValidate<Validator, Replace>::value,
                            "Validator must share root with terms and terms must not contain recursion");
                return {};
            }
            
            template<class Func, class Result, class Validator>
            constexpr Deriving<ReplaceBase<Args, evaluates_to<Func, Result>, Result> ...> replace(evaluates_to<Func, Result>, Validator) const {
                // Todo: need to add validation here, but haven't figured out what that looks like for functions
                return {};
            }
            
            template<class VarN, class VarNp1, class ValN, class ValNp1, bool backward = false>
            constexpr Deriving<ReplaceSame<Args, std::conditional_t<backward, VarNp1, VarN>, std::conditional_t<backward, VarN, VarNp1>>...> replace(const inductive_shift<VarN, VarNp1>&, ValN, ValNp1) const {
                static_assert(CanValidate<ValN,VarN>::value && CanValidate<ValNp1, VarNp1>::value,
                            "Validators must share root with terms and terms must not contain recursion");
                return {};
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
            friend struct less_than;
            template<template<class ...Arg> class Deriving, class ...Args>
            friend class function_of;
            template<class Deriving>
            friend struct transitive;
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
            constexpr less_than<Left, RRight> operator()(less_than_or_equal_to<Right, RRight>, Validator) const;
            
            template<class Validator, class LLeft>
            constexpr less_than<LLeft, Right> operator()(less_than_or_equal_to<LLeft, Right>, Validator) const;
        };
        
        template<class Deriving, class If, class Then>
        struct implies;
        
        template<class Left, class Right>
        struct equal_to
        : protected transitive<equal_to<Left, Right>>
        , protected commutative<equal_to<Left, Right>>
        , protected function_of<equal_to, Left, Right> {
            /*
            static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
                        (is_constant<Right>::value || is_fresh<Right>::value)),
                        "Can only compare fresh variables and constants");
            */
            
            template<class Deriving, class If, class Then>
            friend struct implies;
            friend struct commutative<equal_to<Right, Left>>;
            template<class Deriving, Dir ...dir>
            friend class monotonic;
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
            
            template<class Validator>
            constexpr less_than_or_equal_to<Left, Right> operator()(Validator) const;
        };
        
        
        
        template<class VarN, class VarNp1>
        struct inductive_shift : private equal_to<VarN, VarNp1> {
            inductive_shift(const inductive_shift<VarN, VarNp1>&) = delete;
            inductive_shift(inductive_shift<VarN, VarNp1>&&) = delete;
            inductive_shift& operator=(const inductive_shift<VarN, VarNp1>&) = delete;
            inductive_shift& operator=(inductive_shift<VarN, VarNp1>&&) = delete;
            
            constexpr inductive_shift(VarN, VarNp1) {}
        protected:
            constexpr inductive_shift() = default;
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
            
            
            
            template<class Left_, class Right_, std::enable_if_t<(std::is_same_v<Left_,Left> && std::is_same_v<Right_,Right> &&
                                                                is_constant<Left_>::value && is_constant<Right_>::value),bool> = true>
            constexpr less_than_or_equal_to(Left_, Right_) { static_assert(Left{}.v <= Right{}.v, "Definition of less_than_or_equal_to");	}
            
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
                                    std::is_integral_v<TYPEOF(std::declval<_Left>().v)> &&
                                    std::is_integral_v<TYPEOF(std::declval<_Right>().v)>), bool> = true>
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
        constexpr less_than_or_equal_to<Left, Right> equal_to<Left, Right>::operator()(Validator v) const {
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
                return less_than<Right, Left>{};
            } else {
                return *eq_ev;
            }
        }
        
        template<class Left, class Right>
        template<class Validator, class RRight>
        constexpr less_than<Left, RRight> less_than<Left,Right>::operator()(less_than_or_equal_to<Right, RRight>, Validator) const {
            return {};
        }
        
        template<class Left, class Right>
        template<class Validator, class LLeft>
        constexpr less_than<LLeft, Right> less_than<Left,Right>::operator()(less_than_or_equal_to<LLeft, Right>, Validator) const {
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
        
        template<class _Context, class Left, class Right>
        struct NNAddPredef {
            using Context = _Context;
            using UniqueContext = FreshTag();
            using Result = Fresh<UniqueContext, TYPEOF(std::declval<Left>().v + std::declval<Right>().v)>;
        };
        
        template<class _Context, class Left, class Right>
        struct NonnegativeAddition
        : NNAddPredef<_Context, Left, Right>
        //, commutative<typename tbind<NonnegativeAddition, _Context, _TP<0>, _TP<1>>::template ttype<Left, Right>>
        , monotonic<NonnegativeAddition<_Context, Left, Right>, Invariant, Increasing, Increasing>
        , evaluates_to<NonnegativeAddition<_Context, Left, Right>, typename NNAddPredef<_Context, Left, Right>::Result>
        , implies<NonnegativeAddition<_Context, Left, Right>, equal_to<Left, Zero>, equal_to<typename NNAddPredef<_Context, Left, Right>::Result, Right>>
        /*, implies<NonnegativeAddition<_Context, Left, Right>, equal_to<Right, Zero>, equal_to<typename NNAddPredef<_Context, Left, Right>::Result, Left>>*/ {
            using Predef = NNAddPredef<_Context, Left, Right>;
            using typename Predef::Context;
            using typename Predef::UniqueContext;
        public:
            using typename Predef::Result;
            
            static_assert(dependent_cxx::detail::is_context_tag<Context>::value, "Context must be context");
            static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
                        (is_constant<Right>::value || is_fresh<Right>::value)),
                        "Can only divide fresh variables and constants");
            
            using monotonic<NonnegativeAddition<Context, Left, Right>, Invariant, Increasing, Increasing>::operator();
            //using commutative<typename tbind<NonnegativeAddition, _Context, _TP<0>, _TP<1>>::template ttype<Left, Right>>::operator();
            
            using implies<NonnegativeAddition<_Context, Left, Right>, equal_to<Left, Zero>, equal_to<typename NNAddPredef<_Context, Left, Right>::Result, Right>>::operator();
            //using implies<NonnegativeAddition<_Context, Left, Right>, equal_to<Right, Zero>, equal_to<typename NNAddPredef<_Context, Left, Right>::Result, Left>>::operator();
        public:
            constexpr NonnegativeAddition(less_than_or_equal_to<Zero, Left>, less_than_or_equal_to<Zero, Right>) {
                static_assert(CanValidate<Context, Left>::value &&
                            CanValidate<Context, Right>::value,
                            "Validator must share root with terms and terms must not contain recursion");
            }
            
            constexpr Result operator()(Nonnegative<Left> left, Nonnegative<Right> right) const {
                return {UniqueContext{}, left.first.v + right.first.v};
            }
        };
        
        template<class _Context, class Left, class Right>
        struct PosDivPredef {
            using Context = _Context;
            using UniqueContext = FreshTag();
            using Result = Fresh<UniqueContext, TYPEOF(std::declval<Left>().v / std::declval<Right>().v)>;
        };
        
        template<class _Context, class Left, class Right>
        struct PositiveDivision
        : PosDivPredef<_Context, Left, Right>
        , monotonic<PositiveDivision<_Context, Left, Right>, Invariant, Increasing, Decreasing>
        , implies<PositiveDivision<_Context, Left, Right>, equal_to<Left, Zero>, equal_to<typename PosDivPredef<_Context, Left, Right>::Result, Zero>>
        , implies<PositiveDivision<_Context, Left, Right>, equal_to<Right, One>, equal_to<typename PosDivPredef<_Context, Left, Right>::Result, Left>>
        , implies<PositiveDivision<_Context, Left, Right>, equal_to<Left, Right>, equal_to<typename PosDivPredef<_Context, Left, Right>::Result, One>>
        , evaluates_to<PositiveDivision<_Context, Left, Right>, typename PosDivPredef<_Context, Left, Right>::Result> {
        private:
            using Predef = PosDivPredef<_Context, Left, Right>;
            using typename Predef::Context;
            using typename Predef::UniqueContext;
        public:
            using typename Predef::Result;
        
            static_assert(detail::is_context_tag<Context>::value, "Context must be context");
            static_assert(((is_constant<Left>::value || is_fresh<Left>::value) &&
                        (is_constant<Right>::value || is_fresh<Right>::value)),
                        "Can only divide fresh variables and constants");
            using Self = PositiveDivision<Context, Left, Right>;
            using monotonic<PositiveDivision<Context, Left, Right>, Invariant, Increasing, Decreasing>::operator();
            using implies<Self, equal_to<Left, Zero>, equal_to<Result, Zero>>::operator();
            using implies<Self, equal_to<Right, One>, equal_to<Result, Left>>::operator();
            using implies<Self, equal_to<Left, Right>, equal_to<Result, One>>::operator();
            
            constexpr PositiveDivision(less_than_or_equal_to<Zero, Left>, less_than<Zero, Right>) {
                static_assert(CanValidate<Context, Left>::value &&
                            CanValidate<Context, Right>::value,
                            "Validator must share root with terms and terms must not contain recursion");
            }
            
            constexpr Result operator()(Nonnegative<Left> left, Positive<Right> right) const {
                return {UniqueContext{}, left.first.v / right.first.v};
            }
            /*
            // monotonicity exercise for later
            template<class Validator>
            constexpr less_than<Result, Left> operator()(less_than<One, Right>, Validator) const {
                return {};
            }
            */
            template<class Validator>
            constexpr less_than<Zero, Result> operator()(less_than_or_equal_to<Zero, Left> l_nn_ev, less_than<Zero, Right> r_pos_ev, typename less_than_or_equal_to<Right, Left>::strong lte_ev, Validator) const {
                static_assert(CanValidate<Validator, Left>::value && CanValidate<Validator, Right>::value && CanValidate<Validator, Result>::value,
                            "Left, Right, and Result must share a root with Validator, and can't contain recursion");
                return std::visit([=](auto ev) constexpr -> less_than<Zero, Result> {
                    constexpr const bool trueEqual = std::is_same_v<equal_to<Right, Left>, TYPEOF(ev)>;
                    constexpr const bool dumbCompilerEqual = std::is_same_v<Right, Left>;
                    if constexpr (trueEqual || dumbCompilerEqual) {
                        // These are the same. Need the extra check for exhaustiveness because the compiler doesn't know our axioms
                        equal_to<Right, Left> eq_ev = ([](auto ev) -> equal_to<Right, Left>{
                            if constexpr (trueEqual) { return ev; }
                            else if constexpr (dumbCompilerEqual){ return equal_to<Right, Left>{Left{}}; }
                        })(ev);
                                        
                        equal_to<One, Result>  one_ev = (*this)(eq_ev);
                        return less_than<Zero, One>(Zero{},One{}).replace(one_ev, Validator{});
                    } else {
                        // lt ev
                        constexpr less_than<Right, Left> lt_ev = ev;
                        // left pos ev
                        less_than<Zero, Left> l_pos_ev = r_pos_ev(lt_ev, Validator{});
                        using SneakyOne = PositiveDivision<FreshTag(), Left, Left>;
                        constexpr SneakyOne sneakyOne{l_nn_ev, l_pos_ev};
                        using S1R = typename SneakyOne::Result;
                        auto lte_ev = (*this)(sneakyOne, lt_ev(Validator{}), Validator{});
                        less_than_or_equal_to<SneakyOne, Self> lb1 = ([=](auto lte_ev) constexpr -> less_than_or_equal_to<SneakyOne, Self> {
                            if constexpr (std::is_same_v<TYPEOF(lte_ev), less_than_or_equal_to<SneakyOne, Self>>) {
                                return lte_ev;
                            } else /*if constexpr (std::is_same_v<TYPEOF(lte_ev), equal_to<SneakyOne, Self>>)*/ {
                                return lte_ev(Validator{});
                            }
                        })(lte_ev);
                        less_than_or_equal_to<S1R, Result> lb1_ = lb1.replace(sneakyOne, Validator{}).replace(*this, Validator{});
                        equal_to<S1R, One> s1i = sneakyOne(equal_to<Left,Left>(Left{})/*, Validator{}*/); // haven't figured out function validation yes
                        less_than_or_equal_to<One, Result> lb1__ = lb1_.replace(s1i, Validator{});
                        return less_than<Zero, One>(Zero{}, One{})(lb1__, Validator{});
                    }
                }, lte_ev);
            }
        };
    }
}