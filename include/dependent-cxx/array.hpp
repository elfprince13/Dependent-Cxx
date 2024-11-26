#pragma once

#include <memory>
#include <tuple>
#include <type_traits>

#include <dependent-cxx/core.hpp>
#include <dependent-cxx/algebra.hpp>

namespace dependent_cxx {
    namespace collections {
        template<class Context, class Elem, class Length>
        class Array {
            static_assert(is_fresh<Length>::value || is_constant<Length>::value,
                        "Length must be fresh, or constant");
            std::unique_ptr<Elem[]> data_;
            algebra::Nonnegative<Length> length_;
            
        public:
            
            /*
            template<class Dummy=bool>
            Array()
            {
                static_assert(is_constant<Length>::value,
                            "Can only default initialize a constant-length array");
                
                
            }
            */
            
            template<class Idx>
            using LowerBound = algebra::less_than_or_equal_to<Zero, Idx>;
            template<class Idx>
            using UpperBound = algebra::less_than<Idx, Length>;
            
            template<class Idx>
            using Bounded = std::tuple<Idx, LowerBound<Idx>, UpperBound<Idx>>;
            
            Array(Length len, LowerBound<Length> ev)
            : data_(new Elem[len.v])
            , length_{len, ev} {
                static_assert(CanValidate<Context, Length>::value,
                            "Validator must share root with terms and terms must not contain recursion");
            }
            
            algebra::Nonnegative<Length> length() const {
                return length_;
            }
            
            size_t size() const {
                return length_.first.v;
            }
            
            template<class Idx, std::enable_if_t<is_fresh<Length>::value || is_constant<Length>::value, bool> = true>
            Elem& operator[](const Bounded<Idx>& idx) {
                return data_[std::get<0>(idx).v];
            }
            
            template<class Idx, std::enable_if_t<is_fresh<Length>::value || is_constant<Length>::value, bool> = true>
            const Elem& operator[](const Bounded<Idx>& idx) const {
                return data_[std::get<0>(idx).v];
            }
            
            auto begin() const {
                return data_.get();
            }
            
            auto end() const {
                return begin() + size();
            }
            
            auto begin() {
                return data_.get();
            }
            
            auto end() {
                return begin() + size();
            }
        };
        
        template<class Context, class Elem,
                class ContextL, class LengthL,
                class ContextR, class LengthR, class Sum = algebra::NonnegativeAddition<FreshTag(), LengthL, LengthR>>
        auto concatenate(const Array<ContextL, Elem, LengthL>& left, const Array<ContextR, Elem, LengthR>& right)
        -> std::pair<Array<FreshTag(), Elem, typename Sum::Result>, algebra::equal_to<Sum, typename Sum::Result>>
        {
            auto [lLen, l_nn_ev] = left.length();
            auto [rLen, r_nn_ev] = right.length();
            Sum sum{l_nn_ev, r_nn_ev};
            typename Sum::Result nLen = sum(left.length(), right.length());
            
            constexpr algebra::less_than_or_equal_to<Zero, Zero> z_nn_ev{Zero{}, Zero{}};
            using SneakyZero = algebra::NonnegativeAddition<FreshTag(), Zero, Zero>;
            constexpr SneakyZero sneakyZero{z_nn_ev, z_nn_ev};
            auto n_nn_ev = sum(sneakyZero, l_nn_ev, Context{});
            
            
            //algebra::less_than_or_equal_to<Zero, >
            // TODO: finish me!
        }
    }
}