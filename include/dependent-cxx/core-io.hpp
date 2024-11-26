#pragma once

#include <dependent-cxx/core.hpp>

#include <iostream>

namespace dependent_cxx {
    namespace detail {
        template <size_t... Nums>
        std::ostream &operator<<(std::ostream &out, Unique<Nums...>) {
            out << "Unique<";
            (..., (out << Nums << ","));
            return out << ">";
        }
        
        template<class CT>
        std::ostream& operator<<(std::ostream& out, fixed_point<CT>) {
            return out << "fixed_point{" << CT{} << "}";
        }
    }

    template<class Root, class ...Trail>
    std::ostream& operator<<(std::ostream& out, ContextTag<Root, Trail...>) {
        out << "Context<" << Root{};
        (... , (out << ", " << Trail{}));
        return out << ">";
    }

    template<class Tag, class V>
    std::ostream& operator<<(std::ostream& out, const Fresh<Tag, V>& fresh) {
        return out << "Fresh{" << (Tag)fresh << ", " << fresh.v << "}";
    }

    template<auto V>
    std::ostream& operator<<(std::ostream& out, const Constant<V>) {
        return out << "Constant{" << V << "}";
    }
}