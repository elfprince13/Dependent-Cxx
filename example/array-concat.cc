#include <dependent-cxx/algebra.hpp>
#include <dependent-cxx/array.hpp>
#include <dependent-cxx/core-io.hpp>

using namespace dependent_cxx;

// WIP demo of concatenating a dynamic length array with a static length array
int main(int argc, const char* argv[]) {
	RootFrame();
	constexpr auto v32 = FreshType(32);
	if constexpr (constexpr auto proofNonneg = algebra::less_than_or_equal_to<Zero,TYPEOF(v32)>::apply(Zero{}, v32, Context{});
				  std::nullopt == proofNonneg) {
		std::cerr << "Can't make negative-length array" << std::endl;
	} else {
		constexpr algebra::less_than_or_equal_to<Zero, TYPEOF(v32)> lte_ev = *proofNonneg;
		collections::Array<FreshTag(), float, TYPEOF(v32)> a32(v32, lte_ev);
		
		constexpr Constant<64> SixtyFour;
		constexpr algebra::less_than_or_equal_to<Zero, TYPEOF(SixtyFour)> sixty_four_nn{Zero{}, SixtyFour};
		collections::Array<FreshTag(), float, TYPEOF(SixtyFour)> a64(SixtyFour, sixty_four_nn);
		
		//auto a96{collections::concatenate<FreshTag()>(a64, a32)};
        // TODO: finish implementing concatenate
		
	}

	return 0;
}