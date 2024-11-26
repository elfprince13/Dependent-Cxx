#include <dependent-cxx/algebra.hpp>
#include <dependent-cxx/core-io.hpp>

using namespace dependent_cxx;

template<class ParentContext, class ReturnContext, class VarContext>
constexpr Fresh<ReturnContext, int> log2(Return<ReturnContext, int> rGen,
										 Fresh<VarContext, int> var,
										 algebra::less_than<Zero, TYPEOF(var)> gt0) {
	using namespace algebra;
	FreshFrame();
	return std::visit([rGen=std::move(rGen),var=var,gt0=gt0](auto compareEv) mutable constexpr -> Fresh<ReturnContext, int> {
		if constexpr(std::is_same_v<TYPEOF(compareEv), less_than<TYPEOF(var),Two>>) {
			// 0 < var < 2 -> var == 1
			return std::move(rGen)(0);
		} else {
			using TwoIsPositive = less_than<Zero,Two>;
			constexpr TwoIsPositive twP(Zero{}, Two{});
			
			using Divide = PositiveDivision<FreshTag(), TYPEOF(var), Two>;
			/****************************************
			 * Given: 0 < var; 0 < 2; 1 < var
			 * r = var / 2; (2 <= var) -> (r > 0)
			 ****************************************/
			const Nonnegative<TYPEOF(var)> numerator{var, gt0(Context{})};
			constexpr Positive<Two> denominator{ Two{}, twP };
			using strong_gte2 = typename less_than_or_equal_to<Two, TYPEOF(var)>::strong;
			constexpr strong_gte2 gte2{compareEv};
			
			Divide nextArg(numerator.second, denominator.second);
			const auto newVar = nextArg(numerator, denominator);
			constexpr auto newGT0 = nextArg(gt0(Context{}), twP, gte2, Context{});
			
			using OldContext = Context;
			{
				RootFrame();
				const auto freshVar = RefreshType(newVar);
				constexpr inductive_shift<TYPEOF(newVar), TYPEOF(freshVar)> shift_ev{TYPEOF(newVar){}, TYPEOF(freshVar){}};
				
				auto nextReturn = log2<Context>(MakeReturn(int), freshVar, newGT0.replace(shift_ev, OldContext{}, Context{}));
				return std::move(rGen)(1 + nextReturn.v);
			}
		}
	}, less_than<Two,TYPEOF(var)>::full_compare(Two{}, var, Context{}));
}

// Demo that 0 <= log2(n) < n for all positive n
int main(int argc, const char* argv[]) {
	RootFrame();
	constexpr auto v32 = FreshType(32);
	if constexpr (constexpr auto proofPositive = algebra::less_than<Zero,TYPEOF(v32)>::apply(Zero{}, v32, Context{});
				  std::nullopt == proofPositive) {
		std::cerr << "Can't take log of negative number" << std::endl;
	} else {
		constexpr algebra::less_than<Zero,TYPEOF(v32)> lt_ev{*proofPositive};
		constexpr auto logOf32 = log2<Context>(MakeReturn(int), v32, lt_ev);
		std::cout << "log_2(" << v32 << ") = " << logOf32 << std::endl;
		constexpr algebra::less_than_or_equal_to<Zero, TYPEOF(v32)> lte_ev{lt_ev(Context{})};
    }

    return 0;
}