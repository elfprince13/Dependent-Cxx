#include <dependent-cxx/core.hpp>
#include <dependent-cxx/core-io.hpp>

using namespace dependent_cxx;

template<class ParentContext, class VarContext>
auto inc(Fresh<VarContext, int> var) {
	FreshFrame();
	return FreshType(var.v + 1);
}

auto bad() {
	RootFrame();
	return FreshType(2);
}

// demo of the very low-level functionality for comparing types
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
	// This *should* fail to compile if you uncomment it
	//std::cout << DEPEND_EQUIV(bad(), bad()) << std::endl;
	std::cout << DEPEND_EQUIV(RefreshType(bad()), RefreshType(bad())) << std::endl;

	return 0;
}
