// WIP: proof that a variant is one of a only a subset of possible values
/*
template<class OldVar, class NewVar>
class SubsetVariant {};

template<class OldVarH, class ...OldVarTs, class ...NewVars>
class SubsetVariant<std::variant<OldVarH, OldVarTs...>,std::variant<NewVars...>> {
	template<class Head, class ...Tail>
	inline static std::variant<OldVarH, OldVarTs...> applyHelper(std::variant<NewVars...> input) {
		if(std::holds_alternative<Head>(input)) {
			return std::get<Head>(input);
		} else {
			return applyHelper<Tail...>(input);
		}
	}
	
	template<class ...N, std::enable_if_t<sizeof...(N) == 0, bool> = true>
	inline static std::variant<OldVarH, OldVarTs...> applyHelper(std::variant<NewVars...> ) {
		static_assert(sizeof...(N) == 0);
		return std::variant<OldVarH, OldVarTs...>(([]() -> OldVarH { throw std::logic_error("These don't overlap"); })());
	}
public:
	
	constexpr static std::variant<OldVarH, OldVarTs...> apply(std::variant<NewVars...> input) {
		return applyHelper<OldVarH, OldVarTs...>(input);
	};
};
 */