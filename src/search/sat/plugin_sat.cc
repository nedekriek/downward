#include "sat_search.h"
#include "../plugins/plugin.h"

using namespace std;

namespace plugin_sat {
class SATSearchFeature : public plugins::TypedFeature<SearchAlgorithm, sat_search::SATSearch> {
public:
    SATSearchFeature() : TypedFeature("sat") {
        document_title("SAT search");
        document_synopsis("");
		
		add_option<int>(
            "plan_length",
            "run the search for a single plan length only. -1 if length should not be fixed.",
            "-1");
		add_option<int>(
            "encoding",
            "set the encoding. Currently supported are OneStep: 0 and ExistsStep: 2",
            "2");
		add_option<int>(
            "length_iteration",
            "run the search for a single plan length only. -1 if length should not be fixed. This options run's Rintanen's algorithm C in the round specified by length_iteration",
            "-1");
   		add_option<int>(
            "start_length",
            "only if length_iteration != -1. Start value for C.",
            "5");
   		add_option<int>(
            "disabling_threshold",
            "threshold for the size of the disabling graph. If graph becomes larger than this, make simplifying assumptions.",
            "5000000");
   		add_option<bool>(
            "join_groups_above_threshold",
            "join all groups of operators above the exists-step threshold into a single big group",
            "true");
   		add_option<double>(
            "multiplier",
            "only if length_iteration != -1. Multiplier for C.",
            "1.41");
   		add_option<bool>(
            "use_p",
            "use Rintanen's p as the branching heuristic for the SAT solver. This only works in conjunction with a modified version of kissat",
            "true");
   		add_option<bool>(
            "disable_elimination",
            "disable the SAT solver's variable elimination techniques.",
            "false");
     sat_search::add_sat_search_options_to_feature(*this,"sat");
    }


    virtual shared_ptr<sat_search::SATSearch>
    create_component(const plugins::Options &opts) const override {
        plugins::Options options_copy(opts);
        return plugins::make_shared_from_arg_tuples<sat_search::SATSearch>(
			options_copy.get<int>("encoding"),
			options_copy.get<int>("plan_length"),
			options_copy.get<int>("length_iteration"),
			options_copy.get<int>("start_length"),
			options_copy.get<double>("multiplier"),
			options_copy.get<int>("disabling_threshold"),
			options_copy.get<bool>("join_groups_above_threshold"),
			options_copy.get<bool>("use_p"),
			options_copy.get<bool>("disable_elimination"),
            sat_search::get_sat_search_arguments_from_options(options_copy)
			);
    }


};

static plugins::FeaturePlugin<SATSearchFeature> _plugin;
}
