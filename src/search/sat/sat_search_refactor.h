#ifndef SEARCH_ALGORITHMS_EAGER_SEARCH_H
#define SEARCH_ALGORITHMS_EAGER_SEARCH_H

#include "../search_algorithm.h"
#include "sat_encoder.h"

#include <memory>
#include <vector>
#include <map>
#include <set>


namespace plugins {
class Feature;
}

struct sat_capsule;

namespace sat_search {

// Represents a strongly connected component (SCC) in the axiom dependency graph.
struct AxiomSCC{
	
    std::vector<int> variables;

	bool sizeOne = false;
	bool isOfImplicationType = false;
	bool isDependentOnOneVariableInternally = false;
	int dependingVariable = false;

	bool fullComputationRequired = false;
	int numberOfAxiomLayers;

	// preprocessing information implications
	std::vector<std::vector<int>> direct_transitive_implications;
	std::vector<std::vector<int>> direct_transitive_causes;

	// preprocessing information guarded implications (i.e. ones that depend on a variable value)
	std::vector<std::vector<std::vector<int>>> guarded_transitive_implications;
	std::vector<std::vector<std::vector<int>>> guarded_transitive_causes;

};

// Encapsulates the axiom/derived predicate dependency graph and related reasoning.
class AxiomDependencyGraph {
public:
    // Graph structures
    std::vector<std::vector<int>> derived_implication;
    std::vector<std::vector<int>> pos_derived_implication;
    std::vector<std::vector<int>> neg_derived_implication;
    std::map<FactPair, std::vector<int>> derived_entry_edges;

    // Statically true predicates derived from axioms
    std::unordered_set<int> statically_true_derived_predicates;

    // Relation: derived variable to achieving operators
    std::vector<std::vector<OperatorProxy>> map_dp_to_achieving_axioms;

    // SCCs and in topological order
    std::vector<AxiomSCC> axiom_SCCs_in_top_order;
    
    void setup_axioms(const TaskProxy &task_proxy);
    void axiom_dfs(int var, std::set<int> & pos_reachable, std::set<int> & neg_reachable, bool mode);


private: 
    void clear_and_resize(size_t num_vars);
    void find_statically_true_derived_predicates(const TaskProxy &task_proxy);
    void build_dependency_graph(const TaskProxy &task_proxy);
    void compute_sccs(const TaskProxy &task_proxy);

    // clear_and_resize_axiom_structures();
    // AxiomsProxy axioms = task_proxy.get_axioms();
    // find_statically_true_derived_predicates(axioms);
    // build_derived_predicate_dependency_graph(axioms);
    // compute_derived_predicate_sccs();
    // preprocess_axiom_sccs();
    // log_axiom_statistics();
};

enum class SATEncoding {
    SEQUENTIAL = 0,
	// TODO: implement for all encoding as enum 1
    EXISTS_STEP = 2,
    RELAXED_EXISTS_STEP = 3,
    RELAXED_RELAXED_EXISTS_STEP = 4
};

class SATEncodingStrategy {
public:
    virtual ~SATEncodingStrategy() = default;
    virtual void setup_encoding(SATSearch &search) = 0;
};

class SequentialEncodingStrategy : public SATEncodingStrategy {
public:
    void setup_encoding(SATSearch &search) override;
};

class ExistsStepEncodingStrategy : public SATEncodingStrategy {
public:
    void setup_encoding(SATSearch &search) override;
};

class RelaxedExistsStepEncodingStrategy : public SATEncodingStrategy {
public:
    void setup_encoding(SATSearch &search) override;
};



// Implements SAT-based planning search.
class SATSearch : public SearchAlgorithm {
public:
    // Expose task_proxy for use in SAT solver heuristics.
    using SearchAlgorithm::task_proxy;

    // --- Configuration Parameters ---
    // Mirrored from plugin_sat.cc for consistency.
    int plan_length;
    SATEncoding encoding;
	int length_iteration;
	int start_length;
    int disabling_threshold;
	bool join_groups_above_threshold; //TODO: update from aboveThresholdGroupJoining;
    double multiplier;
    bool use_rintanens_p;
    bool disable_var_elimination;   //TODO: update from disableVARElimination

    // --- Search Control ---
    // Internally controlled parameters.
	int current_length;
    bool force_at_least_one_action;

    // --- SAT Variable Storage ---
    // Variables for facts, operators, and axioms indexed by timestep.
    std::vector<std::vector<std::vector<int>>> fact_variables;      // index: timestep -> variable -> value
    std::vector<std::vector<int>> operator_variables;               // index: timestep -> variable
    std::vector<std::vector<std::vector<int>>> axiom_variables;     // index: timestep -> variable -> value

    // Getters for SAT variables
    int get_fact_var(int time, FactProxy fact);
    int get_axiom_var(int time, int layer, FactProxy fact);
    int get_last_axiom_var(int time, FactProxy fact);

    // Encapsulates axiom/derived predicate reasoning as required by SAS+ representation.
    AxiomDependencyGraph derived_predicate_graph;

    // --- SAT Solver constructor/destructor ---
    explicit SATSearch(
				int _encoding,
				int	_planLength,
				int	_lengthIteration,
				int	_startLength,
				double	_multiplier,
				int	_disablingThreshold,
				bool	_aboveThresholdGroupJoining,
				bool	_useRintanensP,
				bool	_disableVARElimination,
				// inherited from search algorithm
				OperatorCost cost_type,
    			int bound,
				double max_time,
				const std::string &description,
    			utils::Verbosity verbosity);
    virtual ~SATSearch() = default;

    virtual void print_statistics() const override;

protected:
    // --- Search operations ---
    virtual void initialize() override;
    virtual SearchStatus step() override;

};

// Function to add SAT search options to a feature.
extern void add_sat_search_options_to_feature(plugins::Feature &feature, const std::string &description);
// Function to retrieve SAT search arguments from options.
extern std::tuple<OperatorCost, int, double, std::string, utils::Verbosity>
get_sat_search_arguments_from_options(const plugins::Options &opts);

}

#endif