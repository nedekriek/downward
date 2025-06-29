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

struct AxiomSCC{
	std::vector<int> variables;
	bool sizeOne = false;
	bool isOfImplicationType = false;
	bool isDependentOnOneVariableInternally = false;
	int dependingVariable = false;


	bool fullComputationRequired = false;
	int numberOfAxiomLayers;

	// preprocessing information implications
	std::vector<std::vector<int>> directTransitiveImplications;
	std::vector<std::vector<int>> directTransitiveCauses;

	// preprocessing information guarded implications (i.e. ones that depend on a variable value)
	std::vector<std::vector<std::vector<int>>> guardedTransitiveImplications;
	std::vector<std::vector<std::vector<int>>> guardedTransitiveCauses;
	
};

class SATSearch : public SearchAlgorithm {
public:
    // Make task_proxy public for access in sat solver heuristic
    using SearchAlgorithm::task_proxy;
	
	// debugging / output configuration
	bool logInference = false;
	
	// actual run configuration
	int planLength;
	int currentLength;
	int lengthIteration;
	int startLength;
	double multiplier;
	bool existsStep = true;
	int disablingThreshold;
	bool aboveThresholdGroupJoining;
	bool useRintanensP;
	bool disableVARElimination;

	bool forceAtLeastOneAction;

	std::vector<bool> is_leaf_operator;

	// index: timestep -> variable -> value
	std::vector<std::vector<std::vector<int>>> fact_variables;
	// index: timestep -> operator 
	std::vector<std::vector<int>> operator_variables;
	std::vector<std::vector<int>> real_operator_variables;
	int get_fact_var(int time, FactProxy fact);

	std::unordered_set<int> statically_true_derived_predicates;

	// index: timestep -> variable
	std::vector<std::vector<std::vector<int>>> axiom_variables;
	int get_axiom_var(int time, int layer, FactProxy fact);
	int get_last_axiom_var(int time, FactProxy fact);

	//// variable -> value -> list of actions
	//std::vector<std::vector<std::vector<int>>> achiever;
	//std::vector<std::vector<std::vector<int>>> deleter;

	// axiom structure graph
	std::vector<std::vector<int>> derived_implication;
	std::vector<std::vector<int>> pos_derived_implication;
	std::vector<std::vector<int>> neg_derived_implication;
	std::map<FactPair, std::vector<int>> derived_entry_edges;
	void axiom_dfs(int var, std::set<int> & posReachable, std::set<int> & negReachable, bool mode);
	// axiom SCCs
	std::vector<AxiomSCC> axiomSCCsInTopOrder;
	std::vector<std::vector<OperatorProxy>> achievers_per_derived;
	
	void printVariableTruth(void* solver, sat_capsule & capsule);


	bool try_to_satisfy(std::set<int> & activeAxtioms, std::set<FactPair> & currentState, FactPair goal);


	void compute_necessary_effects(int op, FactPair assumedFact,
		std::set<FactPair> & maintainedFacts,
		std::set<FactPair> & potentialEffects,
		std::set<FactPair> & definitiveEffects,
			bool evaluateAxiomsAfter);

	std::set<FactPair> evaluate_axioms_on_partial_state(std::set<FactPair> & definitiveEffects);
	
	void speculative_evaluate_axioms_on_partial_state(
			std::set<FactPair> & maintainedFacts,
			std::set<FactPair> & possibleEffects, std::set<FactPair> & definitiveEffects);


	std::set<FactPair> compute_known_prior_state(int op, FactPair assumedFact);


	// exists step
    std::vector<std::vector<FactPair>> sorted_op_preconditions;
    std::vector<std::vector<FactPair>> sorted_op_effects;
	bool can_be_executed_in_same_state(int op1_no, int op2_no);
	bool have_actions_unconflicting_effects(int op1_no, int op2_no);
	std::vector<int> global_action_ordering;
	// generate Erasing and Requiring list
	// per fact, per SCC, gives a list of all E/R as a pair: <operator,position_in_scc>
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> erasingList;
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> requiringList;

	void exists_step_restriction(void* solver,sat_capsule & capsule, std::vector<int> & operator_variables, int time);
	void generateChain(void* solver,sat_capsule & capsule, std::vector<int> & operator_variables,
		    const std::vector<std::pair<int, int>>& E, const std::vector<std::pair<int, int>>& R, int time);

	
	std::map<std::string,int> clauseCounter;
	std::map<std::string,int> variableCounter;
	
	void set_up_exists_step();
	void set_up_single_step();

	// Kissat interface
	std::map<FactPair,std::vector<std::pair<int,std::vector<FactPair>>>> addingActions;
	int get_last_axiom_var(int time, FactPair fact);
	int get_fact_var(int time, FactPair fact);


protected:
    virtual void initialize() override;
    virtual SearchStatus step() override;

public:
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
};

extern void add_sat_search_options_to_feature(plugins::Feature &feature, const std::string &description);
extern std::tuple<OperatorCost, int, double, std::string, utils::Verbosity>
get_sat_search_arguments_from_options(const plugins::Options &opts);
}

#endif
