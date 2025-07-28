#ifndef SEARCH_ALGORITHMS_EAGER_SEARCH_H
#define SEARCH_ALGORITHMS_EAGER_SEARCH_H

#include "../search_algorithm.h"
#include "sat_encoder.h"

#include <memory>
#include <vector>
#include <map>
#include <set>

namespace sat_search {

struct OperatorDependencies {
    std::map<FactPair, std::set<int>> needing_actions; //TODO: change to in_operator_preconditions // Fact and associated actions needing the fact as a condition
    std::map<FactPair, std::set<int>> deleting_actions; //TODO: change to in_operator_deleting_effects // Fact and associated actions that have deleting the fact as an effect
    std::map<FactPair, std::set<int>> adding_actions; //TODO change to in_operator_adding_effects// Fact and associated actions adding the fact as an effect
};

struct DisablingGraph {
    std::vector<std::set<int>> graph; // Represents the disabling graph
    int number_of_edges = 0; // Total number of edges in the graph
    int number_refuted_edges = 0; // Number of refuted edges in the graph
    std::unordered_set<int> sequential_operators; // Set of sequential operators
    std::set<FactPair> threshold_facts; // Set of threshold facts

    // Constructor to initialize the graph with a given size
    explicit DisablingGraph(size_t size) : graph(size) {}
};

class ImplicationGraph{
public:
	void generateChain(void* solver,sat_capsule & capsule, std::vector<int> & operator_variables,
		    const std::vector<std::pair<int, int>>& E, const std::vector<std::pair<int, int>>& R, int time);
};

class SatEncodingStrategy {
public:
    std::vector<int> global_action_ordering;

    virtual ~SatEncodingStrategy() = default;

    // Define the interface for encoding
    virtual void encode(SATSearch &search);
    virtual void compute_global_action_ordering(SATSearch &search);
};

class SequentialEncodingStrategy : public SatEncodingStrategy {
public:
    void encode(SATSearch &search) override;
    void compute_global_action_ordering(SATSearch &search) override;
};

class ExistsStepEncodingStrategy : public SatEncodingStrategy {
public:
    // --- SAT
    std::map<FactPair,std::vector<std::pair<int,std::vector<FactPair>>>> adding_actions;

    void encode(SATSearch &search) override;
    void compute_global_action_ordering(SATSearch &search) override;
};

// class RelaxedExistsStepEncodingStrategy : public SatEncodingStrategy {
// public:
//     void encode(SATSearch &search) override;
//     void compute_global_action_ordering(SATSearch &search) override;
// };
 
class SATSearch : public SearchAlgorithm {
public:
    // Make task_proxy public for access in sat solver heuristic
    using SearchAlgorithm::task_proxy;

    // --- DATA MEMBERS ---

    // --- Configuration Parameters ---
    // Mirrored from plugin_sat.cc for consistency.
    int plan_length;
    std::unique_ptr<SatEncodingStrategy> encoding_strategy;     //set by processing encoding parameter 
	int length_iteration;
	int start_length;
    int disabling_threshold;
	bool join_groups_above_threshold; //TODO: update from aboveThresholdGroupJoining;
    double multiplier;
    bool use_rintanens_p;
    bool disable_var_elimination;    //TODO: update from disableVARElimination

    // --- Search Control ---
    // Internally controlled parameters.
	int current_length;
    bool force_at_least_one_action;

    

    // --- MEMBER FUNCTIONS ---

    explicit SATSearch(
				int encoding,
				int _plan_length,
				int _length_iteration,
				int _start_length,
				double _multiplier,
				int _disabling_threshold,
				bool _above_threshold_group_joining,
				bool _use_rintanens_p,
				bool _disable_var_elimination,
				OperatorCost cost_type,         // inherited from SearchAlgorithm
                int bound,                      // inherited from SearchAlgorithm
				double max_time,                // inherited from SearchAlgorithm
				const std::string &description, // inherited from SearchAlgorithm
				utils::Verbosity verbosity      // inherited from SearchAlgorithm
            );
    virtual ~SATSearch() = default;

    virtual void print_statistics() const override;

protected:
    // --- Search operations ---
    virtual void initialize() override;
    virtual SearchStatus step() override;
};

std::vector<FactProxy> compute_full_conditions(const TaskProxy &task_proxy);
};

#endif