#include <cmath>
#include <iomanip>
// #include <fstream>
// #include <sstream>

#include "sat.h"
#include "kissat-p.h"

#include "../plugins/options.h"

#include "../algorithms/sccs.h"

#include "../utils/logging.h"

#include "sat_encoder.h"

using namespace std;

// Global variables for the SAT search
sat_search::SATSearch* kissatSearch;
int kissatCurrentLength;
int kissatNVar;
bool kissatReachedFinalStage;

namespace sat_search {

SATSearch::SATSearch(
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
    utils::Verbosity verbosity)      // inherited from SearchAlgorithm
    : SearchAlgorithm(cost_type, bound, max_time, description, verbosity),  // call parent constructor and set parameters
	plan_length(_plan_length),
	length_iteration(_length_iteration),
	start_length(_start_length),
	multiplier(_multiplier),
	disabling_threshold(_disabling_threshold),
	join_groups_above_threshold(_above_threshold_group_joining),
	use_rintanens_p(_use_rintanens_p),
	disable_var_elimination(_disable_var_elimination)
	{
    // Parse the encoding parameter and set the strategy
    switch (encoding) {
        case 0:
            encoding_strategy = std::make_unique<SequentialEncodingStrategy>();
            log << "Using SEQUENTIAL encoding" << endl;
            break;
        case 2:
            encoding_strategy = std::make_unique<ExistsStepEncodingStrategy>();
            log << "Using EXISTS_STEP encoding" << endl;
            break;
        // case 3: 
        //     encoding_strategy = std::make_unique<RelaxedExistsStepEncodingStrategy>();
        //     log << "Using RELAXED_EXISTS_STEP encoding" << endl;
        //     break;
        // case 4:
        //     encoding_strategy = std::make_unique<RelaxedRelaxedExistsStepEncodingStrategy>();
        //     log << "Using RELAXED_RELAXED_EXISTS_STEP encoding" << endl;
        //     break;  
        default:
            log << "Error: encoding No " << encoding << " is not supported" << endl;
            exit(-1);
    }

	force_at_least_one_action = true;

	current_length = 1;
	if (plan_length != -1) current_length = plan_length;

	if (length_iteration != -1){
		current_length = plan_length = int(0.5 + start_length * pow(multiplier, length_iteration));
		force_at_least_one_action = false;
	}
}

void SATSearch::initialize() {
    log << "Conducting SAT search for plan length: "
        << (plan_length == -1 ? "all" : to_string(plan_length)) << endl;

	// Build Axiom Dependency Graph to identify derived predicates
	// set_up_axioms();
	// TODO: Identify if all encoding stats use the axiom dependency graph

	if (encoding_strategy) {
        encoding_strategy->encode(*this);
    } else {
        log << "Error: No encoding strategy set!" << endl;
        exit(-1);
    }

    // Set up data structures for derived predicates and axioms

    // assert(global_action_ordering.size() == task_proxy.get_operators().size());
}

std::vector<FactProxy> compute_full_conditions(const TaskProxy &task_proxy) {
    std::vector<FactProxy> full_conditions;
	
	OperatorsProxy operators = task_proxy.get_operators();
	for (size_t op_index = 0; op_index < operators.size(); ++op_index) {
		OperatorProxy op = operators[op_index];
		
		PreconditionsProxy preconditions = op.get_preconditions();
		for (size_t pre_index = 0; pre_index < preconditions.size(); pre_index++) {
			FactProxy precondition_fact = preconditions[pre_index];
			full_conditions.push_back(precondition_fact);
		}

		EffectsProxy effects = op.get_effects();
		for (size_t eff_index = 0; eff_index < effects.size(); eff_index++) {
			EffectProxy effect = effects[eff_index];
			EffectConditionsProxy effect_conditions = effect.get_conditions();
			for (size_t cond_index = 0; cond_index < effect_conditions.size(); cond_index++) {
				FactProxy effect_condition_fact = effect_conditions[cond_index];
				full_conditions.push_back(effect_condition_fact);
			}
		}
	}

	return full_conditions;
}

    


void SequentialEncodingStrategy::encode(SATSearch &search) {
    global_action_ordering.clear();
    compute_global_action_ordering(search); 
}

void SequentialEncodingStrategy::compute_global_action_ordering(SATSearch &search) {
    for (size_t op = 0; op < search.task_proxy.get_operators().size(); op++) {
        global_action_ordering.push_back(op);
    }
};

OperatorDependencies preprocess_operator_effects_and_dependencies (SATSearch &search) {
	// Preprocess actions/operators. Identifying the following relationships between facts and actions:
    OperatorDependencies dependencies;
    dependencies.needing_actions = {};		// 1. actions which need the fact to be true as a condition
	dependencies.deleting_actions = {}; 	// 2. actions which (implicitly) delete the fact as a effect
	dependencies.adding_actions = {}; 		// 3. actions which add the fact as an effect

	//TODO:figure out adding_actions and why it is needed by kissat

	OperatorsProxy operators = search.task_proxy.get_operators();
	for (size_t op_index = 0; op_index < operators.size(); ++op_index) {
		// if (op_index % 1000 == 0)
		// 	log << "Disabling Graph Operator " << op_index << " of " << search.task_proxy.get_operators().size() << endl;

		OperatorProxy op = operators[op_index];
		std::vector<FactPair> operator_full_preconditions;
		map<int,int> precondition_variable_id_fact_map;
	
		PreconditionsProxy preconditions = op.get_preconditions();
		for (size_t pre_index = 0; pre_index < preconditions.size(); pre_index++) {
			FactProxy precondition_fact = preconditions[pre_index];
			dependencies.needing_actions[precondition_fact.get_pair()].insert(op_index);
			precondition_variable_id_fact_map[precondition_fact.get_variable().get_id()] = precondition_fact.get_value();
			operator_full_preconditions.push_back(precondition_fact.get_pair());
		}

		EffectsProxy effects = op.get_effects();
		for (size_t eff_index = 0; eff_index < effects.size(); eff_index++) {
			std::vector<FactPair> operator_full_conditions_for_single_effect = operator_full_preconditions;
			EffectProxy effect = effects[eff_index];
			EffectConditionsProxy effect_conditions = effect.get_conditions();
			for (size_t cond_index = 0; cond_index < effect_conditions.size(); cond_index++) {
				FactProxy effect_condition_fact = effect_conditions[cond_index];
				needing_actions[effect_condition_fact.get_pair()].insert(op_index);
				precondition_variable_id_fact_map[effect_condition_fact.get_variable().get_id()] = effect_condition_fact.get_value();
				operator_full_conditions_for_single_effect.push_back(effect_condition_fact.get_pair());
			}

			// For each effect tracks what operator can add it and what preconditions need to be met to do so.
			dependencies.adding_actions[effect.get_fact().get_pair()].push_back(
					{op_index, operator_full_conditions_for_single_effect});
			
			//TODO implement axiom dependency graph
			//Identify if the application of this operator via its adding effect changes the value of derived predicates
			for (int & start : derived_entry_edges[effect.get_fact().get_pair()]){
				set<int> posReachable, negReachable;  // Modified by the axiom_dfs function
				axiom_dfs(start, posReachable, negReachable, true); // 'start' fact has become true
				for (const int & reach : posReachable){
					deleting_actions[FactPair(reach,0)].insert(op_index);
					adding_actions[FactPair(reach,1)].push_back({op_index,operator_full_conditions_for_single_effect});
				}
				for (const int & reach : negReachable){
					deleting_actions[FactPair(reach,1)].insert(op_index);
					adding_actions[FactPair(reach,0)].push_back({op_index,operator_full_conditions_for_single_effect});
				}
			}

			for (int val = 0; val < effect.get_fact().get_variable().get_domain_size(); val++){
				// If the value is the same as the effect fact's value, skip it
				if (val == effect.get_fact().get_value()) continue;
				// If the precondition variable id fact map contains the variable id and the value is not
				// the same as the effect fact's value, skip it
				if (precondition_variable_id_fact_map.count(effect.get_fact().get_variable().get_id()) &&
					precondition_variable_id_fact_map[effect.get_fact().get_variable().get_id()] != val)
					continue;
				// It must be that the effect changes the value of the variable, so we add the operator 
				// as a (implicit) deleting action
				FactPair deletedFact(effect.get_fact().get_variable().get_id(),val);
				dependencies.deleting_actions[deletedFact].insert(op_index);

				//Identify if the application of this operator via its deleting effect changes the value of derived predicates
				for (int & start : derived_entry_edges[deletedFact]){
					set<int> posReachable, negReachable;
					axiom_dfs(start,posReachable, negReachable, false); // `start` fact has implictly become false
				
					for (const int & reach : posReachable)
						dependencies.deleting_actions[FactPair(reach,0)].insert(op_index);
					for (const int & reach : negReachable)
						dependencies.deleting_actions[FactPair(reach,1)].insert(op_index);
				}
			}
		}
	}
	return dependencies;
}

void ExistsStepEncodingStrategy::encode(SATSearch &search) {
    global_action_ordering.clear();
	
	OperatorDependencies dependencies = preprocess_operator_effects_and_dependencies(search);

	DisablingGraph disabling_graph(search.task_proxy.get_operators().size());
   
		for (auto [fact, deleting_operators] : dependencies.deleting_actions){
			// If there are no operators needing this fact as a (pre)condition, it is a threshold fact
			if (dependencies.needing_actions[fact].size() == 0) {
				disabling_graph.threshold_facts.insert(fact);
				continue;
			}
		int checkSize = deleting_operators.size() * dependencies.needing_actions[fact].size();
		//log << "DG " << fact << " deleter " << deleting_operators.size() << " needers " << dependencies.needing_actions[fact].size() << " checks " << checkSize << endl;
		if (checkSize > search.disabling_threshold){
			disabling_graph.threshold_facts.insert(fact);
			unordered_set<int> this_sequential_operators;
			for (int deleter : deleting_operators){
				disabling_graph.sequential_operators.insert(deleter);
				this_sequential_operators.insert(deleter);
			}
			for (int needer : dependencies.needing_actions[fact]){
				disabling_graph.sequential_operators.insert(needer);
				this_sequential_operators.insert(needer);
			}

			if (search.join_groups_above_threshold) continue;

			vector<int> atMostOneGroup;
			for (const int & op : thisSequentialOperators)
				atMostOneGroup.push_back(op);

			continue;
		}
		for (int deleter : deleting_operators){
			for (int needer : needingActions[fact]){
				if (deleter == needer) continue;
				// if preconditions are incompatible, action's don't disable each other
				if (!can_be_executed_in_same_state(deleter,needer)) {
					number_refuted_edges_in_disabling_graph++;
					continue;	
				}
				if (!have_actions_unconflicting_effects(deleter,needer)) {
					number_refuted_edges_in_disabling_graph++;
					continue;	
				}

				// deleter disables needer
				if (disabling_graph[deleter].count(needer)) continue; // only count inserted edges once

				disabling_graph[deleter].insert(needer);
				number_of_edges_in_disabling_graph++;
			}
		}
	}


    compute_global_action_ordering(search);
}



