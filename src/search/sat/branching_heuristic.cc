#include <iostream>
#include "../utils/rng.h"
#include "kissat-p.h"
#include "sat_search.h"
#include "branching_heuristic.h"
#include "../abstract_task.h"
#include <queue>

using namespace std;
// gives global(!) pointer to the SAT search object for communication with the SAT solver
extern sat_search::SATSearch* kissatSearch;
extern int kissatCurrentLength;
extern bool kissatReachedFinalStage;

utils::RandomNumberGenerator rng;

extern "C" {

void setup_kissat_for_custom_heuristic(void* solver, bool useRintanensP, bool disableVARElimination){
	if (useRintanensP)
		kissat_set_external_decision_function(rintanens_p);

	if (disableVARElimination){
		kissat_set_option((kissat*)solver,"autarky",0);
		kissat_set_option((kissat*)solver,"xors",0);
		kissat_set_option((kissat*)solver,"ands",0);
		kissat_set_option((kissat*)solver,"forward",0);
		kissat_set_option((kissat*)solver,"eliminate",0);
		kissat_set_option((kissat*)solver,"substitute",0);
	}
}

int var_removed_counter = 0;
int final_stage_calls = 0;
void warn_var_removed(int var){
	cout << "[Warning] variable " << var << " has been eliminated." << endl;
	//exit(0);
	var_removed_counter++;
}


// given a fact pair: what is the value of its sat variable. Can return values from -2 to 2
int get_sat_var_for_factpair(const FactPair & fact, int time){
	if (time < 0){
		cout << "[ERROR] Trying to determine sat variable for time less than 0: " << time << endl;
		exit(-1);
	}

	int var = 0;
	if (kissatSearch->task_proxy.get_variables()[fact.var].is_derived()){
		var = kissatSearch->get_last_axiom_var(time,fact);
	} else {
		var = kissatSearch->get_fact_var(time,fact);
	}

	return var;
}

int get_truth_of_fact_at_time(struct kissat * solver, const FactPair & fact, int time){
	int sat_var = get_sat_var_for_factpair(fact, time);
	int var_truth = kissat_get_truth_of_external_var(solver,sat_var);

	if (var_truth == -2) warn_var_removed(sat_var);
	if (var_truth == 2) {
		cout << "kissat_error on var " << sat_var << " is " << var_truth << endl;
		exit(-1);
	}
	return var_truth;
}

int get_truth_of_action_at_time(struct kissat * solver, int op, int time){
	assert(time >= 0);
	assert(time < int(kissatSearch->operator_variables.size()));
	assert(op >= 0);
	assert(op < int(kissatSearch->operator_variables[time].size()));
	int op_var = kissatSearch->operator_variables[time][op];
	int op_truth = kissat_get_truth_of_external_var(solver,op_var);
	if (op_truth == -2) warn_var_removed(op_var);
	if (op_truth == 2) {
		cout << "kissat_error on op " << op << " -> " << op_var << " is " << op_truth << endl;
		exit(-1);
	}
	return op_truth;
}

int compute_priority_time_for_fact(struct kissat * solver, const FactPair & fact, const int & time){
	// compute the priority time for this fact
	int priorityTime = time;
	while (priorityTime > 0){
		priorityTime--;
		int var_truth = get_truth_of_fact_at_time(solver, fact, priorityTime);
		// found latest time at which the variable is not known to be true.
		if (var_truth != 1) break;
	}
	
	return priorityTime;
}




sat_fact get_sat_fact_for(struct kissat * solver, FactPair fact, int time, bool &isStaticallyTrue, bool &isStaticallyFalse){
	assert(time >= 0); // only facts after the initial state can be branched on.
	isStaticallyTrue = false;
	isStaticallyFalse = false;
	sat_fact f(fact);
	f.time = time;
	
	// statically true check
	if (kissatSearch->statically_true_derived_predicates.count(fact.var) == 1){
		if (fact.value == 1){
			isStaticallyTrue = true;
		} else {
			isStaticallyFalse = true;
		}
		return f;
	}

	f.sat_var = get_sat_var_for_factpair(fact, time);
	f.priorityTime = compute_priority_time_for_fact(solver, fact, time);


	return f;
}


// returns true if adding was successful
bool add_all_preconditions_of_action_to_queue(struct kissat * solver, priority_queue<sat_fact> & q, set<sat_fact> & inQueue, const std::vector<FactPair>  & conditions, int t){
	vector<sat_fact> pre_facts;
	bool oneFalse = false;
	// first check if one of them is known to be false -> this can happen for conditions of conditional effects
	for (const FactPair & f : conditions){
		bool isTrue, isFalse;
		sat_fact sf = get_sat_fact_for(solver,f,t,isTrue,isFalse);
		if (isFalse){ oneFalse = true; break; }
		if (isTrue) continue;
		pre_facts.push_back(sf);
	}
	// this is not the right operator
	if (oneFalse) return false;

	// we reached the initial state, nothing to do.	
	if (t > 0)
		for (const sat_fact & sf : pre_facts){
			if (inQueue.count(sf)) continue;
			q.push(sf);
			inQueue.insert(sf);
		}
	return true;
}


bool rintanens_p_termination(unordered_set<int> &Z, int t, int bound){
	if (Z.size() >= 40 || t >= bound) return true;
	return false;
}

void rintanens_p_cleanup(unordered_set<int> &Z, int t, int bound, int last){
	if (t < bound) Z.insert(last);
}

unordered_set<int> rintanens_p_support(struct kissat * solver){
	//cout << "========================================" << endl << "I am in FD " << var_removed_counter << endl;

	set<sat_fact> inQueue;
	priority_queue<sat_fact> q;
	//stack<sat_fact> q;

	// add all goals to the queue.
	GoalsProxy goals = kissatSearch->task_proxy.get_goals();
	for (size_t i = 0; i < goals.size(); i++){
		bool isTrue, isFalse;
		// kissatCurrentLength is the overall number of time steps, i.e. the time of the goal.
		sat_fact f = get_sat_fact_for(solver,goals[i].get_pair(),kissatCurrentLength,isTrue,isFalse);
		if (isTrue) continue;
		if (isFalse) assert(false);

		q.push(f);
		inQueue.insert(f);
	}

	// set of sat variables that we can branch on.
	unordered_set<int> Z;

	int first_found_action = kissatCurrentLength;

	while (q.size()){
		//cout << "Taking one Fact" << endl;
		sat_fact f = q.top();
		q.pop();

		// search for a supporting action backwards from the goal.
		int t = f.time - 1;
		bool found = false;
		do {
			assert(t >= 0);
			//cout << "LOOP START FOR " << t << endl;
			//
			// search for an action that can make the fact f true.
			for (const auto & [op, conditions] : kissatSearch->addingActions[f.fact]){
				//cout << "ACC " << t << " (" << kissatSearch->operator_variables.size() << ")" << endl;
				//cout << "\t " << op << " (" << kissatSearch->operator_variables[t].size() << ")" << endl;
				int op_truth = get_truth_of_action_at_time(solver,op,t);

				if (op_truth == 1){
					// this action is to be chosen, so all of its preconditions must be true
					bool can_produce_fact = add_all_preconditions_of_action_to_queue(solver,q,inQueue,conditions, t);
					if (!can_produce_fact) continue;
					//cout << "Found true achiever action. Inserting Preconditions |q|=" << q.size() << endl;
					// found the chosen achiever
					found = true;
					// only find the first action.
					break;
				}
			}
			// we found the achiever
			if (found) break;
			
			// no achiever found at time t
			int f_truth = get_truth_of_fact_at_time(solver, f.fact, t);
			
			//cout << "Truth status of this fact: " << sf.sat_var << " is " << f_truth << endl; 
			if (f_truth == -1){
				//cout << "Fact is false here. Branching on Achiever" << endl;
				// fact is false at time t -> it must become true at some point after this time, so let's try to do it now!
				for (const auto & [op, conditions] : kissatSearch->addingActions[f.fact]){
					int op_truth = get_truth_of_action_at_time(solver, op, t);
					// if operator is false, we cannot select it as an achiever here.
					if (op_truth == -1) continue;
					
					// if the variable has been eliminated, we also can't branch on it
					if (op_truth == -2) continue;

					// try to choose this action for the particular effect
					bool can_produce_fact = add_all_preconditions_of_action_to_queue(solver,q,inQueue,conditions, t);
					if (!can_produce_fact) continue; // effect is not realisable, so try next one

					// this action may be the one we are branching on.
					int op_var = kissatSearch->operator_variables[t][op];
					//cout << "Insert |Z|=" << Z.size() << endl;
					found = true;
					// termination test
					if (rintanens_p_termination(Z,t,first_found_action)){
						//cout << "Terminate |Z|=" << Z.size() << " t=" << t << " first=" << first_found_action << endl;
						rintanens_p_cleanup(Z,t,first_found_action,op_var);
						//cout << "Cleanup |Z|=" << Z.size() << endl;
						return Z;
					}

					Z.insert(op_var);
					// record time of first found action.
					if (Z.size() == 1) first_found_action = t;
					break; // take only one of the possible achievers
				}
				//cout << "\tLooped over all Achievers" << endl;
			}
			
			if (t == 0) {
				//cout << "Reached Init" << endl;
				// f is true in init, so let's assume it stays true.
				break; 
			}

			// look for the previous time step
			t--;
			//cout << "END OF LOOP " << t << " cond " << (found == false) << endl; 
		} while (found == false);
	}

	return Z;
}



unsigned rintanens_p(struct kissat * solver, int * made_decision){
	if (kissatReachedFinalStage){
		*made_decision = 0;
		return 0;
		//// the only remaining variables are chain variables.
		//// it is best to set them to false
		//for (int v = kissatNVar; v >= 1; v--){
		//	int truth = kissat_get_truth_of_external_var(solver,v);
		//	if (truth == 0){
		//		*made_decision = 1;
		//		return -v;
		//	}	
		//
		//}
	}


	unordered_set<int> Z = rintanens_p_support(solver);


	//if (var_removed_counter) cout << "Var Removed " << var_removed_counter << endl;

	//cout << "Found " << Z.size() << " facts to branch on:";
	//for (const int & x : X) cout << " " << x;
	//cout << endl;

	if (Z.size() == 0){
		//cout << "Plan is causally complete." << endl;
		// advice is to keep all truth values of facts
		for (size_t var = 0; var < kissatSearch->task_proxy.get_variables().size(); var++){
			if (kissatSearch->statically_true_derived_predicates.count(var)) continue;
			VariableProxy varProxy = kissatSearch->task_proxy.get_variables()[var];
			for (int val = 0; val < varProxy.get_domain_size(); val++){
				FactPair f(var,val);
				// loop from init forwards
				bool wasTrue = false;
				for (int t = 0; t <= kissatCurrentLength; t++){
					int var_truth = get_truth_of_fact_at_time(solver,f,t);
					// eliminated variables are no good
					if (var_truth == -2) break;
					if (var_truth == 0){
						// try to set it to truth at previous time
						*made_decision = 1;
						if (wasTrue) return get_sat_var_for_factpair(f,t);
						else return -get_sat_var_for_factpair(f,t);
					} else if (var_truth == 1) wasTrue = true; else if (var_truth == -1) wasTrue = false;
				}
			}
		}

		// all state variables are set or have been eliminated
		// set all actions to false, we don't need them
		for (int t = 0; t < kissatCurrentLength; t++){
			for(size_t op = 0; op < kissatSearch->task_proxy.get_operators().size(); op ++){
				int op_truth = get_truth_of_action_at_time(solver,op,t);
				if (op_truth == 0){
					*made_decision = 1;
					return -kissatSearch->operator_variables[t][op];
				}	
			}
		}


		//if (var_removed_counter) cout << "Var Removed " << var_removed_counter << endl;
		//cout << "No more advice" << endl;
		// no decision was made
		*made_decision = 0;
		//exit(0);
		kissatReachedFinalStage = true;
		cout << "kissat: reached final state of branching. Leaving all decisions to kissat from now on." << endl;
		return 0;
	}
	//cout << "Plan is causally incomplete." << endl;


	int random = rng.random(Z.size());
	vector<int> ZZ(Z.begin(),Z.end());

	//exit(0);
	*made_decision = 1;
	return ZZ[random];
}



};

