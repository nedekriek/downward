#ifndef _branching_heuriustic_h_INCLUDED
#define _branching_heuriustic_h_INCLUDED


#include "kissat.h"
#include <set>
#include <queue>
#include "../abstract_task.h"


struct sat_fact {
	int sat_var;
	int time;
	FactPair fact;
	int priorityTime;

	sat_fact(FactPair p) : fact(p){}

	bool operator<(const sat_fact& a) const {
		// smaller time (i.e. earlier) receives higher priority and this is "greater" according to the order. 
		if (priorityTime > a.priorityTime) return true;
		if (priorityTime < a.priorityTime) return false;
		// tie breaking if times are equal.
		return fact < a.fact;
	}

};


extern "C" {

// functions provided by modified kissat 
void kissat_set_external_decision_function(unsigned (*function) (struct kissat *, int * ));
unsigned kissat_import_literal (kissat * solver, int elit);
int kissat_set_option (kissat * solver, const char *name, int new_value);
int kissat_get_truth_of_external_var(kissat * solver, int external_var);

// function we provide for modified kissat

// declarations to make the compiler happy.
void warn_var_removed(int var);
int get_sat_var_for_factpair(const FactPair & fact, int time);
int get_truth_of_fact_at_time(struct kissat * solver, const FactPair & fact, int time);
int get_truth_of_action_at_time(struct kissat * solver, int op, int time);
sat_fact get_sat_fact_for(struct kissat * solver, FactPair fact, int time, bool &isStaticallyTrue, bool &isStaticallyFalse);
int compute_priority_time_for_fact(struct kissat * solver, const FactPair & fact, const int & time);
bool rintanens_p_termination(std::unordered_set<int> &Z, int t, int bound);
void rintanens_p_cleanup(std::unordered_set<int> &Z, int t, int bound, int last);
std::unordered_set<int> rintanens_p_support(struct kissat * solver);
bool add_all_preconditions_of_action_to_queue(struct kissat * solver, std::priority_queue<sat_fact> & q, std::set<sat_fact> & inQueue, const std::vector<FactPair>  & conditions, int t);

};
#endif
