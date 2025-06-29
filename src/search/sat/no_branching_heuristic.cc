#include "kissat-p.h"



extern "C" {

int var_removed_counter = 0;
int final_stage_calls = 0;

// nothing to do if we don't use kissat with the special code that allows for custom heuristics
void setup_kissat_for_custom_heuristic(__attribute__((unused)) void* solver, __attribute__((unused)) bool useRintanensP, __attribute__((unused)) bool disableVARElimination){}

unsigned rintanens_p(__attribute__((unused)) struct kissat * solver, __attribute__((unused)) int * made_decision){
	return 0;
}

};

