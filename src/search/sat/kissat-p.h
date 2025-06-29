#ifndef _kissatp_h_INCLUDED
#define _kissatp_h_INCLUDED


///#include "kissat.h"

extern "C" {
extern int var_removed_counter;
extern int final_stage_calls;

unsigned rintanens_p(struct kissat * solver, int * made_decision);

void setup_kissat_for_custom_heuristic(void* solver, bool useRintanensP, bool disableVARElimination);
}

#endif
