/* #### Page 1 */
#include "type.h"
#include "utility.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"

/*
               ******************************
               *                            *
               *         COMPUTE SETS       *
               *                            *
               ******************************
*/

void validate_table()
{
   /*  MAKES SURE TABLE IS CORRECT (INCOMPLETE TEST)  */
   table_state i;

   for (i = 1; i <= no_states; i++) {
      if (accessing_symbol[i] == 0) {
         sprintf(printbuffer, "state %d is inaccessible.", i);
         error(printbuffer, i);
      }
   }
}


void find_goal()
{
   /*  FIND THE GOAL SYMBOL  */
   table_state i;
   vocab_symbol j;

   i = j = 0;
   find_action(action_pair(false, ACCEPT_STATE, 0), &i, &j);
   if (i < 0) {
      error("no accept state found", 1);
      return;
   }
   goal_symbol = accessing_symbol[i];
}

void compute_goto_set(nt_sym)
vocab_symbol nt_sym;
{
   /*  COMPUTE THE CONVENTIONAL GOTO SET  */

   table_state state_no;
   table_entry tab_entry;
   action table_action;
   set_of_states gt_set = NULLBITS;

   x_setempty(&gt_set);
   for (state_no = 0; state_no <= no_states; state_no++) {
/* #### Page 2 */
      tab_entry = stripped_action_table(state_no, nt_sym);
      table_action = action_type(tab_entry);
      if (table_action == GOTO) {
         x_set(&gt_set, state_no);           /* HAND NOTE */
      }
   }
   goto_set[nt_sym] = gt_set;
   gt_set = NULLBITS;  /* don't free; we saved it */
}

boolean compute_lgtf(ss, nt_sym, lgtf)
vocab_symbol nt_sym;
set_of_states ss;
set_of_syms *lgtf;
{
   /*  COMPUTE LIMITED GOTO FOLLOW FOR A GIVEN START SET  */

   table_state j;
   vocab_symbol k;
   action actn;
   table_state goto_state;
   boolean found;

   found = false;
   x_setempty(lgtf);
   for (j = 0; j <= no_states; j++) {
      if (x_test(ss, j)) {
         goto_state = stripped_action_table(j, nt_sym);
         if (action_type(goto_state) == SHIFT) {
            goto_state = action_state(goto_state);
            found = true;
            for (k = 1; k <= no_terminals; k++) {
               actn = action_type(action_table(goto_state, k));
               if (actn != PHI) x_set(lgtf, k);
            }
         }
      }
   }
   return found;
}

boolean find_reduces(rule_x, p, rf)
rule_no rule_x;
set_of_states *p;
set_of_syms *rf;
{
   /*  THIS PROCEDURE FINDS P(RULE_X,1) AND RF(RULE_X). IF NO OCCURRENCES OF
   RED ARE FOUND IT RETURNS FALSE  */

   boolean found;
   table_entry actn_entry;
   vocab_symbol symbol;
   table_state state_no;

   actn_entry = action_pair(false, REDUCE, rule_x);     /*  THE TARGET  */
/* #### Page 3 */
   state_no = 0;
   x_setempty(rf);
   x_setempty(p);
   found = false;
   symbol = 0;
   while (forever) {
      find_action(actn_entry, &state_no, &symbol);
      if (state_no < 0) break;
      x_set(p, state_no);
      x_set(rf, symbol);
      found = true;

      symbol = symbol + 1;
   }
   return found;
}
