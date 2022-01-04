/* #### Page 1 */
#include "type.h"
#include "utility.h"
#include "options.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"
#include "tableio.h"
#include "compsets.h"

/*                   *********************************
                     *                               *
                     *       FIND INACCESSIBLES      *
                     *                               *
                     *********************************
*/

void find_all_inaccessibles()
{
   /*  THIS PROCEDURE COMPUTES THE FULL LR PHI-INACCESSIBILITY FOR THE TABLE  */
   set_of_syms f = NULLBITS;
   set_of_states p = NULLBITS, p_plus_1 = NULLBITS;
   vocab_symbol sym, t_sym;
   table_state state_no, s, goto_state;
   action action_t;
   int i;       /*  POSITION IN A RHS  */
   rule_no prod;
   boolean changed;
   table_entry actn_entry;
   set_of_syms lhs_ok = NULLBITS;
   vocab_symbol lhs;

   x_setempty(&lhs_ok);
   x_setempty(&lhs_used);
   x_setempty(&p);
   x_setempty(&p_plus_1);

   do {

      changed = false;

      for (state_no = 0; state_no <= no_states; state_no++) {
         if (!x_test(lhs_ok, accessing_symbol[state_no]))
             x_setempty(&marks[state_no]);
      }

      for (prod = 1; prod <= no_prods; prod++) {
         lhs = prod_array[prod_start[prod]];

         for (state_no = 0; state_no <= no_states; state_no++) {
            /*  IF THE STATE CONTAINS A RX ENTRY THEN COMPUTE P  */

            if (x_test(reduce_set[prod], state_no)) {
               actn_entry = action_pair(false, REDUCE, prod);

               x_setempty(&f);
/* #### Page 2 */
               for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                  if (stripped_action_table(state_no, t_sym) == actn_entry)
                      x_set(&f, t_sym);
               }

               if (!x_empty(f)) {
                  x_setempty(&p);
                  x_set(&p, state_no);
                  i = rhs_len[prod];
                  while (i > 0) {
                     x_setempty(&p_plus_1);
                     sym = prod_array[prod_start[prod] + i];
                     for (s = 0; s <= no_states; s++) {
                        actn_entry = stripped_action_table(s, sym);
                        if (action_type(actn_entry) == SHIFT &&
                            x_test(p, action_state(actn_entry)))
                              x_set(&p_plus_1, s);
                     }
                     freebits(&p);
                     p = p_plus_1;
                     p_plus_1 = NULLBITS;
                     i = i - 1;
                  }

                  /*  WE HAVE THE PSEUDO START SET  */
                  for (s = 0; s <= no_states; s++) {
                     if (x_test(p, s)) {
                        x_set(&marks[s], lhs);
                        x_set(&lhs_used, lhs);
                        if (!x_test(lhs_ok, lhs)) {
                           /*  IT WOULD BE NICE TO BE ABLE TO DO THIS TEST
                           SOONER BUT WE MUST HAVE P TO MARK ALL COLUMNS EVEN
                           THOUGH WE NEED TO MARK ONLY SELECTED ROWS IN A
                           SECOND PASS  */
                           goto_state = action_state(stripped_action_table(s, lhs));
                           actn_entry = action_pair(false, REDUCE, prod);
                           for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                              if (stripped_action_table(goto_state, t_sym) != actn_entry
                                 && x_test(f, t_sym))
                                    x_set(&marks[goto_state], t_sym);
                           }
                        }
                     }
                  }
               }
            }
         }
      }

      for (sym = 0; sym <= last_nt; sym++) {
         x_set(&lhs_ok, sym);
      }

      /*  APPLY THE MARKS  */
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (accessing_symbol[state_no] >= first_nt) {
/* #### Page 3 */
                                                 /* HAND NOTE s */

            for (sym = 1; sym <= last_nt ;sym++) {
               action_t = action_type( stripped_action_table(state_no, sym ));
               if (x_test(marks[state_no], sym)) {
                  if (action_t == PHI || action_t == ESSENTIAL_ERROR)
                     action_table(state_no, sym) = error_entry;
               }
               else if (action_t != PHI) {
                  if (control[sd]) {
                     printf("Inaccessible_LR (NT) entry %s at state %d and column %d was removed.\n",
                     format_action( stripped_action_table(state_no,sym)), state_no, sym);
                  }
                  if (action_t == REDUCE) {
                     prod = action_rule(stripped_action_table(state_no, sym));
                     x_reset(&reduce_follow[prod], sym);
                     changed = true;
                     /*  WE HAVE ZAPPED A REDUCE ENTRY, TRY AGAIN  */
                     x_reset(&lhs_ok, prod_array[prod_start[prod]]);
                  }
                  action_table(state_no, sym) = phi_entry;
               }
            }
         }
         else if (accessing_symbol[state_no] != 0 || state_no == 0) {
            for (sym = 1; sym <= no_terminals; sym++) {
               if (action_type(stripped_action_table(state_no, sym)) == PHI)
                  action_table(state_no, sym) = error_entry;
            }
            for (sym = first_nt; sym <= last_nt; sym++) {
               if (!x_test(marks[state_no], sym)
                  && action_type(action_table(state_no, sym)) != PHI) {
                  if (control[sd]) printf("Inaccessible LR (T) entry %s at state %d and column %d was removed.\n",
                  format_action(action_table(state_no, sym)), state_no, sym);
                  action_table(state_no, sym) = phi_entry;
               }
            }
         }
      }
   } while (changed);
   freebits(&p);
   freebits(&f);
   freebits(&lhs_ok);
}

void check_lhs_use()
{
   /*  CHECKS TO SEE IF THE LHS IS USED  */
   table_state state_no;
   vocab_symbol sym, t_sym;
   boolean state_removed;
   table_entry actn;

   state_removed = false;
   for (sym = first_nt; sym <= last_nt; sym++) {
      if (!x_test(lhs_used, sym)) {
         if (list_trace)
            printf("Symbol %s is never on the left and thus removed.\n", v[sym]);
/* #### Page 4 */
         for (state_no = 0; state_no <= no_states; state_no++) {
            action_table(state_no, sym) = phi_entry;
            if (accessing_symbol[state_no] == sym) {
               if (list_trace) printf("State %d was removed.\n",state_no);
               state_removed = true;
               accessing_symbol[state_no] = 0;

               for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                  action_table(state_no, t_sym) = phi_entry;
               }
            }
         }
      }
   }
   while (state_removed) {
      state_removed = false;
      x_setempty(&states_used);
      for (state_no = 0; state_no <= no_states; state_no++) {
         for (sym = 1; sym <= last_nt; sym++) {
            actn = stripped_action_table(state_no, sym);
            if (action_type(actn) == SHIFT)
               x_set(&states_used, action_state(actn));
         }
      }

      for (state_no = 0; state_no <= no_states; state_no++) {
         if (!x_test(states_used, state_no)
             && accessing_symbol[state_no] != 0) {
            if (list_trace)
               printf("State %d became inaccessible\n", state_no);
            state_removed = true;
            accessing_symbol[state_no] = 0;
            for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
               action_table(state_no, t_sym) = phi_entry;
            }
         }
      }
   }
}
