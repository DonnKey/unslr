/* #### Page 1 */
/* PORTIONS OF THIS PROGRAM HAVE BEEN BORROWED FROM THE SLR1 PARSER GENERATPR
   BY F. DEREMER, ordgnially written in XPL */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "type.h"
#include "utility.h"
#include "bitstring.h"
#include "nextitem.h"
#include "options.h"

#include "symbol.h"
#include "grammar.h"
#include "table.h"
#include "tableio.h"


FILE *mso;

void print_g();


/*
                        *******************************
                        *                             *
                        *           GRAMMARS          *
                        *                             *
                        *******************************

*/

char *v[MAX_NO_SYMS] = {""};

vocab_symbol no_terminals;      /*  NUMBER OF TERMINALS  */
vocab_symbol no_nts;            /*  NUMBER OF NON-TERMINALS  */
int largest_nt;                 /*  THE ABOVE PLUS SOME SLOP  */

vocab_symbol prod_array[MAX_NO_PROD_SYMBOLS];
production_symbols_ptr prod_array_ptr = 1;
production_symbols_ptr prod_start[MAX_NO_PRODS];
counter rhs_len[MAX_NO_PRODS];

production_ptr no_prods;                /*  NUMBER OF PRODUCTIONS  */
vocab_symbol goal_symbol;               /*  ELEMENT OF V CHOSEN FOR GOAL  */


set_of_states reduce_set[MAX_NO_PRODS]; /*  STATES CONTIAINING RX  */

/*
   INCONSISTENT RULE INFORMATION.  CONTAINS THE DATA FOR THE RULES WHICH
   WERE FOUND INCONSISTENT FOR THE FIRST NT FOUND TO BE INCONSISTENT
*/

boolean inaccessibles_found;

/*                   *********************************
                     *                               *
                     *       FIND INACCESSIBLES      *
                     *                               *
                     *********************************
*/
/* #### Page 2 */

#include "findallinacc.h"

void find_slr_inaccessibles()
{
   /*  THIS PROCEDURE COMPUTES THE SLR INACCESSIBLES.  IT WILL NOT WORK ON A
   FULL LR TABLE, BUT IS ADEQUATE FOR ALL BUT THE FIRST ITERATION OF THIS
   ALGORITHM.  FIND ALL INACCESSIBLES IS USED THE FIRST TIME  */

   set_of_syms follow;
   vocab_symbol sym;
   table_state state_no, goto_state;
   action action_t;
   rule_no prod;
   boolean changed;
   table_entry actn_entry;
   set_of_states lhs_ok;
   vocab_symbol lhs;

   /*  LHS OK IS THE SET OF LHSS WHICH HAVE THE RF OF ALL THEIR RHS"S UNCHANGED
   IN THE PREVIOUS ITERATION.  IT IS INITIALLY EMPTY, SET TO CONTIAN ALL, AHD
   AHS THOSE WHICH ARE CHANGED REMOVED  */;
   lhs_ok = NULLBITS;
   follow = NULLBITS;

   x_setempty(&lhs_ok);
   x_setempty(&lhs_used);

   inaccessibles_found = false;

   for (state_no = 0; state_no < MAX_NO_STATES; state_no++) {
      marks[state_no] = NULLBITS;
   }
   do {
      changed = false;
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (!x_test(lhs_ok, accessing_symbol[state_no]))
                x_setempty(&marks[state_no]);
      }
      for (prod = 1; prod <= no_prods; prod++) {
         actn_entry = action_pair(false, REDUCE, prod);
         lhs = prod_array[prod_start[prod]];
         /*  LOOK AT THE STATES IN SS(X)  */
         for (state_no = 0; state_no <= no_states; state_no++) {
            if (x_test(start_set[prod], state_no)) {
               x_set(&marks[state_no], lhs);
               x_set(&lhs_used, lhs);
               if (!x_test(lhs_ok, lhs)) {
                  goto_state = action_state(action_table(state_no, lhs));
                  follow = newbits(reduce_follow[prod]);
                  for (sym = 1; sym  <=no_terminals; sym++) {
                     if (stripped_action_table(goto_state, sym) == actn_entry)
                        x_reset(&follow, sym);
/* #### Page 3 */
                  }
                  x_or(&marks[goto_state],marks[goto_state], follow);
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
           for (sym = 1; sym <= last_nt; sym++) {
            action_t = action_type(action_table(state_no, sym));
            if (x_test(marks[state_no], sym)) {
               if (action_t == PHI || action_t == ESSENTIAL_ERROR)
                  action_table(state_no, sym) = error_entry;
            }
            else if (action_t != PHI) {
               if (control[sd]) printf("Inaccessible SLR (NT) entry %s at state %d and column %d was removed.\n",
               format_action(action_table(state_no, sym)), state_no, sym);
               inaccessibles_found = true;
               if (action_t == REDUCE) {
                  prod = action_rule(action_table(state_no, sym));
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
               if (action_type(action_table(state_no, sym)) == PHI)
                  action_table(state_no, sym) = error_entry;
            }
            for (sym = first_nt; sym <= last_nt; sym++) {
               if (!x_test(marks[state_no], sym)
                   && action_type(action_table(state_no, sym)) != PHI) {
                  if (control[sd]) printf("Inaccessible SLR (T) entry %s at state %d and column %d was removed.\n"
                  , format_action(action_table(state_no, sym)), state_no, sym);
                  action_table(state_no, sym) = phi_entry;
               }
            }
         }
      }
   } while (changed);

   freebits(&follow);
}

#include "compsets.h"
/* #### Page 4 */
void extract_grammar();

/*

                   *********************************
                   *                               *
                   *    TABLE EXPANSION UTILITY    *
                   *                               *
                   *********************************
*/
table_state new_row_number()
{
   no_states = no_states + 1;
   if (no_states > MAX_NO_STATES) {
      error("too many states, aborting", 3);
   }
   return no_states;
}


rule_no new_reduce_number(len, plh_set)
int len;
set_of_syms plh_set;
{

   no_prods = no_prods + 1;
   if (no_prods > MAX_NO_PRODS) {
      error("too many prods, aborting", 3);
   }
   rhs_len[no_prods] = len;
   plh[no_prods] = newbits(plh_set);
   return no_prods;
}

vocab_symbol create_new_nt()
{
   no_nts = no_nts + 1;
   if (last_nt > largest_nt) {
      error("too many non_terminals generated, aborting", 3);
   }
   return last_nt;
}


char *name_new_nt(numb, name)
char *name;
vocab_symbol numb;
{
   /*  NAME, IF PRESENT, SPECIFIES THE NEW NAME  */
   char *new_name;
   char buffer[10];

   sprintf(buffer,"<%d>",numb - no_terminals);
   new_name = newstring(buffer);
   if (strlen(name) != 0) {
/* #### Page 5 */
      v[numb] = name;
   }
   else {
      v[numb] = new_name;
   }
   return new_name;
}
/* $PA */
/*
                   *********************************
                   *                               *
                   *    FIND DIFFERENT REDUCES     *
                   *                               *
                   *********************************
*/

void find_different_reduces()
{
   /*  FIND WHETHER A GIVEN RX APPEARS IN ALL THE SAME COLUMNS IN ALL ITS ROWS,
   AND IF NOT CHANGE THE RUEDUCE NUMBERS  */
   rule_no prod, new_prod;
   table_state state_no;
   set_of_states rows;
   table_state model;   /*  THE MODEL OF A ROW CONTIAINING RX  */
   vocab_symbol sym;
   table_entry new_actn;
   table_entry actn, k;

   for (prod = 0; prod <= no_prods; prod++) {
      /*  FIND ALL THE ROWS PROD APPEARS IN, USE THE FIRST AS A MODEL  */
      actn = action_pair(false, REDUCE, prod);
      rows = newbits(reduce_set[prod]);
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (x_test(rows, state_no)) {
            model = state_no;
            x_reset(&rows, model);
            break;
         }
      }
      /*  FIND ROWS WHICH MATCH THE MODEL AND REMOVE FROM ROWS  */
      for (state_no = state_no; state_no <= no_states; state_no++) {
         if (x_test(rows, state_no)) {
               for (sym = 1; sym <= no_terminals; sym++) {
                  k = stripped_action_table(state_no, sym);
                  if (k != stripped_action_table(model, sym)
                      && (stripped_action_table(state_no, sym) == actn
                       || stripped_action_table(model, sym) == actn)) {
                     /*  WE HAVE A NO MATCH SITUATION, BAIL OUT WITHOUT
                     RESETTING FLAG  */
                     goto check_state_done;
                  }
               }
               /*  THIS MATCHES, REMOVE FROM SET  */;
               x_reset(&rows, state_no);
         check_state_done:;
/* #### Page 6 */
         }
      }
      /*  IF SOME ROWS WERE DIFFERENT, REPLACE THE REDUCES IN THEM. EACH
          DISTINCT GROUP SHOULD BE KEPT SEPARATE  */
      while (!x_empty(rows)) {
         new_prod = new_reduce_number(rhs_len[prod], plh[prod]);
         if (list_trace) printf("Rule %d has different follow sets, rule %d substituted.\n",
         prod, new_prod);
         new_actn = action_pair(false, REDUCE, new_prod);
         for (state_no = 0; state_no <= no_states; state_no++) {
            if (x_test(rows, state_no)) {
               model = state_no;
               x_reset(&rows, model);
               break;
            }
         }
         /*  REMOVE FROM SET ROWS ALL WHICH HAVE SAME REDUCES AS MODEL  */
         for (state_no = state_no; state_no <= no_states; state_no++) {
            if (x_test(rows, state_no)) {
                  for (sym = 1; sym <= no_terminals; sym++) {
                     if (stripped_action_table(state_no, sym) == actn) {
                        if (stripped_action_table(model, sym) != actn)
                           goto check_state_finished;
                     }
                     else {
                        if (stripped_action_table(model, sym) == actn)
                           goto check_state_finished;
                     }
                  }
                  /*  IT MATCHES THE MODEL, REMOVE FROM SET AND CHANGE ITS
                  REDUCE ACTION  */;
                  x_reset(&rows, state_no);
                  for (sym = 1; sym <= no_terminals; sym++) {
                     if (stripped_action_table(state_no, sym) == actn)
                        action_table(state_no,  sym)= new_actn;
                  }
               check_state_finished:;
            }
         }
         /*  WE SAVED THE MODEL TO LAST SO WE WOULD HAVE IT TO COMPARE WITH  */
         for (sym = 1; sym <= no_terminals; sym++) {
            if (stripped_action_table(model, sym) == actn)
               action_table(model, sym) = new_actn;
         }
      }
   }
   freebits(&rows);
}

/*
                   *********************************
                   *                               *
                   *    BUILD NEW NON-TERMINALS    *
                   *                               *
                   *********************************
*/
/* #### Page 7 */
void copy_row(from_row, to_row)
table_state from_row, to_row;
{
   /*  COPY FROM_ROW TO TO_ROW UNCHANGED  */

   vocab_symbol sym;
   production_ptr prod;
   table_entry k;

   for (sym = 1; sym <= last_nt; sym++) {
      action_table(to_row, sym) = stripped_action_table(from_row, sym);
   }
   accessing_symbol[to_row] = accessing_symbol[from_row];
   for (prod = 1; prod <= no_prods; prod++) {
      if (x_test(start_set[prod], from_row))
         x_set(&start_set[prod], to_row);
   }
}


#define PROD_SUB_MAX 5

table_entry tab_entry;
vocab_symbol col;
set_of_syms tested_cols;
set_of_syms follow_set;
split_index index_x, index_y, index_z;
set_of_syms rf_x;
set_of_states ss_x;
set_of_syms rf_y;
set_of_states ss_y;
rule_no old_rule_number[PROD_SUB_MAX];
rule_no new_rule_number[PROD_SUB_MAX];
int prod_sub_index;     /*  NUMBER USED IN REPLACE WITH...  */
set_of_rules subbed_for;        /*  RULES THAT WERE SUBBED BELOW  */
rule_no prod;

/* some of above possibly shouldn't be global */

   void clear_replace()
   {
      prod_sub_index = 0;
      x_setempty(&subbed_for);
   }


   void replace_with_new_prods(state_no)
   table_state state_no;
   {
      /*  REPLACES ALL REDUCES IN STATE_NO WITH NEW REDCUES  */

      vocab_symbol t_sym, t_sym1;
      set_of_syms tested;
      rule_no rule_x;
      int jj;
/* #### Page 8 */
      table_entry old_actn, new_actn;
      bitstring t_s1;

      tested = NULLBITS;
      x_setempty(&tested);
      for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
         old_actn = stripped_action_table(state_no, t_sym);
         t_s1 = NULLBITS;
         if (!x_test(tested, t_sym) && action_type(old_actn) == REDUCE) {
            rule_x = action_rule(old_actn);
            t_s1 = newbits(reduce_set[rule_x]);
            x_reset(&t_s1, state_no);
            if (!x_empty(t_s1)) {
               if (!x_test(subbed_for, rule_x)) {
                  prod_sub_index = prod_sub_index + 1;
                  old_rule_number[prod_sub_index] = rule_x;
                  new_rule_number[prod_sub_index] =
                     new_reduce_number(rhs_len[rule_x], plh[rule_x]);
                  x_set(&subbed_for, rule_x);
               }
               for (jj = 1; jj <= prod_sub_index; jj++) {
                  if (old_rule_number[jj] == rule_x) {
                     new_actn = action_pair(false, REDUCE, new_rule_number[jj]);
                     break;
                  }
               }
               for (t_sym1 = 1; t_sym1 <= no_terminals; t_sym1++) {
                  if (stripped_action_table(state_no, t_sym1) == old_actn) {
                     action_table(state_no, t_sym1) = new_actn;
                  }
               }
            }
            freebits(&t_s1);
            x_or(&tested,tested, reduce_follow[rule_x]);
         }
      }
      freebits(&tested);
   }


   void copy_chain(start_row, rule_x, pos, end_row)
   table_state start_row;
   rule_no rule_x;
   int pos;
   table_state *end_row;
   {
   /* PROCEDURE TO COPY A CHAIN OF SHIFTS ALONG A RULE STARTING
      AT STATE START ROW AND THE POS'TH SYMBOL OF THE RULE.
      (POS IS DEFINED IN TERMS OF A POSITION IN PROD ARRAY, NOT WITHIN THE RULE)
      OUTPUT END ROW CORRESPONDS TO THE LAST ROW COPIED, WHICH CONTAINS
      THE RX ENTRY.
      IT DOES NOTHING TO THE TABLE IF AT THE END OF A RULE
   */

      table_state old_row;
      table_state copied_row;
/* #### Page 9 */
      table_state next_row;
      vocab_symbol symb;

      old_row = *end_row = start_row;
      for (pos = pos; pos <= prod_start[rule_x] + rhs_len[rule_x]; pos++) {
         symb = prod_array[pos];
         next_row = action_state(action_table(old_row, symb));
         copied_row = new_row_number();
         action_table(old_row, symb) = action_pair(false, SHIFT, copied_row);
         copy_row(next_row, copied_row);
         old_row = copied_row;
      }
      *end_row = copied_row;
   }


   void forward_one_step(in_states, symb, out_states)
   set_of_states in_states;
   vocab_symbol symb;
   set_of_states *out_states;
   {
      /*  COMPUTE THE SYMB - SUCCESSOR OF IN_STATE  */

      table_state i;

      x_setempty(out_states);
      for (i = 0; i <= no_states; i++) {
         if (x_test(in_states, i) && action_type(action_table(i, symb))==SHIFT)
            x_set(out_states, action_state(action_table(i, symb)));
      }
   }


   void build_reduce_row(new_row, model, mask, new_prod, model_mask)
   table_state new_row, model;
   set_of_syms mask;
   rule_no new_prod;
   set_of_syms *model_mask;
   {
      /*  PUT NEW ENTRIES IN THE SPECIFIED ROW.  PUT A REDUCE WHERE MASK IS
      TRUE, COPY FROM THE MODEL OTHERWISE.  IF THERE IS NO MODEL, USE PHIS  */

      set_of_syms copy_mask;
      production_symbols_ptr j, jj;
      set_of_states set_p, set_q;
      table_state end_row;
      vocab_symbol sym;
      rule_no rule;
      boolean changed;
      vocab_symbol first_sym;
      table_entry k;

      set_p = NULLBITS;
      set_q = NULLBITS;
      copy_mask = NULLBITS;
/* #### Page 10 */
      for (sym = 1; sym <= no_terminals; sym++) {
         if (x_test(mask, sym)) {
            action_table(new_row, sym) = action_pair(false, REDUCE, new_prod);
         }
         else if (model != - 1) {
            action_table(new_row, sym) = stripped_action_table(model, sym);
         }
         else {
            action_table(new_row, sym) = phi_entry;
         }
      }
      *model_mask = newbits(mask);

      freebits(&copy_mask);
      copy_mask = newbits(mask);
      x_set(&copy_mask, no_terminals + 1);
      x_not(&copy_mask, copy_mask);

      for (sym = first_nt; sym <= last_nt; sym++) {
         action_table(new_row, sym) = phi_entry;
      }

      if (model != - 1 && !x_empty(in_start_set[model])) {
         /*  THERE ARE NON-T'S IN THE ROW (RARELY)  */
         do {
            changed = false;
            for (rule = 1; rule <= no_prods; rule++)  {
               if (x_test(in_start_set[model], rule)) {
                  first_sym = prod_array[prod_start[rule] + 1];
                  if ((x_test(*model_mask, first_sym) || rhs_len[rule] == 0)
                     && !x_test(*model_mask, prod_array[prod_start[rule]])
                     && (action_type(action_table(model, first_sym) == SHIFT /* N.B.: SHIFT==GOTO */
                       || (rhs_len[rule] == 0
                         && !x_empty_and(*model_mask, reduce_follow[rule]))))) {
                     x_set(model_mask, prod_array[prod_start[rule]]);
                     changed = true;
                  }
                  if ((x_test(copy_mask, first_sym) || rhs_len[rule] == 0)
                     && !x_test(copy_mask, prod_array[prod_start[rule]])
                     && (action_type(action_table(model, first_sym) == SHIFT
                       || (rhs_len[rule] == 0
                         && !x_empty_and(copy_mask, reduce_follow[rule]))))) {
                     x_set(&copy_mask, prod_array[prod_start[rule]]);
                     changed = true;
                  }
               }
            }
         } while (changed);
/* #### Page 11 */
         for (sym = first_nt; sym <= last_nt; sym++) {
            if (x_test(copy_mask, sym)) {
               clear_replace();
               action_table(new_row, sym) = stripped_action_table(model, sym);
               if (x_test(*model_mask, sym)) {
                  for (prod = 1; prod <= no_prods; prod++) {
                     for (j = 1; j <= rhs_len[prod]; j++) {
                        if ((prod_array[prod_start[prod] + j]) == sym) {
                           set_p = newbits(start_set[prod]);
                           for (jj = 1; jj <= j - 1; jj++) {
                              freebits(&set_q);
                              forward_one_step(set_p,
                                 prod_array[prod_start[prod] + jj], &set_q);
                              set_p = newbits(set_q);
                           }
                           if (x_test(set_p, model)) {
                              if (control[sd]) printf("Rule %d was split at symbol %s\n",
                              prod, v[sym]);
                              copy_chain(new_row, prod, j + prod_start[prod],
                                 &end_row);
                              replace_with_new_prods(end_row);
                              freebits(&set_p);
                              goto done_scan_prod;
                           }
                           freebits(&set_p);
                        }
                     }
                     done_scan_prod:;
                  }
               }
            }
         }
      }
      freebits(&copy_mask);
      freebits(&set_p);
      freebits(&set_q);
   }
   void remove_action_from_row(row, mask)
   table_state row;
   set_of_syms mask;
   {
      vocab_symbol sym;
      /*  SETS ALL POSITIONS NOT IN MASK TO PHI  */

      for (sym = 1; sym <= last_nt; sym++) {
         if (!x_test(mask, sym)) {
            action_table(row, sym) = phi_entry;
         }
      }
   }


   boolean in_equiv_class(model, to_test, mask)
   table_state model, to_test;
   set_of_syms mask;
/* #### Page 12 */
   {
      /*  IS TO_TEST IN THE SAME EQUIVALENCE CLASS AS MODEL, USING MASK  */
      table_entry i;
      vocab_symbol sym;

      for (sym = 1; sym <= last_nt; sym++) {
         if (!x_test(mask, sym)) {
            i = stripped_action_table(model, sym);
            if (i != stripped_action_table(to_test, sym)) {
               return false;
            }
         }
      }
      return true;
   }


   table_state find_equiv_model(possible, nt_sym, state_no)
   set_of_states possible;
   vocab_symbol nt_sym;
   table_state *state_no;
   {
      /*  FIND THE FIRST ENTRY IN POSSIBLE AS THE MODEL OF AN EQUIV CLASS  */

      for (*state_no = 0; *state_no <= no_states; (*state_no)++) {
         if (x_test(possible, *state_no)) {
            return action_state(action_table(*state_no, nt_sym));
         }
      }
      /* this will always find something and return */
   }


   void add_chain_rule(nont_a, rule_x)
   vocab_symbol nont_a;
   rule_no rule_x;
   {
      /*  THIS CORRESPONDS TO PART II-3 OF THE ALGORITHM  */

      rule_no rule_z;
      rule_no rule;
      table_state parent_state;
      set_of_states split_mask;
      table_state new_row_n;
      table_state equiv_class_model;
      vocab_symbol t_sym;
      table_state state_no, state_2;
      table_state goto_state;
      set_of_syms model_mask;   /*  FOR EQUIV_CLASS MODEL IF CAN"T ZAP YET  */
      set_of_syms kill_mask;    /*  THE COLS TO DROP FROM THE EQUIV CLASS  */
      table_entry k;    /*  TEMP  */
      vocab_symbol nont_b;
      bitstring t_s1;

      split_mask = NULLBITS;
      model_mask = NULLBITS;
/* #### Page 13 */
      kill_mask = NULLBITS;

      nont_b = create_new_nt();

      for (rule = 1; rule <= no_prods; rule++) {
         if (prod_start[rule] != 0 && prod_array[prod_start[rule]] == nont_a)
           x_set(&plh[rule], nont_b);
      }

      split_mask = newbits(start_set[rule_x]);

      t_s1 = NULLBITS;
      t_s1 = newbits(plh[rule_x]);
      x_set(&t_s1, nont_b);
      rule_z = new_reduce_number(1, t_s1);
      freebits(&t_s1);

      while (!x_empty(split_mask)) {
         x_setempty(&model_mask);
         new_row_n = new_row_number();
         equiv_class_model = find_equiv_model(split_mask, nont_a,&parent_state);
         build_reduce_row(new_row_n, equiv_class_model,
            reduce_follow[rule_x], rule_z, &kill_mask);

         if (x_test(split_mask, equiv_class_model)) {
            /*  IN CASE IT'S ITS OWN SUCCESSOR  */
            x_set(&split_mask, new_row_n);
         }

         /*  WE MUST NOT DO THE MODEL UNTIL LAST SO WE HAVE IT TO COMPARE
             AGAINST.  STATES BEFORE PARENT_STATE CANNOT BE MARKED  */
         for (state_no = parent_state; state_no <= no_states; state_no++) {
            if (state_no != equiv_class_model && x_test(split_mask, state_no)) {
               goto_state = action_state(action_table(state_no, nont_a));
               if (in_equiv_class(equiv_class_model, goto_state,
                     reduce_follow[rule_x])) {

                  if (goto_state != equiv_class_model) {
                     accessing_symbol[goto_state] = nont_b;
                     remove_action_from_row(goto_state, kill_mask);
                  }
                  else model_mask = newbits(kill_mask);

                  for (state_2 = state_no; state_2 <= no_states; state_2++) {
                     if (x_test(split_mask, state_2)
                        && action_state(action_table(state_2, nont_a)) == goto_state) {
                        x_reset(&split_mask, state_2);
                        action_table(state_2, nont_b)
                           = stripped_action_table(state_2, nont_a);
                        action_table(state_2, nont_a) =
                           action_pair(false, SHIFT, new_row_n);
                     }
                  }
               }
            }
         }
/* #### Page 14 */
         /*  NOW DO EQUIV CLASS MODEL  */;
         if (x_test(split_mask, equiv_class_model)) {
            goto_state = action_state(action_table(equiv_class_model, nont_a));
            if (equiv_class_model == goto_state) {
               x_reset(&split_mask, equiv_class_model);
               k = stripped_action_table(equiv_class_model, nont_a);
               action_table(equiv_class_model, nont_b) = k;
               action_table(equiv_class_model, nont_a)
                 = action_pair(false, SHIFT, new_row_n);
               if (action_type(k) == SHIFT)
                  accessing_symbol[action_state(k)] = nont_b;
               remove_action_from_row(goto_state, reduce_follow[rule_x]);
            }
         }
         accessing_symbol[new_row_n] = nont_a;
         if (!x_empty(model_mask)) {
            remove_action_from_row(equiv_class_model, model_mask);
            accessing_symbol[equiv_class_model] = nont_b;
         }
      }
      v[nont_a] = name_new_nt(nont_b, v[nont_a]);
      freebits(&split_mask);
      freebits(&model_mask);
      freebits(&kill_mask);
   }

   void split_by_start_set(rule_x, rule_y)
   rule_no rule_x, rule_y;
   {
      /*  THIS PROCEDURE CORRESPONDS TO PART III OF THE ALGORITHM  */

      table_state state;
      table_state j;
      table_entry old_actn, new_actn;
      vocab_symbol symb, t_sym, t_sym1;
      table_state state_no;
      set_of_states p_sub_i, p_sub_i_minus_1;
      set_of_states q_sub_i, q_sub_i_minus_1;
      int pos;
      table_state end_row;

      p_sub_i = NULLBITS;
      q_sub_i = NULLBITS;
      p_sub_i_minus_1 = NULLBITS;
      q_sub_i_minus_1 = NULLBITS;

      x_minus(&p_sub_i,start_set[rule_x], start_set[rule_y]);
      q_sub_i = newbits(start_set[rule_y]);
      /*  FIND WHERE THE TWO PATHS INTERSECT */;
      {
         for (pos = prod_start[rule_x] + 1;
            pos <= prod_start[rule_x] + rhs_len[rule_x]; pos++) {
            symb = prod_array[pos];
            freebits(&p_sub_i_minus_1);
            freebits(&q_sub_i_minus_1);
            p_sub_i_minus_1 =  p_sub_i;
/* #### Page 15 */
            q_sub_i_minus_1 = q_sub_i;
            p_sub_i = NULLBITS;
            q_sub_i = NULLBITS;
            forward_one_step(p_sub_i_minus_1, symb, &p_sub_i);
            forward_one_step(q_sub_i_minus_1, symb, &q_sub_i);
            if (!x_empty_and(q_sub_i, p_sub_i)){
                goto done_find_intersect;
            }
         }
         /*  THEY DON'T INTERSECT, THUS THERE ARE SEVERAL ROWS CONTAING A RX
         ACTION  */
         clear_replace();
         for (j = 0; j <= no_states; j++) {
            if (x_test(q_sub_i, j)) replace_with_new_prods(j);
         }
         return;
      }
      done_find_intersect:;

      /*  NOW SEPARATE THE PATHS (THERE MAY BE SEVERAL)  */;
      clear_replace();
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (x_test(p_sub_i_minus_1, state_no)) {
            old_actn = stripped_action_table(state_no, symb);
            copy_chain(state_no, rule_x, pos, &end_row);
            /*  CHANGE(ALL REDUCES (INCLUDING RX) TO NEW ACTIONS IN THE NEW
            END ROW  */;
            replace_with_new_prods(end_row);
            new_actn = stripped_action_table(state_no, symb);
            for (j = state_no + 1; j <= no_states; j++) {
               if (x_test(p_sub_i_minus_1, j)
                  && stripped_action_table(j, symb) == old_actn) {
                  action_table(j, symb) = new_actn;
                  x_reset(&p_sub_i_minus_1, j);
               }
            }
         }
      }
      freebits(&p_sub_i);
      freebits(&q_sub_i);
      freebits(&p_sub_i_minus_1);
      freebits(&q_sub_i_minus_1);
   }


   void split_by_follow_set(rule_x, rule_y)
   rule_no rule_x, rule_y;
   {
      /*  BOTH STEP I-5B2D AND PART OF STEP II-1 ARE HERE  */

      set_of_syms intersection_mask;
      table_entry actn_entry;
      table_entry new_reduce_action;
      rule_no rule_z;
      vocab_symbol symbol;
      table_state state_no;
/* #### Page 16 */
      intersection_mask = NULLBITS;
      x_minus(&intersection_mask,reduce_follow[rule_x], reduce_follow[rule_y]);

      actn_entry = action_pair(false, REDUCE, rule_x);  /*  THE TARGET  */
      rule_z = new_reduce_number(rhs_len[rule_x], plh[rule_x]);
      new_reduce_action = action_pair(false, REDUCE, rule_z);
      state_no = 0;
      symbol = 0;
      while (1) {
         find_action(actn_entry, &state_no, &symbol);
         if (state_no < 0) break;
         if (x_test(intersection_mask, symbol))
            action_table(state_no, symbol) = new_reduce_action;
         symbol = symbol + 1;
      }
      x_minus(&reduce_follow[rule_x],reduce_follow[rule_x], intersection_mask);
      reduce_follow[rule_z] = newbits(intersection_mask);
      freebits(&intersection_mask);
   }

void build_new_nts()
{
   table_state state_no, state_to_split;
   split_index i;
   rule_no rule_y;

   /*  MAIN BODY OF BUILD_NEW_NTS STARTS HERE; CORRESPONDS TO STEP I-5B  */
   index_x = 0;
   index_y = - 1;
   ss_x = newbits(split_ss[index_x]);
   rf_x = newbits(split_rf[index_x]);

   /* find_incomparable_sets */
   for (i = 1; i <= split_count; i++) {
      if (split_rule[i] != 0) {

         if (! (x_empty_and(rf_x, split_rf[i])
                || x_empty_and(ss_x, split_ss[i]))) {
            ss_y = newbits(split_ss[i]);
            rf_y = newbits(split_rf[i]);
            index_y = i;
            break;
         }
      }
   }

   if (index_y != - 1) {
      /*  "HARD" CASE -- COMPLEX SPLIT  */

      /*
      THE CODE BELOW IS AN EMBODYMENT OF THIS DECISION TABLE:

                         FOLLOW SET
                  X=Y  X>>Y  X<<Y  X INC Y  X DIS Y
      S   X=Y      D"    D'   D       E"      A"
/* #### Page 17 */ /*
      T   X>>Y     D'    D'   C       E'      A"
      A   X<<Y     D     E    D       E       A"
      R   X INC Y  C"    E'   C       E"      A"
      T   X DIS Y  B"    B"   B"      B"      B"

      ' INDICATES SWAP X AND Y
      " INDICATES ROLES OF X AND Y IRRELEVENT
      CASE D WAS ELIMINATED IN FIND_LEFT_PART.
      CASES A AND B WERE ELIMINATED IMMEDIATELY ABOVE -- IF THERE
          IS A NON-DISJOINT RULE, IT WILL BE Y.
      GIVEN THESE ELIMINATIONS WE CAN CONCLUDE:

      X-Y EMPTY  Y-X EMPTY
          T          T          X = Y
          F          T          X >> Y
          T          F          X << Y
          F          F          X INCOMP Y
      IN THE TABLE THE TEST IS ACTUALLY FOR NON EMPTY.

      WE MAY ACTUALLY FIND CASES C AND E.
      WE ALSO NEED TO IDENTIFY THE CASES WHERE X AND Y ARE TO BE SWAPPED.

      WE CONVERT THE BIT CODES TO NUMBERS  (COMBINED) AND USE A TABLE
      LOOKUP.
      THE BIT CODE ONLY REFERS TO THE FIRST 4 ROWS AND COLUMNS OF THE TABLE.
      CASE 1 IS D (IGNORED)
      CASE 2 IS E
      CASE 3 IS C.
      A VALUE OF 100 ADDED MEANS SWAP X AND Y.
*/
   static char mode_table[16] =
        {1,   1,   1,   2,
         1,   1,   3, 102,
         1,   2,   1,   2,
         3, 102,   3,   2};

      i = 0;
      if (!x_empty_minus(rf_x, rf_y))  i = i + 1;
      if (!x_empty_minus(rf_y, rf_x))  i = i + 2;
      if (!x_empty_minus(ss_x, ss_y))  i = i + 4;
      if (!x_empty_minus(ss_y, ss_x))  i = i + 8;

      if (control[d1]) printf("Mode position selected %d\n", i);
      i = mode_table[i];
      if (i > 100) {
         i = i - 100;
         index_z = index_y;
         index_y = index_x;
         index_x = index_z;
      }

      switch (i) {
      case 0: /*  NO OP (O IS UNDEFINED)  */;
         break;

      case 1: /*  NO OP (1 IS NOT TRULY POSSIBLE)  */;
/* #### Page 18 */
         break;

      case 2: /*  CASE E  */;
            if (control[sd]) printf("A follow set split was used on rules %d and %d for non-terminal %s\n",
            split_rule[index_x], split_rule[index_y], v[nt_to_split]);
            split_by_follow_set(split_rule[index_x], split_rule[index_y]);
            if (!x_empty_minus(rf_y, rf_x)) {
               if (control[sd]) printf("A follow set split was used on rules %d and %d for non-terminal %s\n",
               split_rule[index_y], split_rule[index_x], v[nt_to_split]);
               split_by_follow_set(split_rule[index_y], split_rule[index_x]);
            }
            break;

       case 3: /*  CASE C  */
            if (control[sd]) printf("A start_set split was used on rules %d and %d for non-terminal %s\n",
            split_rule[index_x], split_rule[index_y], v[nt_to_split]);
            split_by_start_set(split_rule[index_x], split_rule[index_y]);
            if (!x_empty_minus(ss_y, ss_x)) {
               if (control[sd]) printf("A start_set split was used on rules %d and %d for non-terminal %s\n",
               split_rule[index_y], split_rule[index_x], v[nt_to_split]);
               split_by_start_set(split_rule[index_y], split_rule[index_x]);
            }
            break;
      }
   }
   else {
      /*  "EASY" CASE (D)  */
      /*  THIS IS STEP II-1; LOOK FOR ILLEAGL SPLITS  */
      /*  FIRST LOOK FOR REDUCE FOLLOW SETS THAT WILL BE CLOBBERED  */
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (x_test(ss_x, state_no)) {
            state_to_split = action_state(action_table(state_no, nt_to_split));
            x_setempty(&tested_cols);
            for (col = 1; col <= no_terminals; col++) {
               if (!x_test(tested_cols, col)) {
                  tab_entry = stripped_action_table(state_to_split, col);
                  if (action_type(tab_entry) == REDUCE) {
                     rule_y = action_rule(tab_entry);
                     follow_set = newbits(reduce_follow[rule_y]);
                     if (!x_empty_and(rf_x, follow_set)
                      && !x_empty_minus(follow_set, rf_x)) {
                        if (control[sd]) printf("Rule %d was split by follow set.\n", rule_y);
                        split_by_follow_set(rule_y, split_rule[index_x]);
                     }
                     x_or(&tested_cols,tested_cols, follow_set);
                     freebits(&follow_set);
                  }
               }
            }
         }
      }
      /*  NOW LOOK FOR START SETS THAT WILL BE MANGLED  */
      for (prod = 0; prod <= no_prods; prod++) {
         if (prod_array[prod_start[prod] + 1] == nt_to_split
            && !x_empty_minus(start_set[prod], ss_x)
            && !x_empty_and(start_set[prod], ss_x)) {
/* #### Page 19 */
            if (control[sd]) printf("Rule %d was split by start set.\n", prod);
            split_by_start_set(prod, split_rule[index_x]);
            /*  THE  START SET COULD HAVE CHANGED,MAKE SURE SS_X IS UP TO
            SPEED.  */;
            ss_x = newbits(start_set[split_rule[index_x]]);
         }
      }
      if (control[sd]) printf("Non terminal %s was left split by rule %d.\n",
         v[nt_to_split], split_rule[index_x]);
      add_chain_rule(nt_to_split, split_rule[index_x]);
   }
}


void initialize()
{
   int rule_x;

   phi_entry = action_pair(false, PHI, 0);
   error_entry = action_pair(false, ESSENTIAL_ERROR, 0);
   for (rule_x = 1; rule_x <= MAX_NO_PRODS; rule_x++) {
      rhs_len[rule_x] = unspec_len;
      x_setempty(&plh[rule_x]);
   }
   mso = fopen("unslr.out","w");
}

/*
             **********************************
             *                                *
             *             MAIN               *
             *                                *
             **********************************
*/
main (argc,argv)
int argc;
char **argv;
{
        set_control(argc, argv);

        initialize();
        read_table();
        validate_table();

        if (error_count > 0 && !control[ie]) exit(1);

        if (control[lf]) echo_table();
        list_trace = control[lf] && control[lt];

        extract_grammar();
        find_all_inaccessibles();
        find_goal();
        check_lhs_use();
        if (control[ap]) {
           echo_table();
           print_g(true, false);
/* #### Page 20 */
        }
        list_trace = control[lt];
        find_different_reduces();
        if (!control[go]) do {
           subsets_found = false;
           inaccessibles_found = false;
           /*  THINGS ARE DONE IN_THE ORDER BELOW SO THAT THE PUNCHED VERSION HAS A
           GOOD LHS, BUT THE PRINTING OF THE TRACE COMES AFTER A COPY OF THE TABLE  */
           if (control[it]) echo_table();
           extract_grammar();
           if (control[pi]) punch_table();
           find_slr_inaccessibles();
           check_lhs_use();
           find_goal();
           if (control[ig] || control[pg]) print_g(control[ig], control[pg]);
           if (!inaccessibles_found && subsets_found) build_new_nts();
           if (error_count > 0) break;
        } while (inaccessibles_found || subsets_found);

        if ((control[fg] && !control[ig])
           ||(control[pf] && !control[pg]))
           print_g(control[fg] && !control[ig], control[pf] && !control[pg]);
        if (control[pt] && !control[pi]) punch_table();
        if (control[ft] && !control[ig]) echo_table();
        if (control[ea]) eject_page;
        return 0;
}
