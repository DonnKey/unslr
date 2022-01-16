# unslr
SLR1 table expansion starting from a table for an ambiguous grammar
with conflicts resolved
and resulting with a table (and grammar) for the corresponding unambiguous
grammar.

See Also: cmptab (next to this repository on GitHub).  This README is the primary
documentation for both programs.

Unslr is one of a pair to compress and expand SLR(1) (and some LR(1)) 
grammars along with their corresponding tables. Unslr expands tables and grammars,
cmptab compresses out redundancies while still retaining a sense of the grammar.

The tables can be considered something like a "Fourrier Transform" of the 
grammar -- another way to look at the same information, and thus manipulate 
that information more easily for certain tasks.

This interacts strongly with ambiguous grammars: the compressed tables 
correspond to ambiguous grammars for which ambiguity resolution information has 
been applied to the corresponding table.

Table expansion of tables with ambiguity resolution recovers an unambiguous 
grammar for that particular ambiguity resolution. The grammars so recovered are 
often ones that would take a great deal of thought to arrive at in terms of 
manipulating the grammar: as an example, it finds a nice grammar for the C ?: 
operator such that only expressions which would be "ambiguous" to the casual 
reader of such a statement are required to be parenthesised.

### History

The source code is a translation to K&R C of the original XPL/S sources (from 1978),
with some additions/changes made in 1988-1989. (The translation was made in 1979-81.)
The C source was recovered via OCR (gImageReader) and hand edited to correct OCR errors until it
compiled correctly using gcc/90 in the "standard C" configuration.
A visual inspection for confusing standalone 'i' with '1' and 'l' was done, but
some similar errors might remain.

The C source was mostly mechanically translated from the XPL/S source, and
continues to bear a strong resemblence to the original. (Some indentation also 
reflects the original code.)
XPL/S supported labeled blocks (as in Perl and modern C++) that could be
(in modern terms) used with the break and continue statements.
The use of goto in the C source is a translation of
the XPL/S EXIT and CONTINUE statements (equivalent to break and continue): the
block label in XPL/S is translated to the target of the goto.
(All gotos are thus either forward branches to just below the bottom of a loop
or backward branches to the beginning of a loop.)

XPL/S assumed programs were a single file, and supported nested procedures.
The C version is more C-like in that regard; many procedures are in separate
files, and nested procedures (and the associated scoping) are simulated by
using file-scope variables.

Some XPL/S code was found unnecessary in the original translation 
(thanks to C libraries), and XPL/S allowed functions on the left, which is
translated using #define.  The original code (in C-ish syntax) was retained
as commentary.

Some subsequent edits were required to make it run correctly, specifically
some standard headers were included, a test added where the code was assuming that
(as on historical early C machines) *0 == 0 (and was not an error), and some
handwritten notes were flagged.  After further analysis, those notes have been applied (or not);
the GIT history has a change just for that purpose.
Minor fixes to the punch-grammar function, introduced in the C translation,
were made as well.

### Input

The input format consists of white-space separated strings.
Each line has a specific meaning.  Lines ending with '\$' are assumed
to be continued on the next input line.  (Be careful if you use '\$' as
a grammar symbol, particularly as the end of input.)
(This usage is due to the assumption that fixed-length records are involved.)
If a token begins with '<', it may contain embedded spaces until the '>'
is reached.

The first line is two integers giving the number of states and the number of productions in the grammar.
The second line is the terminal vocabulary (the actual symbols to be parsed),
with the last being the 'end of input' distinguished symbol.
The third line is the non-terminal vocabularly, usually consisting of strings
like \<E> or \<expression>.

The subsequent lines are the table itself: the first entry on each line is
the row number, starting from zero.  (The row number is not strictly necessary, but it
makes editing the tables much easier.)
The subsequent symbols on the line are the table actions. They can be one of:

| Entry | Meaning |
| ----- | ---------------------------------------------------------------------|
|  rnn  | Reduce nn: the end of rule nn. |
|  smm  | Shift to state mm. |
|  e    | Essential error (parser must error if it sees this) |
|  a    | Accept: exactly one, indicating the final state |
|  -    | Phi: unreachable (or input syntax error for terminals) |

The phi (-) entries in the non-terminal columns are required up to the rightmost entry for that row, but may
be omitted to the right of the last non-terminal shift (traditionally "goto" for non-terminals) entry (if any).
(For many rows there will be no entries in the non-terminal columns.)

The next (last) line is optional depending on the command line option "il" (input length): 
if present it gives the length and left hand side (LHS) of each rule (pairs of numbers and symbols).
(Most, but not all, tables contain sufficient redundancy that the lengths are not
needed, but certain cases need the length.)  (When punching the tables, the length and LHS
are always emitted.)

## Reference
The algoritghms used are discussed in detail in:

||
| ------------ |
| Ambiguity and LR Parsing |
| Donn Scott Terry |
Department of Computer Science (now Allen School of Computer Science)
Technical Report No. 78-11-02
University of Washington

## Building
This Git repo along with the standard C libraries and a compatible compiler
is all it takes to build this program.  CMake selects c89 gcc, which is fine.

## Running
The program runs as a utility program, accepting an input file describing the
table and emitting a pretty-printed copy of the table, the recovered grammar,
and the decisions used to compress the table, iteratively until the table 
comes to represent an unambiguous grammar.  (That is determined by certain internal consistency
measures in the table.)  It takes command line options as two-letter
codes (no hyphen), and always reads from stdin and writes to stdout. The
option codes and meanings are found in options.h.

In a modern environment "punching" (the table) means writing to ./unslr.out.

A sample input program is in test/test_input, and launch.json is set up
to read it and "print" to build/test_output.

The run time is very short for reasonable tables (sub-second).
### Current State

The table compresion (cmptab) and expansion (unslr, this Git repo) is running,
apparently correctly - but there may be remaining issues. The code may
have whitespace differences from the original, and a few corrections
(visible in the Git history) have been applied for compatibility with
the current C standard.  Minor bugfixes (mentioned above) was also
applied.  There are comments in the source indicating the beginning of
each page of the paper document to facilitate comparison.

The algorithms rely heavily on a set-of-bits type, which is a bit clumsy
to use in C. That code has been rewritten to make it clearer (it was the
source of a number of portability problems) and in somewhat newer C. (In
particular, using function prototypes properly.)

Note that this program and cmptab share a number of file names, particularly
bitstring.c/.h. Those are intended to be identical in the two versions, so 
please fix any bugs in both versions.  (In a couple of cases the files differ
slightly in obvious ways.)

The PDF scans have not been uploaded (yet?).

### Testing
Both this program and cmptab have a few simple tests that can be run using
launch.json and the VS Code debugger tools.

In addtion there is the "81 grammars" test.  Consider the tiny grammar:
```
   <E> ::= <E> + <E>  
         | <E> * <E>   
         | ( <E>)      
         | a            
```

Ambiguities in a grammar yield shift/reduce conflicts in the parser table.
There are four locations in the table corresponding to this grammar with shift/reduce conflicts.
The ambiguity is resolved by chosing a shift (keep parsing/right associative/lower precedence),
reduce (accept input/left associative/higher precedence)
or error (disallow that associativity/precedence) for that cell.
Each of those tables has a corresponding grammar.

The perl script 81gram.pl will generate the table for each of those 3^4 (81) grammars,
run unslr on it, and then run cmptab on the resulting table, set to remove redundant rules only.
(Grammars are numbered 0-80.)  

The total runtime on my machine is about one second -- when I first did this it was 1/2 hour counting print time.

I compared the result generated with this version with a paper listing saved over many years:
the results were the same as the paper listing.
Most of the resulting grammars are quite strange, but it (as it should) does find the 
usual precedence/associativity grammer (case 37) and "must be fully parenthesised" (case 80).
Case 37 is one of quite a few where the cmptab cleanup stage yields a better (smaller) grammar
by eliminating redundant rules or unnecessary trivial chain rules. (See also cases 31 and 66
for other examples of compression - there are many others.)
(Case 31 is also the grammar for inverted precedence: + binds more strongly.)

The result used above is in the Git repo as test/81gram.reference for comparison purposes.

Notes:

Cases 21 and 55: On the paper listing both of these fail with what appears to be an out of range
subscript, meaning a runaway loop.  Case 55 is much shorter than 21. There is probably a housekeeping bug in
the XPL version (runs with 81 successes were made, but no copies exist).

In this version, these run a bit longer with a cleaner (but still very incorrect) termination.

The original (RBM on a Sigma 5) script used to also run the SLR1 parser generator on the grammar to confirm 
whether the language was SLR(1), LR(0), or something else. That program has not been ported (yet?)

Test/test_inputNN are speicifc cases of the 81 grammars.

## If you are interested in serious use.

I would recommend converting the current source into at least modern C,
and preferably into a more modern (and easier to work with) language.
(I personally would choose a language with operator overloading for the bitset type.)
Doing that would probably expose any remaining translation bugs. 
The original XPL/S code was written "thinking" in a more modern language
(e.g. the use of functions on the left/operator overloading) so this would be fairly natural.
