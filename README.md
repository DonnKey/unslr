# unslr
SLR1 table expansion with starting from a table for an ambiguous grammar
with conflicts resolved
and resulting with a table (and grammar) for the corresponding unambiguous
grammar.

See Also: cmptab (next to this repository on GitHub).

This program is one of a pair to compress and expand SLR(1) (and some LR(1)) 
grammars along with their corresponding tables.

The tables can be considered something like a "Fourrier Transform" of the 
grammar -- another way to look at the same information, and thus manipulate 
that information more easily for certain tasks.

This interacts strongly with ambiguous grammars: the compressed tables 
correspond to ambiguous grammars for which ambiguity resolution information has 
been applied to the table.

Table expansion of tables with ambiguity resolution recovers an unambiguous 
grammar for that particular ambiguity resolution. The grammars so recovered are 
often ones that would take a great deal of thought to arrive at in terms of 
manipulating the grammar: as an example it finds a nice grammar for the C ?: 
operator such that only expressions which would be "ambiguous" to the casual 
reader of such a statement are required to be parenthesised.

The source code is a translation to K&R C of the original XPL/S sources (from 1978),
with some additions/changes made in 1988-1989. (The translation was made in 1979-81.)
The C source was recovered via OCR (gImageReader) and hand edited to correct OCR errors until it
compiled correctly using gcc/90 in the "standard C" configuration.
A visual inspection for confusing standalone 'i' with '1' and 'l' was done, but
some similar errors might remain.

The C source was mostly mechanically translated from the XPL/S source, and
continues to bear a strong resemblence to the original. 
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
handwritten notes were flagged.  After further analysys, those notes have been applied (or not);
the GIT history has a change just for that purpose.
Minor fixes to the punch-grammar function, introduced in the C translation,
were made as well.

The input format consists of white-space separated strings.
Each line has a specific meaning.  Lines ending with '$' are assumed
to be continued on the next input line.  (Be careful if you use '$' as
a grammar symbol, particularly as the end of input.)
(This due to the assumption that fixed-length records are involved.)
If a token begins with '<', it may contain embedded spaces until the '>'
is reached.
The first line is two integers giving the number of states and the number of productions in the grammar.
The second line is the terminal vocabulary (the actual symbols to be parsed),
with the last being the 'end of input' distinguished symbol.
The third line is the non-terminal vocabularly, usually consisting of strings
line <E> or <expression>.
The subsequent lines are the table itself: the first entry on each line is
the row number, starting from zero.  (This is not strictly necessary, but it
makes editing the tables much easier.)
The subsequent symbols on the line are the table actions. They can be one of:

| Entry | Meaning |
| ----- | ---------------------------------------------------------------------|
|  rnn  | reduce nn: the end of rule nn. |
|  smm  | shift to state mm. |
|  e    | essential error (parser must error if it sees this) |
|  a    | accept: exactly one, indicating the final state |
|  -    | phi: unreachable (or input syntax error for terminals) |

The phi (-) entries in the non-terminal columns are required, but may
be omitted to the right of the last non-terminal entry.  (For many rows
there will be no entries in the non-terminal columns.)


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
cannot be compressed any further.  It takes command line options as two-letter
codes (no hyphen), and always reads from stdin and writes to stdout. The
option codes and meanings are found in options.h.

In a modern environment "punching" (the table) means writing to ./unslr.out.

A sample input program is in test/test_input, and launch.json is set up
to read it and "print" to build/test_output.

The run time is very short for reasonable tables (sub-second).
### Current State

The table expansion (unslr, this Git repo) is running,
apparently correctly - but there may be remaining issues. The code may
have whitespace differences from the original, and a few corrections
(visible in the Git history) have been applied for compatibility with
the current C standard.  Minor bugfixes (mentioned above) was also
applied.  There are comments in the source indicating the beginning of
each page of the paper document to facilitate comparison.

The PDF scans have not been uploaded yet.

### If you are interested in serious use.

I would recommend converting the current source into at least modern C,
and preferably into a more modern (and easier to work with) language.
(C++ or Java seen good candidates.) 
Doing that would probably expose any remaining translation bugs. 
The original XPL/S code was written "thinking" in a more modern language
(e.g. the use of functions on the left) so this would be fairly natural.
