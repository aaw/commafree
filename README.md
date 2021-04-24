# commafree

Tools for generating, verifying, and extracting [commafree codes](https://en.wikipedia.org/wiki/Comma-free_code) with a fixed word size.

## Requirements

[Python3](https://www.python.org/downloads/) and a SAT solver (we use [kissat](https://github.com/arminbiere/kissat) in examples here but any other popular command-line SAT solver should work).

## Usage

First, use `commafree.py` to generate an input file that encodes the search
for a commafree code with word length _k_ over an alphabet of size _n_ that
is has size _m_ less than the maximum achievable code size.

For example, for _n_=4, _k_=4, it's known that the maximum possible size of
a commafree code is 57 even though the maximum achievable code
size is 60 (which is the number of [Lyndon words](https://en.wikipedia.org/wiki/Lyndon_word)
of length 4 over an alphabet of size 4).

To prove this fact, run `kissat` on the output of `commafree.py` to show
that there's no code of size 60 - 2 = 58:

```
$ kissat <(commafree.py 4 4 2)
...
s UNSATISFIABLE
...
```

But there is a commafree code of size 60 - 3 = 57:

```
$ kissat <(commafree.py 4 4 3)
...
s SATISFIABLE
...
```

To extract and verify the resulting code from a satisfiable result, use `extract-code.py`:

```
$ commafree.py 4 4 3 > commafree-4-4-3.cnf
$ kissat commafree-4-4-3.cnf > kissat-4-4-3.out
$ extract-code.py commafree-4-4-3.cnf kissat-4-4-3.out
{0010, 0020, 0030, 0110, 0113, 0120, 0121, 0123, 0130, 0131,
 0133, 0210, 0211, 0212, 0213, 0220, 0221, 0223, 0230, 0231,
 0233, 0310, 0313, 0320, 0330, 0333, 1110, 1113, 1120, 1121,
 1123, 1220, 1221, 1223, 2220, 2221, 2223, 3010, 3020, 3110,
 3113, 3120, 3121, 3123, 3210, 3211, 3212, 3213, 3220, 3221,
 3223, 3230, 3231, 3233, 3310, 3313, 3320}

size: 57
```

And to identify the equivalence classes that are missing from a satisfiable result, use `missing-codes.py`:

```
$ commafree.py 4 4 3 > commafree-4-4-3.cnf
$ kissat commafree-4-4-3.cnf > kissat-4-4-3.out
$ missing-codes.py 4 4 commafree-4-4-3.cnf kissat-4-4-3.out
Missing: [0102]
Missing: [0132]
Missing: [0232]
```