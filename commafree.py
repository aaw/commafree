#!/usr/bin/python3

# Usage: python3 commafree.py k n m
#
# Generates clauses that are satisfiable exactly when there exists a set of
# commafree codewords of size MAXCF(k,n) - m on words of length k using an
# alphabet of size n. MAXCF(k,n) is the maximum possible size of such a set,
# equal to the number of Lyndon words (also called "prime strings" by Knuth)
# of length k over an alphabet of size n. There's a closed-form formula for
# MAXCF(k,n) that involves the mobius function [1].
#
# A set of strings is commafree if no concatenation of any two strings in
# the set contains another string in the set as a substring that overlaps
# both. So if '100' and '212' are in the set, '002' and '021' (and '121'
# and '210') can't be in the set. Here's an example commafree code with
# words of length 3 over the alphabet {0,1,2} that achieves the maximum
# possible size:
#
#   {100, 101, 102, 200, 201, 202, 211, 212}
#
# If k is odd, the resulting clauses are satisfiable for any n >= 2 and
# n > m >= 0 due to results by Eastman [2].
#
# If k is even, not much is known beyond small values of k and n. Here's a
# sample of what's known:
#
# (k,n,m)  | SAT/UNSAT?
# ---------------------
# (2,2,0)  | SAT
# (2,4,0)  | UNSAT
# (2,4,1)  | SAT
# (4,3,0)  | SAT
# (4,4,0)  | UNSAT
# (4,4,3)  | SAT
# ...
# (10,2,0) | SAT
# (12,2,0) | UNSAT
# (12,2,1) | SAT
#
# [1] Golumb, S. W., B. Gordon, and L. R. Welch, Comma-free codes, Can. J.
#     Math, vol. 10, 1958, pp 202-209.
# [2] Eastman, W. L., On the Construction of Comma-Free Codes, IEEE Trans.
#     IT-11 (1965), pp 263-267.

import argparse
from collections import defaultdict
import copy
import io
import itertools
import math
import tempfile
import sys

# Global variable counter.
vc = 0
def new_var(): global vc; vc += 1; return vc
def num_vars(): global vc; return vc

def ensure_vars(nv): global vc; vc = nv

# Global clause counter.
cc = 0
def write_clause(f, c):
    global cc
    f.write((" ".join(["{}"] * len(c)) + " 0\n").format(*c))
    cc += 1
def num_clauses(): global cc; return cc

# Generates all Lyndon words of length k over alphabet of size n. A Lyndon word
# is a string that is strictly lexicographically smaller than all of its
# rotations. Comma-free codes can only contain Lyndon words and their rotations.
# This method is essentially Knuth's Algorithm 7.2.1.1 F from The Art of
# Computer Programming, Volume 4A. Knuth calls these "prime strings".
def primes(k, n):
    a = [-1] + [0]*k
    j = 1
    while True:
        if j == k:
            yield tuple(a[1:])
        j = k
        while a[j] == n-1:
            j -= 1
        if j == 0: return
        a[j] += 1
        for i in range(j+1, k+1):
            a[i] = a[i-j]

# Generates all rotations of a string.
# rotations((1,2,3)) == ((1,2,3),(2,3,1),(3,1,2))
def rotations(t):
    for i in range(len(t)):
        yield t[i:]+t[:i]

# Given variables a, b, minout, and maxout, generates clauses that are
# satisfiable iff minout = min(a,b) and maxout = max(a,b).
def comparator(a, b, minout, maxout):
    return [(-maxout, a, b), (-a, maxout), (-b, maxout),
            (minout, -a, -b), (a, -minout), (b, -minout)]

# Given variables vin, returns a permutation of the values in vin such that if
# the d smallest elements of vin appear as the last d elements of vin in
# decreasing order, the d+1 smallest elements of vin appear as the last d+1
# elements of vout in decreasing order. This is essentially one round of
# bubblesort with the smallest elements appearing at the end of the output list.
def merge(cf, vin, offset):
    vout = vin[:]
    minout = vin[0]
    for i in range(1, len(vin)-offset):
        newmin, newmax = new_var(), new_var()
        for clause in comparator(minout, vin[i], newmin, newmax):
            write_clause(cf, clause)
        vout[i-1], vout[i] = newmax, newmin
        minout = newmin
    return vout

# Generates a variable for each non-cyclic string of length n over an alphabet
# of size m. Stores them in a map from string -> var so that we can add comments
# about the association of codewords to variables later. Also generates
# representative variables for each equivalence class of prime strings (under
# rotation) that asserts "something from this class is chosen". Returns the
# map of string -> var and the list of representative vars.
def make_vars(cf, k, n):
    var = {}
    reps = {}
    for p in primes(k, n):
        rotvars = []
        for r in rotations(p):
            nv = new_var()
            var[r] = nv
            rotvars.append(nv)

        # Create a representative var and add clauses that assert "this string
        # or one of its rotations is chosen".
        nv = new_var()
        reps[p] = nv
        # Ensure that nv is false if none of rotvars is true.
        write_clause(cf, [-nv] + rotvars)
    return (var, reps)

# Comma-free codes can't contain three strings x,y,z such that y is a substring
# of the concatentation xz but not a prefix or suffix of xz. This function
# returns a naive encoding of these constraints consisting of ternary clauses
# for every such (x,y,z).
def commafree_property_naive(cf, k, var):
    for x, x_id in var.items():
        for y, y_id in var.items():
            for i in range(1,k):
                z = tuple(x[i:]+y[:i])
                z_id = var.get(z)
                if z_id is None: continue
                write_clause(cf, (-x_id, -y_id, -z_id))

# Returns True exactly when tuple s has prefix t.
def tstarts_with(s, t):
    for i, n in enumerate(t):
        if s[i] != n: return False
    return True

assert(tstarts_with((1,2,3,4),(1,)))
assert(tstarts_with((1,2,3,4),(1,2)))
assert(tstarts_with((1,2,3,4),(1,2,3)))
assert(tstarts_with((1,2,3,4),(1,2,3,4)))
assert(not(tstarts_with((1,2,3,4),(1,3))))

# Returns True exactly when tuple s has suffix t.
def tends_with(s, t):
    for i, n in enumerate(t):
        if s[-len(t)+i] != n: return False
    return True

assert(tends_with((1,2,3,4),(4,)))
assert(tends_with((1,2,3,4),(3,4)))
assert(tends_with((1,2,3,4),(2,3,4)))
assert(tends_with((1,2,3,4),(1,2,3,4)))
assert(not(tends_with((1,2,3,4),(1,3))))

# If x and y don't overlap, returns None. Otherwise, for all strings abc where
# ab = x and bc = y, returns the pair (a,c). Results are returned as a list,
# arguments are passed as tuples but interpreted as strings.
def diff(x,y):
    def intersects(x,y,i):
        for j in range(len(x)-i):
            if x[j+i] != y[j]: return False
        return True

    for i in range(1,len(y)):
        if not intersects(x,y,i): continue
        yield (x[:i],y[len(x)-i:])

assert(list(diff((1,2,3),(4,5,6))) == [])
assert(list(diff((1,2,3),(2,1,3))) == [])
assert(list(diff((1,2,3),(3,2,1))) == [((1,2),(2,1))])
assert(list(diff((1,2,3),(2,3,1))) == [((1,),(1,))])
assert(list(diff((1,2,3),(1,2,3))) == [])
assert(list(diff((2,2,2,2),(2,2,2,2))) ==
       [((2,), (2,)), ((2,2), (2,2)), ((2,2,2),(2,2,2))])

# Comma-free codes can't contain three strings x,y,z such that y is a substring
# of the concatentation of xz but not a prefix or suffix of xz. In contrast to
# commafree_property_naive, this function compresses the encoding of this
# constraint with bounded variable addition (BVA).
def commafree_property_bva(cf, k, n, var):
    # Precompute two tables of some intersections of var.keys() with var.keys().
    # If x = ab and y = bc for some non-empty string b, then ri[c] contains
    # (x_id, y_id) and li[a] contains (x_id, y_id).
    ri = defaultdict(list)
    li = defaultdict(list)
    for x, x_id in var.items():
        for y, y_id in var.items():
            for pre, suf in diff(x,y):
                if len(suf) <= k // 2: ri[suf].append((x_id, y_id))
                if len(pre) <= k // 2: li[pre].append((x_id, y_id))

    for i in range(1, k // 2):
        for core in itertools.product(range(n), repeat=i):
            v = new_var()
            for x, x_id in var.items():
                if not tstarts_with(x, core): continue
                write_clause(cf, (-v, -x_id))
            for x_id, y_id in ri[core]:
                write_clause(cf, (v, -x_id, -y_id))

            v = new_var()
            for x, x_id in var.items():
                if not tends_with(x, core): continue
                write_clause(cf, (-v, -x_id))
            for x_id, y_id in li[core]:
                write_clause(cf, (v, -x_id, -y_id))

    for core in itertools.product(range(n), repeat = k // 2):
        v = new_var()
        for x, x_id in var.items():
            if not tstarts_with(x, core): continue
            write_clause(cf, (-v, -x_id))
        for x_id, y_id in ri[core]:
            write_clause(cf, (v, -x_id, -y_id))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description= 'Generate a DIMACS CNF file for a commafree code.')
    parser.add_argument('k', type=int, help='codeword length')
    parser.add_argument('n', type=int, help='alphabet size')
    parser.add_argument('m', type=int,
                        help='number of codewords away from optimal')
    parser.add_argument('--compress', action='store_true',
                        help='use BVA to compress commafree property')
    parser.add_argument('--no-compress', dest='compress', action='store_false')
    parser.set_defaults(compress=True)
    args = parser.parse_args()

    assert (args.k > 1), "k must be greater than 1"
    assert (args.n > 1), "n must be greater than 1"
    assert (args.m >= 0), "m must be non-negative"

    with tempfile.TemporaryFile(mode='w+t') as cf:
        # Generate variables for all possible codewords and equivalence classes.
        var, reps = make_vars(cf, args.k, args.n)
        vout = [x for x in reps.values()]
        assert (args.m < len(vout)), \
            "impossible value of m=%s: only %s prime strings" % \
            (args.m, len(vout))

        # Cut search space in half by excluding half of the rotations from
        # one class. Example: with n=6, exclude: 10000, 010000, 001000
        for i in range(args.k // 2):
            t = [0] * args.k
            t[i] = 1
            write_clause(cf, (-var[tuple(t)],))

        # Don't allow any three strings (x,y,z) in the final set of codewords
        # if y is a substring of the concatenation of x and z.
        if args.compress:
            commafree_property_bva(cf, args.k, args.n, var)
        else:
            commafree_property_naive(cf, args.k, var)

        # Finally, we need to make an assertion about the size of the set of
        # codewords. When we created variables for each prime string and all of
        # its rotations, we also created variables that represent 'some member
        # of this equivalence class was chosen' for each prime string's
        # equivalence class. We run d+1 rounds of bubblesort over these
        # representatives now, after which the d smallest values should be false
        # and the (d+1)st smallest value should be true if we're exactly d away
        # from the maximum possible code size.
        if len(vout) > 1:
            for i in range(args.m+1):
                vout = merge(cf, vout, i)
            if args.m > 0:
                write_clause(cf, [-vout[-args.m]])
            write_clause(cf, [vout[-1-args.m]])

        # Write the final DIMACS file. We've cached clauses in a temp file until
        # now, so we'll rewind and write those out to stdout as a final step.
        sys.stdout.write(
            "c Generated by commafree.py {0}\n".format(' '.join(sys.argv[1:])))
        sys.stdout.write(
            "c Generator source: github.com/aaw/commafree/commafree.py\n")
        for k,v in sorted(reps.items(), key=lambda x: x[1]):
            sys.stdout.write('c var %s == class [%s] used\n' %
                             (v, ''.join(str(x) for x in k)))
        for k,v in sorted(var.items(), key=lambda x: x[1]):
            sys.stdout.write('c var %s == %s chosen\n' %
                             (v, ''.join(str(x) for x in k)))
        sys.stdout.write('p cnf {0} {1}\n'.format(num_vars(), num_clauses()))
        cf.seek(0)
        for line in cf:
            sys.stdout.write(line)
        sys.stdout.write('\n')
