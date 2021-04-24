#!/usr/bin/python3

# Extracts the equivalence classes missing from a commafree code with word
# length m over an alphabet of size n that does not achieve the maximum
# theoretical size from a CNF file created by commafree.py and the output
# of a SAT solver on that CNF file. Only works on satisfiable instances.
#
# Usage: missing-codes.py n m <cnf file> <sat-solver-output-file>

import re
import sys

def primes(n, m):
    a = [-1] + [0]*n
    j = 1
    while True:
        if j == n:
            yield tuple(a[1:])
        j = n
        while a[j] == m-1:
            j -= 1
        if j == 0: return
        a[j] += 1
        for i in range(j+1, n+1):
            a[i] = a[i-j]

def rotations(t):
    for i in range(len(t)):
        yield t[i:]+t[:i]

def make_prime_map(n,m):
    fmap = {}
    rmap = {}
    for i, p in enumerate(p for p in primes(n,m)):
        rmap[i] = ''.join(str(x) for x in p)
        for r in rotations(p):
            fmap[''.join(str(x) for x in r)] = i
    return fmap, rmap

def strip_cnf_mapping(filename):
    # lines look like 'c var 1 == 000001 chosen'
    mapping = {}
    pattern = re.compile('c var ([^\\s]+) == ([^\\s]+) chosen')
    with open(filename) as f:
        for line in f:
            if not line.startswith('c'): return mapping
            m = re.match(pattern, line)
            if m is None:
                continue
            mapping[int(m.groups()[0])] = m.groups()[1]
    return mapping

def strip_sat_solution(filename):
    pos = []
    with open(filename) as f:
        for line in f:
            if not line.startswith('v'): continue
            pos += [int(x) for x in line[1:].strip().split(' ') if int(x) > 0]
    return pos

def verify_commafree(codewords):
    n = len(codewords[0])
    cws = set(c for c in codewords)
    for x in codewords:
        for y in codewords:
            for i in range(1,n):
                cw = x[i:]+y[:i]
                if cw in cws:
                    print("CONFLICT: %s, %s, and %s." % (x,y,cw))
                    return False
    return True

if __name__ == '__main__':
    if len(sys.argv) < 5:
        print('Usage: %s n m <cnf file> <sat-solver-output-file>'\
              % sys.argv[0])
        sys.exit(1)
    n = int(sys.argv[1])
    m = int(sys.argv[2])
    mapping = strip_cnf_mapping(sys.argv[3])
    solution = strip_sat_solution(sys.argv[4])
    code = [mapping[code_id] for code_id in solution
            if mapping.get(code_id) is not None]
    verify_commafree(code)
    pm, rpm = make_prime_map(n,m)
    ids = set(pm.values())
    for c in code:
        ids.remove(pm[c])
    for x in ids:
        print('Missing: [%s]' % rpm[x])
