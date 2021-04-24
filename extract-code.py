#!/usr/bin/python3

# Extracts a commafree code from a CNF file created by commafree.py and
# the output of a SAT solver on that CNF file. Only works on satisfiable
# instances.
#
# Usage: extract-code.py <cnf-file> <sat-solver-output-file>

import re
import sys

def strip_cnf_mapping(filename):
    # lines look like 'c var 1 == 000001 chosen'
    mapping = {}
    pattern = re.compile('c var ([^\\s]+) == ([^\\s]+) chosen')
    with open(filename) as f:
        for line in f:
            if line.startswith('p'): continue
            if not line.startswith('c'): return mapping
            m = re.match(pattern, line)
            if m is None: continue
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
    if len(sys.argv) < 3:
        print('Usage: %s <cnf-file> <sat-solver-output-file>' % sys.argv[0])
        sys.exit(1)
    mapping = strip_cnf_mapping(sys.argv[1])
    solution = strip_sat_solution(sys.argv[2])
    code = [mapping[code_id] for code_id in solution
            if mapping.get(code_id) is not None]
    assert verify_commafree(code)
    print('{' + ', '.join(sorted(code)) + '}')
    print('')
    print('size: %s' % len(code))
