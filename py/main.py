import puzzle
import argparse
import os
import subprocess
from os import getcwd
from shlex import quote
from pysat.formula import CNF

def sh(command):
    return subprocess.run(command,cwd=getcwd(), universal_newlines=True, capture_output=True)
    

parser = argparse.ArgumentParser(description="Software for Edge Matching puzzles à la Eternity II")
parser.add_argument('-i', '--input', help='Input file to read the puzzle pieces', required=True)
parser.add_argument('-o', '--output', help='Output file for the encoding', required=True)
parser.add_argument('-d', '--decode', help='To decode a solution', type=str, default=None)
parser.add_argument('-pv', '--piecevars', help='Output piece variables (for blocking multiple solutions)', type=bool, default=False)
parser.add_argument('-c', '--cardinality', help='Type of cardinality encoding for PySAT', type=int, default=1)
parser.add_argument('-b', '--borderonly', help='To specify that only the border will be considered', action='store_true')
parser.add_argument('--count', help='For counting solutions', action='store_true')


args = parser.parse_args()

input_filename = args.input
decode_filename = args.decode
output_filename = args.output
cardinality_constraints_encoding = args.cardinality
only_border = args.borderonly
piece_vars = args.piecevars
count = args.count

p = puzzle.Puzzle.parse(input_filename)
p.encode(output_filename, piece_vars, cardinality_constraints_encoding, only_border)

if decode_filename is not None:
    p.decode(decode_filename)

def get_sol_from_output(output):
    lines = list(filter(lambda l: len(l), output.split('\n')))
    sol_lines = list(filter(lambda l: l[0] == 'v', lines))
    lits = []
    for sol_line in sol_lines:
        lits_line = sol_line.split(' ')[1:]
        lits.extend(list(map(int, lits_line)))
    return lits[:-1]


if count:
    cnt = 0
    cnf = CNF(from_file=output_filename)
    cnf.to_file(output_filename + '0')
    while True:
        print(f'FINDING SOLUTON #{cnt+1}')
        return_call = sh(['yalsat', output_filename + str(cnt)])
        if return_call.returncode != 10:
            break
        sol = get_sol_from_output(return_call.stdout)
        cnt += 1
        blocked = []
        for lit in sol:
            if lit > 0 and lit in p.IV:
                blocked.append(lit)
        clauses = cnf.clauses
        clauses.append([-1*b for b in blocked])
        cnf = CNF(from_clauses=clauses)
        os.remove(output_filename + str(cnt-1)) # remove previous one
        cnf.to_file(output_filename + str(cnt))
