import puzzle
import argparse

parser = argparse.ArgumentParser(description="Software for Edge Matching puzzles à la Eternity II")
parser.add_argument('-i', '--input', help='Input file to read the puzzle pieces', required=True)
parser.add_argument('-o', '--output', help='Output file for the encoding', required=True)
parser.add_argument('-d', '--decode', help='To decode a solution', type=str, default=None)
parser.add_argument('-pv', '--piecevars', help='Output piece variables (for blocking multiple solutions)', type=bool, default=False)
parser.add_argument('-c', '--cardinality', help='Type of cardinality encoding for PySAT', type=int, default=1)
parser.add_argument('-b', '--borderonly', help='To specify that only the border will be considered', action='store_true')

args = parser.parse_args()

input_filename = args.input
decode_filename = args.decode
output_filename = args.output
cardinality_constraints_encoding = args.cardinality
only_border = args.borderonly
piece_vars = args.piecevars

p = puzzle.Puzzle.parse(input_filename)
p.encode(output_filename, piece_vars, cardinality_constraints_encoding, only_border)

if decode_filename is not None:
    p.decode(decode_filename)


