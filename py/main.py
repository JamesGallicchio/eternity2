import puzzle
import argparse

parser = argparse.ArgumentParser(description="Software for Edge Matching puzzles à la Eternity II")
parser.add_argument('-i', '--input', help='Input file to read the puzzle pieces', required=True)
parser.add_argument('-d', '--decode', help='To decode a solution', type=str, default=None)

args = parser.parse_args()

input_filename = args.input
decode_filename = args.decode

p = puzzle.Puzzle.parse(input_filename)


p.encode('test.cnf')
if decode_filename is not None:
    p.decode(decode_filename)


