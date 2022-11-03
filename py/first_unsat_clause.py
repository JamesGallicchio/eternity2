import sys
import puzzle

puzzlefile = sys.argv[1]
formula = sys.argv[2]

def build_assignment(filename):
    p = puzzle.Puzzle.parse(filename)
    p.encode('test.cnf')
    n, m = p.dims
    assignment = []
    for i in range(n):
        for j in range(m):
            piece = p.pieces[i*n+j]
            if not piece.is_center():
                assignment.append(p.V[((i, j), piece)])
            else:
                assignment.append(p.V[((i, j), piece, 0)])
    for d_pos in p.diamonds_pos:
        p1, p2 = d_pos
        print(f'p1 = {p1}, p2 = {p2}')
        piece1 = p.pieces[p1[0]*n + p1[1]]
        piece2 = p.pieces[p2[0]*n + p2[1]]
           
        if p2[0] == p1[0] + 1:
            assert piece1.color_seq[2] == piece2.color_seq[0]
            assignment.append(p.V[(d_pos, piece1.color_seq[2])])
        else:
            assert piece1.color_seq[1] == piece2.color_seq[3]
            assignment.append(p.V[(d_pos, piece1.color_seq[1])])
    for idx in range(1, len(p.V)+1):
        if idx not in assignment:
            assignment.append(-idx)
    return assignment

        

assignment = build_assignment(puzzlefile)

def sats(assignment, clause):
    for lit in clause:
        if lit in assignment:
            return True
    return False

with open(formula, 'r') as f:
    first_line = f.readline()
    for line in f:
        print(line)
        clause = list(map(int, line.split(' ')[:-1]))
        if not sats(assignment, clause):
            print('CLAUSE NOT SATISFIED!!')
            break
