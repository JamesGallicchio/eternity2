from pysat.formula import CNF
from pysat.card import *
import matplotlib.pyplot as plt


side = 5

class Puzzle:
    def __init__(self, pieces, dims):
        self.pieces = pieces
        self.corner_pieces = list(filter(lambda x: x.is_corner(), self.pieces))
        self.border_pieces = list(filter(lambda x: x.is_border(), self.pieces))
        self.center_pieces = list(filter(lambda x: x.is_center(), self.pieces))
        self.colors = count_colors(self.pieces)
        self.dims = dims
        self.V = {}
        n, m = dims
        self.center_pos = []
        self.corner_pos = []
        self.border_pos = []
        for i in range(n):
            for j in range(m):
                li = (n-1-i) % (n-1)
                lj = (m-1-j) % (m-1)
                if li == 0 and lj == 0:
                    self.corner_pos.append((i, j))
                elif li == 0 or lj == 0:
                    self.border_pos.append((i, j))
                else:
                    self.center_pos.append((i, j))
        self.positions = self.center_pos + self.corner_pos + self.border_pos

    def encode(self, filename='out.cnf'):
        self.clauses = []
        self.create_rotational_piece_variables()
        self.clauses.extend(self.eop_clauses())

        self.create_diamond_variables()
        self.clauses.extend(self.alocd_clauses())

        self.clauses.extend(self.connection_rotational_clauses())

        self.clauses.extend(self.guided_search(5))

        cnf = CNF(from_clauses=self.clauses)
        cnf.to_file(filename)

    def decode(self, solution_filename):
        fig = plt.figure()
        lits = []
        positive_set = set()
        with open(solution_filename, 'r') as f:
            for line in f:
                tokens = line[2:-1].split(' ')
                lits.extend(list(map(int, tokens)))

        for i in lits:
            if i > 0: positive_set.add(i)

        for pos in self.corner_pos:
            for piece in self.corner_pieces:
                if self.V[(pos, piece)] in positive_set:
                    print(f'CORNER: at pos {pos} goes piece = {piece.color_seq}')
                    triangles = piece_to_triangles(piece, pos)
                    for t in triangles:
                        plt.gca().add_patch(t)

        for pos in self.border_pos:
            for piece in self.border_pieces:
                if self.V[(pos, piece)] in positive_set:
                    print(f'BORDER: at pos {pos} goes piece = {piece.color_seq}')
                    triangles = piece_to_triangles(piece, pos)
                    for t in triangles:
                        plt.gca().add_patch(t)

        for pos in self.center_pos:
            for piece in self.center_pieces:
                for rot in range(4):
                    if self.V[(pos, piece, rot)] in positive_set:
                        print(f'at pos = {pos} goes piece = {piece.color_seq} with rotation = {rot}')
                        triangles = piece_to_triangles(piece, pos, rot)
                        for t in triangles:
                            plt.gca().add_patch(t)

        for pos in self.diamonds_pos:
            for color in range(1, self.colors):
                if self.V[(pos, color)] in positive_set:
                    print(f'CENTER: diamond pos = {pos}, color = {color}')

        n, m = self.dims
        plt.xlim([0, side*m])
        plt.ylim([0, side*n])

        plt.show()

    def create_rotational_piece_variables(self):
        for pos in self.corner_pos:
            for piece in self.corner_pieces:
                self.V[(pos, piece)] = len(self.V) + 1
        for pos in self.border_pos:
            for piece in self.border_pieces:
                self.V[(pos, piece)] = len(self.V) + 1
        for pos in self.center_pos:
            for piece in self.center_pieces:
                for rot in range(4):
                    self.V[(pos, piece, rot)] = len(self.V) + 1

    def create_diamond_variables(self):
        n, m = self.dims
        # diamond-color variables
        # a diamond is specified by two piece positions
        vdirs = [(0, 1), (1, 0)]
        self.diamonds_pos = []
        t_id = CNF(from_clauses=self.clauses).nv
        cnt = 1
        for i in range(n):
            for j in range(m):
                for vdir in vdirs:
                    di, dj = vdir
                    ni, nj = i+di, j+dj
                    if ni < n and nj < m:
                        diamond_pos = ((i, j), (ni, nj))
                        self.diamonds_pos.append(diamond_pos)
                        for color in range(1, self.colors+1):
                            self.V[(diamond_pos, color)] = t_id+cnt
                            cnt += 1

    # each piece needs to be in exactly one position
    def eop_clauses(self):
        ans = []
        # note: it is crucial that these long clauses go first, so that way the top-id correctly matches len(self.V)
        for pos in self.corner_pos:
            ans.append([self.V[(pos, piece)] for piece in self.corner_pieces])
        for pos in self.border_pos:
            ans.append([self.V[(pos, piece)] for piece in self.border_pieces])
        for pos in self.center_pos:
            ans.append([self.V[(pos, piece, rot)] for piece in self.center_pieces for rot in range(4)])
        # cardinality constraints 
        for piece in self.corner_pieces:
            t_id = CNF(from_clauses=self.clauses+ans).nv
            card_clauses = CardEnc.equals(lits=[self.V[(pos, piece)] for pos in self.corner_pos], top_id=t_id, encoding=1)
            ans.extend(card_clauses.clauses)
        for piece in self.border_pieces:
            t_id = CNF(from_clauses=self.clauses+ans).nv
            card_clauses = CardEnc.equals(lits=[self.V[(pos, piece)] for pos in self.border_pos], top_id=t_id, encoding=1)
            ans.extend(card_clauses.clauses)
        for piece in self.center_pieces:
            t_id =  CNF(from_clauses=self.clauses+ans).nv
            card_clauses = CardEnc.equals(lits=[self.V[(pos, piece, rot)] for pos in self.center_pos for rot in range(4)], top_id=t_id, encoding = 1)
            ans.extend(card_clauses.clauses)
        return ans

    # enforce at least one color per diamond.
    def alocd_clauses(self):
        ans = []
        for pos in self.diamonds_pos:
            ans.append([self.V[(pos, color)] for color in range(1, self.colors+1)])
        return ans

    def connection_rotational_clauses(self):
        ans = []
        for pos in self.diamonds_pos:
            p_one, p_two = pos
            for color in range(1, self.colors+1):
                if p_two[0] == p_one[0] + 1: # vertical diamond
                    p_set = self.get_pieces_by_color_mask(['_', '_', str(color), '_'], p_one)
                    p_set_2 = self.get_pieces_by_color_mask([str(color), '_', '_', '_'], p_two)
                else: # horizontal diamond
                    p_set = self.get_pieces_by_color_mask(['_', str(color), '_', '_'], p_one)
                    p_set_2 = self.get_pieces_by_color_mask(['_', '_', '_', str(color)], p_two)
                
                clause_one, clause_two = [], []
                for piece_rot in p_set:
                    piece, rot = piece_rot
                    if not piece.is_center():
                        clause_one.append(self.V[(p_one, piece)])
                    else:
                        clause_one.append(self.V[(p_one, piece, rot)])
                
                for piece_rot in p_set_2:
                    piece, rot = piece_rot
                    if not piece.is_center():
                        clause_two.append(self.V[(p_two, piece)])
                    else:
                        clause_two.append(self.V[(p_two, piece, rot)])
                ans.append([-self.V[(pos, color)]] + clause_one)
                ans.append([-self.V[(pos, color)]] + clause_two)
        return ans

    def guided_search(self, guide_limit):
        ans = []
        n, m = self.dims
        for i in range(guide_limit):
            for j in range(guide_limit):
                piece = self.pieces[i*n+j]
                if piece.is_center():
                    ans.append([self.V[((i, j), piece, 0)]])
                else:
                    ans.append([self.V[((i, j), piece)]])
        return ans

    def get_pieces_by_color_mask(self, mask, pos):
        i, j = pos
        n, m = self.dims
        if i == 0:
            mask[0] = '0'
        if j == 0:
            mask[3] = '0'
        if i == n-1:
            mask[2] = '0'
        if j == m-1:
            mask[1] = '0'
        ans = []
        for piece in self.pieces:
            rotation =  piece.match(mask)
            if rotation != -1: ans.append((piece, rotation))
        return ans

    @staticmethod
    def parse(filename):
        pieces = []
        with open(filename, 'r') as f:
            first_line_tokens = f.readline()[:-1].split(' ')
            dims = list(map(int, first_line_tokens))
            for line in f:
                pieces.append(Piece.parse(line[:-1]))

        return Puzzle(pieces, dims)

class Piece:
    def __init__(self, color_seq): # colors are passed as a 4-seq, North-East-South-West
        self.color_seq = color_seq

    def __hash__(self):
        return hash(tuple(self.color_seq))

    def __str__(self):
        return f'Piece with colors = {self.color_seq}'

    def __repr__(self):
        return str(self)

    def is_center(self):
        return self.color_seq.count(0) == 0

    def is_border(self):
        return self.color_seq.count(0) == 1

    def is_corner(self):
        return self.color_seq.count(0) == 2

    def match(self, mask):
        for rot in range(4):
            works = True
            for i in range(4):
                piece_c = str(self.color_seq[(i+rot)%4])
                if piece_c != mask[i] and (mask[i] != '_' or piece_c == '0'):
                    works = False
                    break
            if works: return rot
        return -1

    @staticmethod
    def parse(color_seq_text):
        color_seq = list(map(int, color_seq_text.split(' ')))
        return Piece(color_seq)

def count_colors(pieces):
    S = set()
    for piece in pieces:
        for col in piece.color_seq:
            S.add(col)
    return len(S)-int(0 in S)

def piece_to_triangles(piece, pos, rot=None):
    ans = []
    list_of_cols = ['black','aqua', 'beige', 'crimson', 'coral', 'deeppink', 'green', 'khaki', 'maroon', 'orange', 'peru', 'teal', 'gold', 'chartreuse']

    i, j = pos
    if rot is None:
        if piece.is_corner():
            if i == 0 and j == 0:
                rot = piece.match(['0', '_', '_', '0'])
            elif i == j:
                rot = piece.match(['_', '0', '0', '_'])
            elif i > j:
                rot = piece.match(['_', '_', '0', '0'])
            else:
                rot = piece.match(['0', '0', '_', '_'])
        elif piece.is_border():
            if i == 0:
                rot = piece.match(['0', '_', '_', '_'])
            elif j == 0:
                rot = piece.match(['_', '_', '_', '0'])
            elif i > j:
                rot = piece.match(['_', '_', '0', '_'])
            else:
                rot = piece.match(['_', '0', '_', '_'])

    colors = []
    for ix in range(4):
        colors.append(list_of_cols[piece.color_seq[(ix + rot)%4]])
    
    x, y = j, i
    ans.append(plt.Polygon([(x*side, y*side), (x*side+side, y*side), (x*side + side/2, y*side+side/2)], facecolor=colors[0], edgecolor='black', lw=1))
    ans.append(plt.Polygon([(x*side+side, y*side), (x*side+side, y*side+side), (x*side + side/2, y*side+side/2)], facecolor=colors[1], edgecolor='black', lw=1))
    ans.append(plt.Polygon([(x*side+side, y*side+side), (x*side, y*side+side), (x*side + side/2, y*side+side/2)], facecolor=colors[2], edgecolor='black', lw=1))
    ans.append(plt.Polygon([(x*side, y*side+side), (x*side, y*side), (x*side + side/2, y*side+side/2)], facecolor=colors[3], edgecolor='black', lw=1))
#ans.append(plt.Polygon([(x*side, y*side), (x*side+side, y*side+side), color='black']))
    return ans
