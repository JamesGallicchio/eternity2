import Eternity2.TileSet
import Eternity2.CardinalityHelpers
import Eternity2.SATSolve

namespace Eternity2.Constraints

open Std EncCNF

/- Implement constraints as described in Heule 2008 -/

structure SquareIndex (size : Nat) where
  row : Fin size
  col : Fin size
deriving Repr

inductive DiamondIndex (psize : Nat) where
/-- col refers to the left triangle's column -/
| horz (row : Fin psize.succ) (col : Fin psize)
/-- row refers to the top triangle's row -/
| vert (row : Fin psize) (col : Fin psize.succ)
deriving Repr

namespace SquareIndex

def toFin : SquareIndex size → Fin (size * size)
| ⟨⟨i,hi⟩,⟨j,hj⟩⟩ => ⟨i * size + j, by
  cases size; case zero => contradiction
  case succ ps =>
  apply Nat.lt_of_succ_le
  rw [←Nat.add_succ]
  conv => rhs; rw [Nat.succ_mul]
  apply Nat.add_le_add
  apply Nat.mul_le_mul_right
  apply Nat.le_of_succ_le_succ hi
  exact hj⟩

private def maxIdx {psize : Nat} : Fin psize.succ := ⟨psize, Nat.lt_succ_self _⟩

private def middleFins (psize : Nat) : List ((i : Fin psize.succ) ×' (0 : Nat) < i ∧ i < psize) :=
  forIn' (m := Id) [1:psize] [] (fun x h y =>
    .yield (⟨⟨x, by exact Nat.le_step h.2⟩, by simp [h.2]; exact h.1⟩ :: y))

private def up : (i j : Fin psize.succ) → i.val > 0 → DiamondIndex psize
| i, j, h => .vert ⟨i-1, by
  match i with | ⟨i+1,h⟩ => simp; exact Nat.lt_of_succ_lt_succ h⟩ j

private def left : (i j : Fin psize.succ) → j.val > 0 → DiamondIndex psize
| i, j, h => .horz i ⟨j-1, by
  match j with | ⟨j+1,h⟩ => simp; exact Nat.lt_of_succ_lt_succ h⟩

private def down : (i j : Fin psize.succ) → i.val < psize → DiamondIndex psize
| i, j, h => .vert ⟨i, h⟩ j

private def right : (i j : Fin psize.succ) → j.val < psize → DiamondIndex psize
| i, j, h => .horz i ⟨j, h⟩


def corners (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 2 → DiamondIndex psize.succ)) :=
  [ (⟨0,0⟩, fun
        | 0 => right  0 0             (Nat.zero_lt_succ _)
        | 1 => down   0 0             (Nat.zero_lt_succ _))
  , (⟨0, maxIdx⟩, fun
        | 0 => down   0 maxIdx        (Nat.zero_lt_succ _)
        | 1 => left   0 maxIdx        (by simp [maxIdx, Nat.zero_lt_succ]))
  , (⟨maxIdx, maxIdx⟩, fun
        | 0 => left   maxIdx maxIdx   (by simp [maxIdx, Nat.zero_lt_succ])
        | 1 => up     maxIdx maxIdx   (by simp [maxIdx, Nat.zero_lt_succ]))
  , (⟨maxIdx, 0⟩, fun
        | 0 => up     maxIdx 0        (by simp [maxIdx, Nat.zero_lt_succ])
        | 1 => right  maxIdx 0        (Nat.zero_lt_succ _))
  ]

def borders (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 3 → DiamondIndex psize.succ)) :=
  middleFins psize.succ |>.bind fun ⟨i,h⟩ =>
    [ (⟨0, i⟩, fun
        | 0 => right  0 i   h.2
        | 1 => down   0 i   (Nat.zero_lt_succ _)
        | 2 => left   0 i   h.1)
    , (⟨i, 0⟩, fun
        | 0 => up     i 0   h.1
        | 1 => right  i 0   (Nat.zero_lt_succ _)
        | 2 => down   i 0   h.2)
    , (⟨maxIdx, i⟩, fun
        | 0 => left   maxIdx i  h.1
        | 1 => up     maxIdx i  (by simp [maxIdx, Nat.zero_lt_succ])
        | 2 => right  maxIdx i  h.2)
    , (⟨i, maxIdx⟩, fun
        | 0 => down   i maxIdx  h.2
        | 1 => left   i maxIdx  (by simp [maxIdx, Nat.zero_lt_succ])
        | 2 => up     i maxIdx  h.1)
    ]

def center (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 4 → DiamondIndex psize.succ)) :=
  middleFins psize.succ |>.bind fun ⟨x,hx⟩ =>
    middleFins psize.succ |>.map fun ⟨y,hy⟩ =>
      (⟨x,y⟩, fun
        | 0 => up     x y   hx.1
        | 1 => right  x y   hy.2
        | 2 => down   x y   hx.2
        | 3 => left   x y   hy.1)

def all (size : Nat) : List (SquareIndex size) :=
  List.fins size |>.bind fun i =>
    List.fins size |>.map fun j =>
      ⟨i,j⟩

end SquareIndex

namespace DiamondIndex

def toFin : DiamondIndex psize → Fin (2 * (psize * psize.succ))
| horz ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (psize + psize.succ) + j, by sorry⟩
| vert ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (psize + psize.succ) + psize + j, by sorry⟩

private def maxIdx {psize : Nat} : Fin psize.succ := ⟨psize, Nat.lt_succ_self _⟩
private def majorFins (psize : Nat) : List (Fin psize.succ) :=
  forIn (m := Id) [0:psize.succ] [] (fun x y => .yield (.ofNat x :: y))
private def middleFins (psize : Nat) : List (Fin psize.succ) :=
  forIn (m := Id) [1:psize] [] (fun x y => .yield (.ofNat x :: y))
private def minorFins (psize : Nat) : List (Fin psize) :=
  forIn' (m := Id) [0:psize] [] (fun x h y => .yield (⟨x,by exact h.2⟩ :: y))

def all (psize : Nat) : List (DiamondIndex psize) :=
  majorFins psize |>.bind fun i =>
    minorFins psize |>.bind fun j =>
      [ .horz i j
      , .vert j i ]

def border (psize : Nat) : List (DiamondIndex psize) :=
  minorFins psize |>.bind fun i =>
    [ .horz 0 i
    , .horz maxIdx i
    , .vert i 0
    , .vert i maxIdx ]

def center (psize : Nat) : List (DiamondIndex psize) :=
  middleFins psize |>.bind fun i =>
    minorFins psize |>.bind fun j =>
      [ .horz i j
      , .vert j i ]

end DiamondIndex

structure TileSetVariables (psize : Nat) (colors : Nat) where
  tiles : List Tile
  h_ts : tiles.length = psize.succ * psize.succ
  h_colors : tiles.all (·.colors.all (·.all (· ≤ colors)))
  h_ts_uniq : tiles.isDistinct
  piece_vars : Fin (psize.succ * psize.succ) → SquareIndex psize.succ → Var
  /-- color 0 here is color 1 elsewhere -/
  diamond_vars : DiamondIndex psize → Fin colors → Var

def TileSetVariables.pieceVarList (tsv : TileSetVariables psize colors) :=
  List.fins _ |>.bind fun p =>
  List.fins _ |>.bind fun r =>
  List.fins _ |>.map fun c =>
  tsv.piece_vars p ⟨r,c⟩

def TileSetVariables.diamondVarList (tsv : TileSetVariables psize colors) :=
  Constraints.DiamondIndex.all _ |>.bind fun d =>
  List.fins _ |>.map fun i =>
  tsv.diamond_vars d i

def tileIndices (psize : Nat) : List (Fin (psize.succ * psize.succ)) :=
  forIn (m := Id) [0:psize.succ * psize.succ] [] (fun x y => .yield (.ofNat x :: y))

private def cornerTiles (tsv : TileSetVariables s c) := tileIndices s |>.filterMap (fun i =>
  let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
  let tile := tsv.tiles[i']
  if tile.isCorner then some (tile,i) else none)
private def borderTiles (tsv : TileSetVariables s c) := tileIndices s |>.filterMap (fun i =>
  let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
  let tile := tsv.tiles[i']
  if tile.isBorder then some (tile,i) else none)
private def centerTiles (tsv : TileSetVariables s c) := tileIndices s |>.filterMap (fun i =>
  let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
  let tile := tsv.tiles[i']
  if tile.isCenter then some (tile,i) else none)

def mkVars (tiles : List Tile) (psize colors : Nat)
  (h_ts : tiles.length = psize.succ * psize.succ)
  (h_colors : tiles.all (·.colors.all (·.all (· ≤ colors))))
  (h_uniq : tiles.isDistinct)
  : EncCNF (TileSetVariables psize colors) := do
  let pvs ← EncCNF.mkVarBlock "x" [psize.succ*psize.succ, psize.succ*psize.succ]
  let dvs ← EncCNF.mkVarBlock "y" [2 * (psize * psize.succ), colors]
  return ⟨tiles, h_ts, h_colors, h_uniq, (pvs[·][·.toFin]), (dvs[·.toFin][·])⟩

def pieceConstraints (tsv : TileSetVariables size colors) : EncCNF Unit := do
  match size with
  | 0 => return
  | psize+1 =>

  /- Each square has a tile -/
  for (q,_) in SquareIndex.corners psize do
    EncCNF.addClause (cornerTiles tsv |>.map (tsv.piece_vars ·.2 q))

  for (q,_) in SquareIndex.borders psize do
    EncCNF.addClause (borderTiles tsv |>.map (tsv.piece_vars ·.2 q))

  for (q,_) in SquareIndex.center psize do
    EncCNF.addClause (centerTiles tsv |>.map (tsv.piece_vars ·.2 q))

  /- Each tile has a square -/
  for (_,p) in cornerTiles tsv do
    EncCNF.addClause (SquareIndex.corners psize |>.map (tsv.piece_vars p ·.1))

  for (_,p) in borderTiles tsv do
    EncCNF.addClause (SquareIndex.borders psize |>.map (tsv.piece_vars p ·.1))

  for (_,p) in centerTiles tsv do
    EncCNF.addClause (SquareIndex.center psize |>.map (tsv.piece_vars p ·.1))

  /- Eliminate mismatched square/tile types -/
  for (_,p) in cornerTiles tsv do
    for (q,_) in SquareIndex.borders psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.center psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]

  for (_,p) in borderTiles tsv do
    for (q,_) in SquareIndex.corners psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.center psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]

  for (_,p) in centerTiles tsv do
    for (q,_) in SquareIndex.corners psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.borders psize do
      EncCNF.addClause [.not (tsv.piece_vars p q)]


def diamondConstraints (tsv : TileSetVariables psize colors) : EncCNF Unit := do
  let borderColors : List (Fin colors) :=
      tsv.tiles.bind (·.getBorderColors) |>.filterMap (fun
        | none => none
        | some 0 => none
        | some (.succ i) => if h : i < colors then some ⟨i,h⟩ else none
      ) |>.distinct
  let centerColors : List (Fin colors) :=
      tsv.tiles.bind (·.getCenterColors) |>.filterMap (fun
        | none => none
        | some 0 => none
        | some (.succ i) => if h : i < colors then some ⟨i,h⟩ else none
      ) |>.distinct

  /- Each diamond has exactly one color (of the right type) -/
  for d in DiamondIndex.border psize do
    EncCNF.addClause (borderColors.map (tsv.diamond_vars d ·))

    for c in borderColors do
      for c' in borderColors do
        if c < c' then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]
    
    for c in List.fins _ do
      if !(c ∈ borderColors) then
        EncCNF.addClause [.not (tsv.diamond_vars d c)]

  for d in DiamondIndex.center psize do
    EncCNF.addClause (centerColors.map (tsv.diamond_vars d ·))
  
    for c in centerColors do
      for c' in centerColors do
        if c < c' then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]

    for c in List.fins _ do
      if !(c ∈ centerColors) then
        EncCNF.addClause [.not (tsv.diamond_vars d c)]

/- Piece classification for essential constraints -/
private inductive PieceClass (colors : Nat)
| corner            (u r      : Fin colors)
| border            (u r d    : Fin colors)
| fourSame          (urdl     : Fin colors)
| threeSame         (urd l    : Fin colors)
| twoNeighborPairs  (ur dl    : Fin colors)
| twoOppositePairs  (ud rl    : Fin colors)
| oneNeighborPair   (ur d l   : Fin colors)
| oneOppositePair   (ud r l   : Fin colors)
| allDiff           (u r d l  : Fin colors)
deriving Repr

instance : ToString (PieceClass colors) where
  toString x := (repr x).pretty

instance (c : Nat) : Inhabited (PieceClass c.succ) := ⟨.corner 0 0⟩

private def classify (colors : Nat) (t : Tile) (h : t.colors.all (·.all (· ≤ colors.succ))) : PieceClass colors.succ :=
  match t with
  | ⟨none, _, _, _, _⟩
  | ⟨_, none, _, _, _⟩
  | ⟨_, _, none, _, _⟩
  | ⟨_, _, _, none, _⟩ => panic! "unreachable 290581052"
  | ⟨some u, some d, some l, some r, _⟩ =>
  /- rotate to put color at u, border at l (if possible) -/
  match u,r,d,l with
  | 0, 0, 0, 0
  | _+1, 0, 0, 0 | 0, _+1, 0, 0 | 0, 0, _+1, 0 | 0, 0, 0, _+1
  | 0, _+1, 0, _+1 | _+1, 0, _+1, 0
     => panic! t.toString
  | u+1, r+1, 0, 0
  | 0, u+1, r+1, 0
  | 0, 0, u+1, r+1
  | r+1, 0, 0, u+1 => .corner ⟨u,sorry⟩ ⟨r,sorry⟩
  | u+1, r+1, d+1, 0
  | 0, u+1, r+1, d+1
  | d+1, 0, u+1, r+1
  | r+1, d+1, 0, u+1 => .border ⟨u,sorry⟩ ⟨r,sorry⟩ ⟨d,sorry⟩
  | w+1, x+1, y+1, z+1 =>
  dbgTrace s!"{w} {x} {y} {z}" fun () =>
  let w : Fin colors.succ := ⟨w,sorry⟩
  let x : Fin colors.succ := ⟨x,sorry⟩
  let y : Fin colors.succ := ⟨y,sorry⟩
  let z : Fin colors.succ := ⟨z,sorry⟩
  /- so much casework-/
  if w = x ∧ x = y ∧ y = z then
    .fourSame w
  else if w = x ∧ x = y then
    .threeSame w z
  else if x = y ∧ y = z then
    .threeSame x w
  else if y = z ∧ z = w then
    .threeSame y x
  else if z = w ∧ w = x then
    .threeSame z y
  else if w = x ∧ y = z then
    .twoNeighborPairs w y
  else if x = y ∧ z = w then
    .twoNeighborPairs x z
  else if w = y ∧ x = z then
    .twoOppositePairs w x
  else if w = x then
    .oneNeighborPair w y z
  else if x = y then
    .oneNeighborPair x z w
  else if y = z then
    .oneNeighborPair y w x
  else if z = w then
    .oneNeighborPair z x y
  else if w = y then
    .oneOppositePair w x z
  else if x = z then
    .oneOppositePair x y w
  else
    .allDiff w x y z

def essentialConstraints (tsv : TileSetVariables psize colors) : EncCNF Unit := do
  match psize, colors with
  | 0, _ | _, 0 => return
  | psize+1, colors+1 =>
  for _h : i in tileIndices psize.succ do
    match
      let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
      let res := classify colors tsv.tiles[i'] sorry
      res
    with
    | .corner u r =>
        for (q,ds) in SquareIndex.corners psize do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r -/
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 0) u]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 1) r]
    | .border u r d =>
        for (q,ds) in SquareIndex.borders psize do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r ∧ diamond3 colored d -/
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 0) u]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 1) r]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 2) d]
    | .fourSame urdl =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then all diamonds colored urdl -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds rot) urdl]
    | .threeSame urd l =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then one diamond must be l -/
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 0) l,
            tsv.diamond_vars (ds 1) l, tsv.diamond_vars (ds 2) l, tsv.diamond_vars (ds 3) l]
          /- and one of each opposite pair must be urd -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) urd, tsv.diamond_vars (ds (rot+2)) urd]
          /- and one of each adjacent pair must be urd -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) urd, tsv.diamond_vars (ds (rot+1)) urd]
    | .twoNeighborPairs ur dl =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then one of each opposite pair must be ur -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ur, tsv.diamond_vars (ds (rot+2)) ur]
          /- and one of each opposite pair must be dl -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) dl, tsv.diamond_vars (ds (rot+2)) dl]
    | .twoOppositePairs ud rl =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then one of each adjacent pair must be ud -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ud, tsv.diamond_vars (ds (rot+1)) ud]
          /- and one of each adjacent pair must be rl -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) rl, tsv.diamond_vars (ds (rot+1)) rl]
    | .oneNeighborPair ur d l =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then one of each opposite pair must be ur -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ur, tsv.diamond_vars (ds (rot+2)) ur]
          /- and if the adjacent pair is rot, rot+1, then rot+2 must be d and rot+3 must be l -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) ur), .not (tsv.diamond_vars (ds (rot+1)) ur),
              tsv.diamond_vars (ds (rot+2)) d]
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) ur), .not (tsv.diamond_vars (ds (rot+1)) ur),
              tsv.diamond_vars (ds (rot+3)) l]
    | .oneOppositePair ud r l =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed at q, then one of each adjacent pair must be ud -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ud, tsv.diamond_vars (ds (rot+1)) ud]
          /- and (if rot is r, rot+2 is l) and (if rot is l, rot+2 is r) -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) r), tsv.diamond_vars (ds (rot+2)) l]
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) l), tsv.diamond_vars (ds (rot+2)) r]
    | .allDiff u r d l =>
        for (q,ds) in SquareIndex.center psize do
          /- if i placed t q, then if rot is [u,r,d,l] then rot+1 is [r,d,l,u] -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) u), tsv.diamond_vars (ds (rot+1)) r]
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) r), tsv.diamond_vars (ds (rot+1)) d]
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) d), tsv.diamond_vars (ds (rot+1)) l]
            EncCNF.addClause [.not (tsv.piece_vars i q),
              .not (tsv.diamond_vars (ds rot) l), tsv.diamond_vars (ds (rot+1)) u]

def puzzleConstraints (ts : TileSet size colors)
  : ExceptT String EncCNF (TileSetVariables size.pred colors) := do
  match ts.tiles, size, colors with
  | _, 0, _ => throw "size must be greater than 0"
  | _, _, 0 => throw "colors must be greater than 0"
  | tiles, psize+1, pcolors+1 =>
  match h_ts : decide <| tiles.length = psize.succ * psize.succ with
  | false => throw s!"wrong number of tiles in tileset; expected {psize.succ * psize.succ} but got {tiles.length}"
  | true =>
  match h_colors : decide <| _ with
  | false => throw s!"some tiles exceed the color {pcolors+1}"
  | true =>
  match h_uniq : decide <| _ with
  | false => throw s!"some tiles not unique"
  | true =>
    let tsv ← mkVars tiles psize pcolors.succ
        ((decide_eq_true_iff _).mp h_ts)
        ((decide_eq_true_iff _).mp h_colors)
        ((decide_eq_true_iff _).mp h_uniq)
    pieceConstraints tsv
    diamondConstraints tsv
    essentialConstraints tsv
    return tsv
