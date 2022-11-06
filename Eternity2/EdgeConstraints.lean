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

def dUp : SquareIndex psize.succ → Option (DiamondIndex psize)
| ⟨⟨0,_⟩,_⟩   => none
| ⟨⟨i+1,h⟩,j⟩ => some <| .vert ⟨i, Nat.lt_of_succ_lt_succ h⟩ j

def dLeft : SquareIndex psize.succ → Option (DiamondIndex psize)
| ⟨_,⟨0,_⟩⟩   => none
| ⟨i,⟨j+1,h⟩⟩ => some <| .horz i ⟨j, Nat.lt_of_succ_lt_succ h⟩

def dDown : SquareIndex psize.succ → Option (DiamondIndex psize)
| ⟨⟨i,_⟩,j⟩ =>
  if h : i < psize then
    some <| .vert ⟨i, h⟩ j
  else none

def dRight : SquareIndex psize.succ → Option (DiamondIndex psize)
| ⟨i,⟨j,_⟩⟩ =>
  if h : j < psize then
    some <| .horz i ⟨j, h⟩
  else none

private def middleFins (psize : Nat) : List (Fin psize.succ) :=
  forIn (m := Id) [1:psize] [] (fun x y => .yield (.ofNat x :: y))

def corners (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 2 → DiamondIndex psize.succ)) :=
  [ (⟨0,0⟩, fun
        | 0 => .horz 0 0
        | 1 => .vert 0 0)
  , (⟨0, maxIdx⟩, fun
        | 0 => .vert 0 maxIdx
        | 1 => .horz 0 maxIdx)
  , (⟨maxIdx, 0⟩, fun
        | 0 => .vert maxIdx 0
        | 1 => .horz maxIdx 0)
  , (⟨maxIdx, maxIdx⟩, fun
        | 0 => .horz maxIdx maxIdx
        | 1 => .vert maxIdx maxIdx)
  ]

def borders (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 3 → DiamondIndex psize.succ)) :=
  middleFins psize.succ |>.bind fun i =>
    [ (⟨0, i⟩, fun
        | 0 => .horz 0 (.ofNat i.val)
        | 1 => .vert 0 i
        | 2 => .horz 0 (.ofNat (i.val-1)))
    , (⟨i, 0⟩, fun
        | 0 => .vert (.ofNat (i.val-1)) 0
        | 1 => .horz i 0
        | 2 => .vert (.ofNat i.val) 0)
    , (⟨maxIdx, i⟩, fun
        | 0 => .horz maxIdx (.ofNat (i.val-1))
        | 1 => .vert maxIdx i
        | 2 => .horz maxIdx (.ofNat i.val))
    , (⟨i, maxIdx⟩, fun
        | 0 => .vert (.ofNat (i.val-1)) maxIdx
        | 1 => .horz i maxIdx
        | 2 => .vert (.ofNat i.val) maxIdx)
    ]

def center (psize : Nat) : List (SquareIndex psize.succ.succ × (Fin 4 → DiamondIndex psize.succ)) :=
  middleFins psize.succ |>.bind fun x =>
    middleFins psize.succ |>.map fun y =>
      (⟨x,y⟩, fun
        | 0 => .vert (.ofNat (x.val-1)) (.ofNat y.val)
        | 1 => .horz (.ofNat x.val) (.ofNat y.val)
        | 2 => .vert (.ofNat x.val) (.ofNat y.val)
        | 3 => .horz (.ofNat x.val) (.ofNat (y.val-1)))

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

private def tileIndices (psize : Nat) : List (Fin (psize.succ * psize.succ)) :=
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

def pieceConstraints (tsv : TileSetVariables psize colors) : EncCNF Unit := do
  match psize with
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

  /- Each diamond has exactly one color -/
  for d in DiamondIndex.border psize do
    EncCNF.addClause (borderColors.map (tsv.diamond_vars d ·))

    for c in borderColors do
      for c' in borderColors do
        if c < c' then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]

  for d in DiamondIndex.center psize do
    EncCNF.addClause (centerColors.map (tsv.diamond_vars d ·))
  
    for c in centerColors do
      for c' in centerColors do
        if c < c' then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]

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

instance (c : Nat) : Inhabited (PieceClass c.succ) := ⟨.corner 0 0⟩

private def classify (colors : Nat) (t : Tile) (h : t.colors.all (·.all (· ≤ colors.succ))) : PieceClass colors.succ :=
  match t with
  | ⟨none, _, _, _, _⟩
  | ⟨_, none, _, _, _⟩
  | ⟨_, _, none, _, _⟩
  | ⟨_, _, _, none, _⟩ => panic! "unreachable 290581052"
  | ⟨some u, some d, some r, some l, _⟩ =>
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
  else if y = z ∧ z = x then
    .threeSame y x
  else if z = x ∧ x = y then
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
      classify colors tsv.tiles[i'] sorry
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

def puzzleConstraints (ts : TileSet)
  : EncCNF (Except String (TileSetVariables ts.size.pred ts.colors)) := do
  match ts with
  | ⟨_, 0, _⟩ => return .error "size must be greater than 0"
  | ⟨_, _, 0⟩ => return .error "colors must be greater than 0"
  | ⟨tiles, psize+1, pcolors+1⟩ =>
  match h_ts : decide <| tiles.length = psize.succ * psize.succ with
  | false => return .error s!"wrong number of tiles in tileset; expected {psize.succ * psize.succ} but got {tiles.length}"
  | true =>
  match h_colors : decide <| _ with
  | false => return .error s!"some tiles exceed the color {pcolors+1}"
  | true =>
  match h_uniq : decide <| _ with
  | false => return .error s!"some tiles not unique"
  | true =>
    let tsv ← mkVars tiles psize pcolors.succ
        ((decide_eq_true_iff _).mp h_ts)
        ((decide_eq_true_iff _).mp h_colors)
        ((decide_eq_true_iff _).mp h_uniq)
    pieceConstraints tsv
    diamondConstraints tsv
    essentialConstraints tsv
    return .ok tsv
