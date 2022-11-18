import Eternity2.TileSet
import Eternity2.SATSolve.CardinalityHelpers

namespace Eternity2.Constraints

open Std EncCNF

/- Implement constraints as described in Heule 2008 -/

structure TileSetVariables (size b c : Nat) where
  tiles : List (Tile (Color.withBorder b c))
  h_ts : tiles.length = size * size
  h_ts_uniq : tiles.isDistinct
  piece_vars : Fin (size * size) → SquareIndex size → Var
  diamond_vars : DiamondIndex size → Fin (b+c+1) → Var

namespace TileSetVariables

variable (tsv : TileSetVariables size b c)

def pieceVarList :=
  List.fins _ |>.bind fun p =>
  List.fins _ |>.bind fun r =>
  List.fins _ |>.map fun c =>
  tsv.piece_vars p ⟨r,c⟩

def diamondVarList :=
  DiamondIndex.all _ |>.bind fun d =>
  List.fins _ |>.map fun i =>
  tsv.diamond_vars d i

def borderDiamondVarList :=
  DiamondIndex.border _ |>.bind fun d =>
  List.fins _ |>.map fun i =>
  tsv.diamond_vars d i

def frameDiamondVarList :=
  DiamondIndex.frame _ |>.bind fun d =>
  List.fins _ |>.map fun i =>
  tsv.diamond_vars d i

private def cornerTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
    let tile := tsv.tiles[i']
    if tile.isCorner then some (tile,i) else none)
private def sideTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
    let tile := tsv.tiles[i']
    if tile.isSide then some (tile,i) else none)
private def centerTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
    let tile := tsv.tiles[i']
    if tile.isCenter then some (tile,i) else none)

end TileSetVariables

def mkVars (tiles : List (Tile (Color.withBorder b c))) (size : Nat)
  (h_ts : tiles.length = size * size)
  (h_uniq : tiles.isDistinct)
  : EncCNF (TileSetVariables size b c) := do
  let pvs ← EncCNF.mkVarBlock "x" [size*size, size*size]
  let dvs ← EncCNF.mkVarBlock "y" [2 * (size * size.succ), b+c+1]
  return ⟨tiles, h_ts, h_uniq, (pvs[·][·.toFin]), (dvs[·.toFin][·])⟩

def pieceConstraints (tsv : TileSetVariables size b c) : EncCNF Unit := do
  
  /- Each square has a tile -/
  for (q,_) in SquareIndex.corners size do
    EncCNF.addClause (tsv.cornerTiles |>.map (tsv.piece_vars ·.2 q))

  for (q,_) in SquareIndex.sides size do
    EncCNF.addClause (tsv.sideTiles |>.map (tsv.piece_vars ·.2 q))

  for (q,_) in SquareIndex.center size do
    EncCNF.addClause (tsv.centerTiles |>.map (tsv.piece_vars ·.2 q))

  /- Each tile has a square -/
  for (_,p) in tsv.cornerTiles do
    EncCNF.addClause (SquareIndex.corners size |>.map (tsv.piece_vars p ·.1))

  for (_,p) in tsv.sideTiles do
    EncCNF.addClause (SquareIndex.sides size |>.map (tsv.piece_vars p ·.1))

  for (_,p) in tsv.centerTiles do
    EncCNF.addClause (SquareIndex.center size |>.map (tsv.piece_vars p ·.1))

  /- Eliminate mismatched square/tile types -/
  for (_,p) in tsv.cornerTiles do
    for (q,_) in SquareIndex.sides size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.center size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]

  for (_,p) in tsv.sideTiles do
    for (q,_) in SquareIndex.corners size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.center size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]

  for (_,p) in tsv.centerTiles do
    for (q,_) in SquareIndex.corners size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]
    for (q,_) in SquareIndex.sides size do
      EncCNF.addClause [.not (tsv.piece_vars p q)]


/-- Constrain each diamond has exactly one color (of the right type) -/
def diamondConstraints (tsv : TileSetVariables size b c) : EncCNF Unit := do
  /- Frame (always frameColor) -/
  for d in DiamondIndex.frame size do
    EncCNF.addClause [tsv.diamond_vars d (Color.frameColor)]

  /- Border -/
  for d in DiamondIndex.border size do
    EncCNF.addClause (Color.borderColors.map (tsv.diamond_vars d ·))

    /- AMO constraint, defined pairwise -/
    for c in Color.borderColors do
      for c' in Color.borderColors do
        if c.val < c'.val then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]
  
  for d in DiamondIndex.center size do
    EncCNF.addClause (Color.centerColors.map (tsv.diamond_vars d ·))
  
    for c in Color.centerColors do
      for c' in Color.centerColors do
        if c.val < c'.val then
          EncCNF.addClause [.not (tsv.diamond_vars d c), .not (tsv.diamond_vars d c')]


/- Piece classification for essential constraints -/
private inductive PieceClass (color : Type u)
| corner            (u r      : color)
| side              (u r d    : color)
| fourSame          (urdl     : color)
| threeSame         (urd l    : color)
| twoNeighborPairs  (ur dl    : color)
| twoOppositePairs  (ud rl    : color)
| oneNeighborPair   (ur d l   : color)
| oneOppositePair   (ud r l   : color)
| allDiff           (u r d l  : color)
deriving Repr

instance [Repr c] : ToString (PieceClass c) where
  toString x := (repr x).pretty

instance (b c : Nat) : Inhabited (PieceClass (Color.withBorder b c)) :=
  ⟨.corner ⟨0,Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩⟩

private def classify (t : Tile (Color.withBorder b c))
  : PieceClass (Color.withBorder b c) :=
  match t with
  | {up, right, down, left} =>
  /- rotate to put color at u, border at l (if possible) -/
  match up.val,right.val,down.val,left.val with
  | 0, 0, 0, 0
  | _+1, 0, 0, 0 | 0, _+1, 0, 0 | 0, 0, _+1, 0 | 0, 0, 0, _+1
  | 0, _+1, 0, _+1 | _+1, 0, _+1, 0
     => panic! s!"Encountered invalid piece during solving:\n{t.toString}"
  | u+1, r+1, 0, 0
  | 0, u+1, r+1, 0
  | 0, 0, u+1, r+1
  | r+1, 0, 0, u+1 => .corner ⟨u+1,sorry⟩ ⟨r+1,sorry⟩
  | u+1, r+1, d+1, 0
  | 0, u+1, r+1, d+1
  | d+1, 0, u+1, r+1
  | r+1, d+1, 0, u+1 => .side ⟨u+1,sorry⟩ ⟨r+1,sorry⟩ ⟨d+1,sorry⟩
  | w+1, x+1, y+1, z+1 =>
  let w : Color.withBorder b c := ⟨w+1,sorry⟩
  let x : Color.withBorder b c := ⟨x+1,sorry⟩
  let y : Color.withBorder b c := ⟨y+1,sorry⟩
  let z : Color.withBorder b c := ⟨z+1,sorry⟩
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

def essentialConstraints (tsv : TileSetVariables size b c) (onlyEdge : Bool) : EncCNF Unit := do
  for _h : i in List.fins _ do
    match (
      let i' : Fin tsv.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
      classify tsv.tiles[i']
    ) with
    | .corner u r =>
        for (q,ds) in SquareIndex.corners size do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r -/
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 0) u]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 1) r]
    | .side u r d =>
        for (q,ds) in SquareIndex.sides size do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r ∧ diamond3 colored d -/
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 0) u]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 1) r]
          EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds 2) d]
    | .fourSame urdl =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then all diamonds colored urdl -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q), tsv.diamond_vars (ds rot) urdl]
    | .threeSame urd l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
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
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each opposite pair must be ur -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ur, tsv.diamond_vars (ds (rot+2)) ur]
          /- and one of each opposite pair must be dl -/
          for rot in [0,1] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) dl, tsv.diamond_vars (ds (rot+2)) dl]
    | .twoOppositePairs ud rl =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each adjacent pair must be ud -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) ud, tsv.diamond_vars (ds (rot+1)) ud]
          /- and one of each adjacent pair must be rl -/
          for rot in [0,1,2,3] do
            EncCNF.addClause [.not (tsv.piece_vars i q),
              tsv.diamond_vars (ds rot) rl, tsv.diamond_vars (ds (rot+1)) rl]
    | .oneNeighborPair ur d l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
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
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
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
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
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

def puzzleConstraints (ts : TileSet size (Color.withBorder b c)) (onlyEdge : Bool := false)
  : ExceptT String EncCNF (TileSetVariables size b c) := do
  match h_ts : decide <| ts.tiles.length = size * size with
  | false => throw s!"wrong number of tiles in tileset; expected {size * size} but got {ts.tiles.length}"
  | true =>
  match h_uniq : decide <| _ with
  | false => throw s!"some tiles not unique"
  | true =>
    let tsv ← mkVars ts.tiles size
        ((decide_eq_true_iff _).mp h_ts)
        ((decide_eq_true_iff _).mp h_uniq)
    pieceConstraints tsv
    diamondConstraints tsv
    essentialConstraints tsv onlyEdge
    return tsv

def fixCorner (ts : TileSetVariables size b c) : EncCNF Unit := do
  -- Break rotational symmetry by assigning a corner to (0,0)
  if h:size > 0 then
    for (i, _) in ts.tiles.enum.find? (·.2.isCorner) do
      if hi:_ then
        addClause [ts.piece_vars ⟨i, hi⟩ ⟨⟨0,h⟩,⟨0,h⟩⟩]
      else panic! "woah"

def associatePolarities (ts : TileSetVariables size b c)
        (signVars : List (Tile (Color.withBorder b c) × EncCNF.Var))
        (h : signVars.length = size * size) : EncCNF Unit := do
  -- For each piece & location, positive location -> positive piece, negative location -> negative piece
  for p in List.fins _ do
    for ⟨i,j⟩ in SquareIndex.all size do
      if (i.val + j) % 2 = 0 then
        -- positive location
        addClause [.not <| ts.piece_vars (h ▸ p) ⟨i,j⟩, signVars[p].2]
      else
        -- negative location
        addClause [.not <| ts.piece_vars (h ▸ p) ⟨i,j⟩, .not <| signVars[p].2]