/- Implement constraints as described in Heule 2008 -/

import Eternity2.Puzzle.TileSet
import Eternity2.Puzzle.CardConstraint

namespace Eternity2.Encoding

open Std LeanSAT Encode EncCNF Notation

structure TileSetVariables (size s) where
  ts : TileSet size (Tile <| Color.WithBorder s)
  piece_vars : Fin (size * size) → SquareIndex size → Var
  diamond_vars : DiamondIndex size → Color.WithBorder s → Var
  sign_vars : Fin (size * size) → Var

namespace TileSetVariables

instance [Inhabited (Color.WithBorder s)] : Inhabited <| TileSetVariables size s where
  default := {
    ts := default
    piece_vars := λ _ _ => 0
    diamond_vars := λ _ _ => 0
    sign_vars := λ _ => 0
  }

variable (tsv : TileSetVariables size s)

def pieceVarList :=
  List.fins _ |>.bind fun p =>
  List.fins _ |>.bind fun r =>
  List.fins _ |>.map fun c =>
  tsv.piece_vars p ⟨r,c⟩

def diamondVarList :=
  DiamondIndex.all _ |>.bind fun d =>
  Color.allColors |>.map fun i =>
  tsv.diamond_vars d i

def signVarList := List.fins _ |>.map (tsv.sign_vars)

def borderDiamondVarList :=
  DiamondIndex.border _ |>.bind fun d =>
  Color.allColors |>.map fun i =>
  tsv.diamond_vars d i

def frameDiamondVarList :=
  DiamondIndex.frame _ |>.bind fun d =>
  Color.allColors |>.map fun i =>
  tsv.diamond_vars d i

private def cornerTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.ts.h_ts]; exact i.isLt⟩
    let tile := tsv.ts.tiles[i']
    if tile.isCorner then some (tile,i) else none)
private def sideTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.ts.h_ts]; exact i.isLt⟩
    let tile := tsv.ts.tiles[i']
    if tile.isSide then some (tile,i) else none)
private def centerTiles :=
  List.fins _ |>.filterMap (fun i =>
    let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.ts.h_ts]; exact i.isLt⟩
    let tile := tsv.ts.tiles[i']
    if tile.isCenter then some (tile,i) else none)

end TileSetVariables

def mkVars (ts : TileSet size (Tile <| Color.WithBorder s))
  : EncCNF (TileSetVariables size s) := do
  match ts.tiles.isDistinct with
  | false => throw s!"some tiles not unique; currently unsupported"
  | true =>
  let map := s.toMap
  let pvs ← mkVarBlock "x" [size*size, size*size]
  let dvs ← mkVarBlock "y" [2 * (size * size.succ), s.size]
  let svs ← mkVarBlock "z" [size*size]
  return ⟨ts, (pvs[·][·.toFin]), (fun di c =>
    match map.find? c with
    | some i => dvs[di.toFin][i]
    | none => panic! s!"{c}"), (svs[·])⟩

def pieceConstraints (tsv : TileSetVariables size s) : EncCNF Unit :=
  EncCNF.newCtx "pieceConstraints" do

  let squaresAndTiles :=
    [ (0, SquareIndex.corners  size |>.map (·.1), tsv.cornerTiles |>.map (·.2))
    , (1, SquareIndex.sides    size |>.map (·.1), tsv.sideTiles   |>.map (·.2))
    , (2, SquareIndex.center   size |>.map (·.1), tsv.centerTiles |>.map (·.2))]

  for (_,squares,tiles) in squaresAndTiles do
    /- Each square has a tile -/
    for q in squares do
      addClause ⟨tiles |>.map (tsv.piece_vars · q)⟩
    
    /- Each tile has a square -/
    for p in tiles do
      addClause ⟨squares |>.map (tsv.piece_vars p ·)⟩

  /- Eliminate mismatched square/tile types -/
  for ((x,squares,_),(y,_,tiles)) in
    List.product squaresAndTiles squaresAndTiles do
    if x ≠ y then
      for p in tiles do
        for q in squares do
          addClause (¬tsv.piece_vars p q)


/-- Constrain each diamond has exactly one color (of the right type) -/
def diamondConstraints (tsv : TileSetVariables size s) : EncCNF Unit :=
  EncCNF.newCtx "diamondConstraints" do
  /- Frame (always frameColor) -/
  for d in DiamondIndex.frame size do
    addClause (tsv.diamond_vars d .frame)
    for c in Color.allColors do
      if not c.isFrame then
        addClause (¬tsv.diamond_vars d c)

  /- Border -/
  for d in DiamondIndex.border size do
    addClause ⟨Color.borderColors.map (tsv.diamond_vars d ·)⟩

    atMostOne <| Color.borderColors.map (tsv.diamond_vars d ·)

    for c in Color.allColors do
      if not c.isBorder then
        addClause (¬tsv.diamond_vars d c)

  for d in DiamondIndex.center size do
    addClause ⟨Color.centerColors.map (tsv.diamond_vars d ·)⟩

    atMostOne <| Color.centerColors.map (tsv.diamond_vars d ·)

    for c in Color.allColors do
      if not c.isCenter then
        addClause (¬tsv.diamond_vars d c)


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

instance (s) : Inhabited (PieceClass (Color.WithBorder s)) :=
  ⟨.corner default default⟩

private def classify (t : Tile (Color.WithBorder s))
  : PieceClass (Color.WithBorder s) :=
  match t.classify with
  | none => panic! s!"Encountered invalid piece during solving:\n{t.toString}"
  | some (.corner x y) => .corner x y
  | some (.side x y z) => .side x y z
  | some (.center w x y z) =>
  /- so much casework-/
  if w = x && x = y && y = z then
    .fourSame w
  else if w = x && x = y then
    .threeSame w z
  else if x = y && y = z then
    .threeSame x w
  else if y = z && z = w then
    .threeSame y x
  else if z = w && w = x then
    .threeSame z y
  else if w = x && y = z then
    .twoNeighborPairs w y
  else if x = y && z = w then
    .twoNeighborPairs x z
  else if w = y && x = z then
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

def essentialConstraints (tsv : TileSetVariables size s) (onlyEdge : Bool) : EncCNF Unit :=
  EncCNF.newCtx "essentialConstraints" do
  for _h : i in List.fins _ do
    match (
      let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.ts.h_ts]; exact i.isLt⟩
      classify tsv.ts.tiles[i']
    ) with
    | .corner u r =>
        for (q,ds) in SquareIndex.corners size do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r -/
          addClause (¬tsv.piece_vars i q ∨ tsv.diamond_vars (ds 0) u)
          addClause (¬tsv.piece_vars i q ∨ tsv.diamond_vars (ds 1) r)
    | .side u r d =>
        for (q,ds) in SquareIndex.sides size do
          /- if i placed at q, then diamond1 colored u ∧ diamond2 colored r ∧ diamond3 colored d -/
          addClause (¬ tsv.piece_vars i q ∨ tsv.diamond_vars (ds 0) u)
          addClause (¬ tsv.piece_vars i q ∨ tsv.diamond_vars (ds 1) r)
          addClause (¬ tsv.piece_vars i q ∨ tsv.diamond_vars (ds 2) d)
    | .fourSame urdl =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then all diamonds colored urdl -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q ∨ tsv.diamond_vars (ds rot) urdl)
    | .threeSame urd l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one diamond must be l -/
          addClause (¬tsv.piece_vars i q ∨ tsv.diamond_vars (ds 0) l ∨
            tsv.diamond_vars (ds 1) l ∨ tsv.diamond_vars (ds 2) l ∨ tsv.diamond_vars (ds 3) l)
          /- and one of each opposite pair must be urd -/
          for rot in [0,1] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) urd ∨ tsv.diamond_vars (ds (rot+2)) urd)
          /- and one of each adjacent pair must be urd -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) urd ∨ tsv.diamond_vars (ds (rot+1)) urd)
    | .twoNeighborPairs ur dl =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each opposite pair must be ur -/
          for rot in [0,1] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) ur ∨ tsv.diamond_vars (ds (rot+2)) ur)
          /- and one of each opposite pair must be dl -/
          for rot in [0,1] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) dl ∨ tsv.diamond_vars (ds (rot+2)) dl)
    | .twoOppositePairs ud rl =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each adjacent pair must be ud -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) ud ∨ tsv.diamond_vars (ds (rot+1)) ud)
          /- and one of each adjacent pair must be rl -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) rl ∨ tsv.diamond_vars (ds (rot+1)) rl)
    | .oneNeighborPair ur d l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each opposite pair must be ur -/
          for rot in [0,1] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) ur ∨ tsv.diamond_vars (ds (rot+2)) ur)
          /- and if the adjacent pair is rot, rot+1, then rot+2 must be d and rot+3 must be l -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) ur ∨ ¬tsv.diamond_vars (ds (rot+1)) ur
              ∨ tsv.diamond_vars (ds (rot+2)) d)
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) ur ∨ ¬tsv.diamond_vars (ds (rot+1)) ur
              ∨ tsv.diamond_vars (ds (rot+3)) l)
    | .oneOppositePair ud r l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then one of each adjacent pair must be ud -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds rot) ud ∨ tsv.diamond_vars (ds (rot+1)) ud)
          /- and (if rot is r, rot+2 is l) and (if rot is l, rot+2 is r) -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) r ∨ tsv.diamond_vars (ds (rot+2)) l)
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) l ∨ tsv.diamond_vars (ds (rot+2)) r)
          /- one of the diamonds must be one of the colours -/
          addClause (¬tsv.piece_vars i q
            ∨ tsv.diamond_vars (ds 0) r ∨ tsv.diamond_vars (ds 1) r
            ∨ tsv.diamond_vars (ds 2) r ∨ tsv.diamond_vars (ds 3) r)
          addClause (¬tsv.piece_vars i q
            ∨ tsv.diamond_vars (ds 0) l ∨ tsv.diamond_vars (ds 1) l
            ∨ tsv.diamond_vars (ds 2) l ∨ tsv.diamond_vars (ds 3) l)
    | .allDiff u r d l =>
      if !onlyEdge then
        for (q,ds) in SquareIndex.center size do
          /- if i placed at q, then if rot is [u,r,d,l] then rot+1 is [r,d,l,u] -/
          for rot in [0,1,2,3] do
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) u ∨ tsv.diamond_vars (ds (rot+1)) r)
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) r ∨ tsv.diamond_vars (ds (rot+1)) d)
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) d ∨ tsv.diamond_vars (ds (rot+1)) l)
            addClause (¬tsv.piece_vars i q
              ∨ ¬tsv.diamond_vars (ds rot) l ∨ tsv.diamond_vars (ds (rot+1)) u)
          /- one of the diamonds must be each of the colours -/
          for c in [u,r,d,l] do
            addClause (¬tsv.piece_vars i q
              ∨ tsv.diamond_vars (ds 0) c ∨ tsv.diamond_vars (ds 1) c
              ∨ tsv.diamond_vars (ds 2) c ∨ tsv.diamond_vars (ds 3) c)

def compactEncoding (tsv : TileSetVariables size s) (onlyEdge : Bool := false)
  : EncCNF Unit := do
    pieceConstraints tsv
    diamondConstraints tsv
    essentialConstraints tsv onlyEdge

/-- A piece can be placed in atMostOne spot -/
def pieceExplicitConstraints (tsv : TileSetVariables size s) : EncCNF Unit := do
  for (_,p) in tsv.cornerTiles do
    SquareIndex.corners size
    |>.map (tsv.piece_vars p ·.1)
    |> atMostOne
  for (_,p) in tsv.sideTiles do
    SquareIndex.sides size
    |>.map (tsv.piece_vars p ·.1)
    |> atMostOne
  for (_,p) in tsv.centerTiles do
    SquareIndex.center size
    |>.map (tsv.piece_vars p ·.1)
    |> atMostOne

def forbiddenColors (tsv : TileSetVariables size s) : EncCNF Unit := do
  for (t,p) in tsv.centerTiles do
    let forbiddenColors := Color.centerColors.filter (!t.colors.contains ·)
    for (q,ds) in SquareIndex.center size do
      /- If tile p is placed at q, then each bordering diamond cannot be
          among the forbidden colors -/
      for c in forbiddenColors do
        for i in List.fins 4 do
          addClause (¬tsv.piece_vars p q ∨ ¬tsv.diamond_vars (ds i) c)

/- Break rotational symmetry by assigning a corner to (0,0) -/
def fixCorner (tsv : TileSetVariables size s) : EncCNF Unit := do
  if h:size > 0 then
    for (i, _) in tsv.ts.tiles.enum.find? (·.2.isCorner) do
      if hi:_ then
        addClause (tsv.piece_vars ⟨i, hi⟩ ⟨⟨0,h⟩,⟨0,h⟩⟩)
      else panic! "woah"

/- Constrain board to be the i'th corner configuration -/
def fixCorners (tsv : TileSetVariables size s) (num : Fin 6) : EncCNF Unit := do
  if h:size > 0 then
    let corners := tsv.ts.tiles.enum'.filter (fun (_, t) => t.isCorner)
    match corners with
    | [a,b,c,d] =>
      let (b,c,d) :=
        match num with
        | 0 => (b,c,d)
        | 1 => (b,d,c)
        | 2 => (c,b,d)
        | 3 => (c,d,b)
        | 4 => (d,b,c)
        | 5 => (d,c,b)
      addClause <| tsv.piece_vars (tsv.ts.h_ts ▸ a.1) ⟨⟨0,h⟩,        ⟨0,h⟩⟩
      addClause <| tsv.piece_vars (tsv.ts.h_ts ▸ b.1) ⟨⟨0,h⟩,        Fin.last _ h⟩
      addClause <| tsv.piece_vars (tsv.ts.h_ts ▸ c.1) ⟨Fin.last _ h, ⟨0,h⟩⟩
      addClause <| tsv.piece_vars (tsv.ts.h_ts ▸ d.1) ⟨Fin.last _ h, Fin.last _ h⟩
    | _ =>
      panic! s!"Tileset had {corners.length} corners"

/-- Given a list of tiles, encode that for each
border- or center-color, the `c`-colored triangles
must be half `+` and half `-`.
-/
def colorCardConstraints (tsv : TileSetVariables size s)
  : EncCard Unit := do
  for color in Color.borderColors ++ Color.centerColors do
    let cVars :=
      List.fins (size*size) |>.bind (fun idx =>
        let t := tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx]
        let var := tsv.sign_vars idx
        t.colors.filter (· = color) |>.map (fun _ => var))
    let pos := cVars.map (.pos)
    assert! (pos.length % 2 = 0) -- handshake lemma :)
    EncCard.addClause <| .ofLits pos (pos.length / 2)

def signCardConstraints (tsv : TileSetVariables size s)
  : EncCard Unit := do
  if size % 2 == 0 then
    /- Half the corners should be pos -/
    let corner_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isCorner)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! corner_vars.length == 4
    EncCard.addClause <| .ofLits corner_vars 2
    /- Half the side pieces should be pos -/
    let side_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isSide)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! side_vars.length == 4*(size-2)
    EncCard.addClause <| .ofLits side_vars (2*(size-2))
    /- Half the center pieces should be pos -/
    let center_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isCenter)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! center_vars.length == (size-2)*(size-2)
    EncCard.addClause <| .ofLits center_vars ((size-2) * (size-2) / 2)
  else
    /- All the corners should be pos -/
    let corner_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isCorner)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! corner_vars.length == 4
    EncCard.addClause <| .ofLits corner_vars 4
    /- Half - 2 of the side pieces should be pos -/
    let side_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isSide)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! side_vars.length == 4*(size-2)
    EncCard.addClause <| .ofLits side_vars (2*(size-3))
    /- Half (round up) the center pieces should be pos -/
    let center_vars := List.fins (size*size)
      |>.filter (fun idx => tsv.ts.tiles[tsv.ts.h_ts.symm ▸ idx].isCenter)
      |>.map (.pos <| tsv.sign_vars ·)
    assert! center_vars.length == (size-2)*(size-2)
    EncCard.addClause <| .ofLits center_vars (((size-2) * (size-2) + 1) / 2)

def associatePolarities (ts : TileSetVariables size s) : EncCNF Unit := do
  -- For each piece & location, positive location -> positive piece, negative location -> negative piece
  for p in List.fins _ do
    for ⟨i,j⟩ in SquareIndex.all size do
      if (i.val + j) % 2 = 0 then
        -- positive location
        addClause (¬ts.piece_vars p ⟨i,j⟩ ∨ ts.sign_vars p)
      else
        -- negative location
        addClause (¬ts.piece_vars p ⟨i,j⟩ ∨ ¬ts.sign_vars p)
