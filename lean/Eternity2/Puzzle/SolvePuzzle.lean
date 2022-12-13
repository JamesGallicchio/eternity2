import Eternity2.Puzzle.EdgeConstraints
import Eternity2.Puzzle.Board
import Eternity2.SATSolve

namespace Eternity2

open Constraints EncCNF

structure BoardSol [BEq c] (ts : TileSet size c) where
  /-- For each tile in tileset, its index + rotation (0 = up) -/
  pieceIdx : Fin (size * size) → SquareIndex size × Fin 4

def SolvePuzzle.decodeDiamonds (tsv : Constraints.TileSetVariables size b c)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : DiamondBoard size (Option (Color.withBorder b c)) := {
    board :=
      Array.init _ (fun k =>
          List.fins _
            |>.find? (fun color => s.find? (tsv.diamond_vars (.ofFin k) color) |>.getD false)
      )
    boardsize := by simp
  }
  tb

def SolvePuzzle.decodePieces
      (tsv : Constraints.TileSetVariables size b c)
      (s : Std.HashMap EncCNF.Var Bool)
    : Except String (BoardSol tsv.ts) := do
  let board ← decodeDiamonds tsv s |>.expectFull
  let sol ←
    Array.initM _ (fun p => do
      match
        SquareIndex.all size
          |>.find? (fun idx => s.find? (tsv.piece_vars p idx) |>.get!)
      with
      | some idx =>
        let tile := tsv.ts.tiles[tsv.ts.h_ts.symm ▸ p]
        match Tile.numRotations tile (board.diamond_to_tile idx.row idx.col) with
        | some rot => return (idx,rot)
        | none => throw "tile {p} does not fit at {i},{j} in the diamond solution:\n{board}"
      | none => throw "Incomplete tile assignment"
    )
  have : sol.size = size * size := sorry
  return ⟨(sol[this.symm ▸ ·])⟩

def BoardSol.writeSolution (filename : System.FilePath)
    [BEq c] {ts : TileSet size c} (sol : BoardSol ts)
                : IO Unit := do
  IO.FS.withFile filename .write (fun h => do
    -- h.putStrLn "c pieceNum x y rotation"
    h.putStrLn ""
    for i in List.fins _ do
      let (⟨x,y⟩,rot) := sol.pieceIdx i
      h.putStrLn s!"{i} {x} {y} {rot}"
  )

def BoardSol.readSolution (filename : System.FilePath)
                 (ts : TileSet size (Color.withBorder b c))
               : IO (BoardSol ts) := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )

  have parseLine : String → IO (Fin _ × Fin _ × Fin _ × Fin 4) := fun line => do
    match line.splitOn " " with
    | [t, x, y, r] => (
      match (t.toNat?, x.toNat?, y.toNat?, r.toNat?) with
      | (some t, some x, some y, some r) =>
        if ht : t ≥ size*size then
          panic! s!"Tile index out of range: {line}"
        else if hx : x ≥ size then
          panic! s!"Row {x} out of range: {line}"
        else if hy : y ≥ size then
          panic! s!"Col {y} out of range: {line}"
        else if hr : r ≥ 4 then
          panic! s!"Rotation {r} out of range: {line}"
        else pure (
          ⟨t,Nat.not_ge_eq _ _ ▸ ht⟩,
          ⟨x,Nat.not_ge_eq _ _ ▸ hx⟩,
          ⟨y,Nat.not_ge_eq _ _ ▸ hy⟩,
          ⟨r, by rw [Nat.not_ge_eq] at hr; exact hr⟩)
      | _ => panic! s!"Could not parse integers on line: {line}"
    )
    | _ => panic! s!"Incorrectly formatted sol line: {line}"

  let data ← do
    let lines :=
      contents.splitOn "\n"
      |>.map (·.trim) |>.filter (fun l => !(l.length = 0 || l.startsWith "c"))
    let parsed ← lines.mapM parseLine 
    pure <| parsed.foldl (init := Std.HashMap.empty) (fun map (t,loc) => map.insert t loc)

  let array ← Array.initM (size*size) (fun i => do
    match data.find? i with
    | none => panic! s!"Piece {i} is missing from solution"
    | some (x,y,r) => pure (⟨x,y⟩,r))
  have : array.size = size*size := sorry
  return ⟨(array[this.symm ▸ ·])⟩

def BoardSol.toTileBoard {ts : TileSet size (Color.withBorder b c)}
                          (sol : BoardSol ts)
    : IO (TileBoard size (Color.withBorder b c)) := do
  let mut temp_board :=
    Array.init size (fun _ => Array.init size (fun _ => none))
  for t in List.fins _ do
    let (⟨x,y⟩,r) := sol.pieceIdx t
    temp_board :=
      temp_board.set! y (temp_board[y]!.set! x (some <| ts.tiles[ts.h_ts.symm ▸ t].rotln r))

  let board := Array.init size (fun y =>
    Array.init size (fun x =>
      match temp_board[y]![x]! with
      | some t => t
      | none => panic! "Incomplete solution loaded"
    )
  )

  let tb : TileBoard size (Color.withBorder b c) := {
    board := board
    board_size := by simp
  }
  return tb

def TileBoard.toBoardSol (tb : TileBoard size (Color.withBorder b c))
  : Σ ts : TileSet size (Color.withBorder b c), BoardSol ts :=
  let withIdx : Array (SquareIndex size × Tile _) :=
    (Array.init size fun i => Array.init size fun j =>
      (⟨i,j⟩,tb.board[tb.board_size.1.symm ▸ i][(tb.board_size.2 _ _).symm ▸ j])
    ).flatten
  have : withIdx.size = size*size := sorry
  ⟨ ⟨withIdx.map (·.2) |>.toList, sorry⟩
  , ⟨fun idx => (withIdx[this.symm ▸ idx].1, 0)⟩
  ⟩

/- Randomly rotate the tiles, and mix up their order -/
def BoardSol.scramble {ts : TileSet size (Color.withBorder b c)} (sol : BoardSol ts)
  : IO ((ts : TileSet size (Color.withBorder b c)) × BoardSol ts) := do
  /- Rotate the pieces -/
  let rotated ← ts.tiles.enum'.mapM (fun (i, tile) => do
    let rot ← IO.rand 0 3
    let rot' : Fin 4 := ⟨rot, sorry⟩
    /- og index, rotation vs og, rotated tile -/ 
    return (ts.h_ts ▸ i, rot', tile.rotln rot'))
  /- Randomly permute the corners/sides/centers -/
  let corners ← rotated.filter (·.2.2.isCorner) |> IO.randPerm
  let sides   ← rotated.filter (·.2.2.isSide)   |> IO.randPerm
  let centers ← rotated.filter (·.2.2.isCenter) |> IO.randPerm
  /- Recombine -/
  have all := corners.toArray ++ sides ++ centers
  have h_all : all.size = size * size := sorry
  /- Tileset -/
  let tiles := all.toList.map (·.2.2)
  have h_tiles : tiles.length = size * size := by simp [h_all]
  /- solution -/
  let sol := Array.init (size*size) (fun i =>
    let (old_i, rot, tile) := all[h_all.symm ▸ i]
    let (pos, old_rot) := sol.pieceIdx old_i
    (pos,rot+old_rot))
  return ⟨⟨tiles, h_tiles⟩, ⟨(sol[·])⟩⟩


def SolvePuzzle.solve (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : Option (DiamondBoard size (Option (Color.withBorder b c))) :=
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  SATSolve.solve enc (pVars ++ dVars)
  |>.2.getAssn?.map fun assn =>
  decodeDiamonds tsv assn

/-- Find all solutions -/
def SolvePuzzle.solveAll (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  (termCond : Option (IO Bool) := none)
  : IO (List (DiamondBoard size (Option (Color.withBorder b c)))) := do
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  let sols : IO.Ref (List _) ← IO.mkRef []
  SATSolve.allSols enc (pVars ++ dVars) (varsToBlock := dVars)
    (termCond := termCond)
    (perItem := fun assn => do
      sols.modify (decodeDiamonds tsv assn :: ·))
  return ←sols.get
