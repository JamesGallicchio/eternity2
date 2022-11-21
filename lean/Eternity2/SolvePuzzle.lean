import Eternity2.EdgeConstraints
import Eternity2.Board
import Eternity2.SATSolve

namespace Eternity2.SolvePuzzle

open Constraints EncCNF

def decodeDiamondBoard (tsv : Constraints.TileSetVariables size b c)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : DiamondBoard size (Option (Color.withBorder b c)) := {
    board :=
      Array.init _ (fun k =>
          List.fins _
            |>.find? (fun color => s.find? (tsv.diamond_vars (.ofFin k) color) |>.get!)
      )
    boardsize := by simp
  }
  tb

def decodeTileBoard (tsv : Constraints.TileSetVariables size b c)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : TileBoard size (Option (Color.withBorder b c)) := {
    board :=
      Array.init _ (fun i =>
        Array.init _ (fun j =>
          List.fins _
            |>.find? (fun p => s.find? (tsv.piece_vars p ⟨i,j⟩ ) |>.get!)
            |>.map (fun p => tsv.tiles[tsv.h_ts.symm ▸ p].map (some ·))
            |>.getD ⟨none, none, none, none⟩
        )
      )
    board_size := by simp
  }
  tb

def solve (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : Option (DiamondBoard size (Option (Color.withBorder b c))) :=
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  SATSolve.solve enc (pVars ++ dVars)
  |>.map fun (_, assn) =>
  decodeDiamondBoard tsv assn

def solveAll (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : IO (List (DiamondBoard size (Option (Color.withBorder b c)))) := do
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  let sols : IO.Ref (List _) ← IO.mkRef []
  SATSolve.allSols enc (pVars ++ dVars) (varsToBlock := dVars) (perItem := fun assn => do
    -- IO.FS.withFile "test.txt" .append (fun h => do
    --   h.putStrLn
    --     <| toString
    --     <| (decodeDiamondBoard tsv assn).tileBoard.mapColors
    --           (fun | none => " " | some a => toString a)
    --   h.putStrLn ""
    -- )

    -- IO.FS.withFile "test-p.txt" .append (fun h => do
    --   h.putStrLn
    --     <| toString
    --     <| (decodeTileBoard tsv assn).mapColors
    --           (fun | none => " " | some a => toString a)
    --   h.putStrLn ""
    -- )

    sols.modify (decodeDiamondBoard tsv assn :: ·)
  )
  return ←sols.get
