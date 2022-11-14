import Eternity2.EdgeConstraints
import Eternity2.Board
import Eternity2.SATSolve

namespace Eternity2.SolvePuzzle

open Constraints EncCNF

def decodeDiamondBoard (tsv : Constraints.TileSetVariables psize colors)
  (assn : Std.HashMap Var Bool) : DiamondBoard psize.succ :=
  {
    board := Array.init (2*psize.succ - 1) (fun ⟨idx,hidx⟩ =>
      let r := idx / 2
      if idx % 2 = 0 then
        Array.init psize (fun c =>
          dbgTrace s!"{r} {c}" fun () =>
          ⟨ List.fins colors
            |>.find? (fun col =>
              assn.findD (tsv.diamond_vars (.horz ⟨r,sorry⟩ c) col) false)
            |>.map (fun c => c.val)
          , sorry⟩)
      else
        Array.init psize.succ (fun c =>
          ⟨ List.fins colors
            |>.find? (fun col =>
              assn.findD (tsv.diamond_vars (.vert ⟨r,sorry⟩ c) col) false)
            |>.map (fun c => c.val)
          , sorry⟩))
    boardsize := by simp
    rowsize := by
      sorry
    isFinalized := true
    finalize := sorry
  }


def decodeTileBoard (tsv : Constraints.TileSetVariables psize colors)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : TileBoard psize.succ := {
    board :=
      Array.init _ (fun i =>
        Array.init _ (fun j =>
          List.fins _
            |>.find? (fun p => s.find? (tsv.piece_vars p ⟨i,j⟩) |>.get!)
            |>.map (tsv.tiles[·]!)
            |>.getD ⟨none,none,none,none,none⟩
      ))
    board_size := sorry
    isFinalized := true
    finalize := sorry
  }
  tb

def solve (enc : EncCNF.State) (tsv : TileSetVariables psize colors)
  : Option (DiamondBoard psize.succ) :=
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  SATSolve.solve enc (pVars ++ dVars)
  |>.map fun (_, assn) =>
  decodeDiamondBoard tsv assn

def solveAll (enc : EncCNF.State) (tsv : TileSetVariables psize colors)
  : IO (List (DiamondBoard psize.succ)) := do
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  let sols : IO.Ref (List _) ← IO.mkRef []
  SATSolve.allSols enc (pVars ++ dVars) (perItem := fun assn => do
    sols.modify (decodeDiamondBoard tsv assn :: ·)
  )
  return ←sols.get
