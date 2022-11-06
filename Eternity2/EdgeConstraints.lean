import Eternity2.TileSet
import Eternity2.CardinalityHelpers
import Eternity2.SATSolve

namespace Eternity2.Constraints

open Std EncCNF

/- Implement constraints as described in Heule 2008 -/

structure SquareIndex (size : Nat) where
  row : Fin size
  col : Fin size

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
private def middleFins (psize : Nat) : List (Fin psize.succ) :=
  forIn (m := Id) [1:psize] [] (fun x y => .yield (.ofNat x :: y))

def corners (psize : Nat) : List (SquareIndex psize.succ) :=
  [ ⟨0,0⟩,
    ⟨0, psize, Nat.lt_succ_self _⟩,
    ⟨maxIdx, 0⟩,
    ⟨maxIdx, ⟨psize, Nat.lt_succ_self _⟩⟩
  ]

def borders (psize : Nat) : List (SquareIndex psize.succ) :=
  middleFins psize |>.bind fun i =>
    [ (⟨0, i⟩),
      (⟨i, 0⟩),
      (⟨maxIdx, i⟩),
      (⟨i, maxIdx⟩) ]

def center (psize : Nat) : List (SquareIndex psize.succ) :=
  middleFins psize |>.bind fun x =>
    middleFins psize |>.map fun y =>
      ⟨x,y⟩

end SquareIndex

inductive DiamondIndex (psize : Nat) where
/-- col refers to the left triangle's column -/
| horiz (row : Fin psize.succ) (col : Fin psize)
/-- row refers to the top triangle's row -/
| vert (row : Fin psize) (col : Fin psize.succ)

def DiamondIndex.toFin : DiamondIndex psize → Fin (2 * (psize * psize.succ))
| horiz ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (psize + psize.succ) + j, by sorry⟩
| vert ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (psize + psize.succ) + psize + j, by sorry⟩

structure TileSetVariables (psize : Nat) (colors : Nat) where
  ts : TileSet
  h_ts : ts.tiles.length = psize.succ * psize.succ
  h_ts_uniq : ts.unique
  piece_vars : Fin (psize.succ * psize.succ) → SquareIndex psize.succ → Var
  diamond_vars : DiamondIndex psize → Fin colors → Var

def tileIndices (psize : Nat) : List (Fin (psize.succ * psize.succ)) :=
  forIn (m := Id) [0:psize.succ * psize.succ] [] (fun x y => .yield (.ofNat x :: y))

def mkVars (ts : TileSet) (psize colors : Nat)
  (h_ts : ts.tiles.length = psize.succ * psize.succ)
  (h_uniq : ts.unique)
  : EncCNF (TileSetVariables psize colors) := do
  let pvs ← EncCNF.mkVarBlock "x" [psize.succ*psize.succ, psize.succ*psize.succ]
  let dvs ← EncCNF.mkVarBlock "y" [2 * (psize * psize.succ), colors]
  return ⟨ts, h_ts, h_uniq, (pvs[·][·.toFin]), (dvs[·.toFin][·])⟩

def pieceVarConstraints (tsv : TileSetVariables psize colors) : EncCNF Unit := do
  let cornerTiles := tileIndices psize |>.filterMap (fun i =>
        let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
        let tile := tsv.ts.tiles[i']
        if tile.isCorner then some i else none)
  let borderTiles := tileIndices psize |>.filterMap (fun i =>
        let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
        let tile := tsv.ts.tiles[i']
        if tile.isBorder then some i else none)
  let centerTiles := tileIndices psize |>.filterMap (fun i =>
        let i' : Fin tsv.ts.tiles.length := ⟨i.val, by rw [tsv.h_ts]; exact i.isLt⟩
        let tile := tsv.ts.tiles[i']
        if tile.isCenter then some i else none)

  /- Each square has a tile -/
  for q in SquareIndex.corners psize do
    EncCNF.addClause (cornerTiles.map (tsv.piece_vars · q))

  for q in SquareIndex.borders psize do
    EncCNF.addClause (borderTiles.map (tsv.piece_vars · q))

  for q in SquareIndex.center psize do
    EncCNF.addClause (centerTiles.map (tsv.piece_vars · q))

  /- Each tile has a square -/
  for p in cornerTiles do
    EncCNF.addClause (SquareIndex.corners psize |>.map (tsv.piece_vars p ·))

  for p in borderTiles do
    EncCNF.addClause (SquareIndex.borders psize |>.map (tsv.piece_vars p ·))

  for p in centerTiles do
    EncCNF.addClause (SquareIndex.center psize |>.map (tsv.piece_vars p ·))


