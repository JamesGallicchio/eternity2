import Eternity2.DiscrSearch
import Eternity2.Puzzle.BoardSol
import Eternity2.Puzzle.SignSol
import Eternity2.Puzzle.Encoding
import Eternity2.Puzzle.SolvePuzzle
import LeanSAT.Encode.EncCNF
import LeanSAT.Solver.Basic

namespace Eternity2

open LeanSAT Encode

structure SignCorr where
  numSame : Nat
  numDiff : Nat
deriving Inhabited, Repr

instance : ToString SignCorr := ⟨fun ⟨same,diff⟩ => s!"same: {same}, diff: {diff}"⟩

def SignCorr.mag : SignCorr → Nat
| {numSame, numDiff} => max (numSame - numDiff) (numDiff - numSame)

def SignCorrs (size : Nat) := Fin (size*size) → Fin (size*size) → SignCorr

instance : Inhabited (SignCorrs size) := ⟨λ _ _ => default⟩

class SignCorrSolver (m) [Monad m] where
  getCorrs {size s} {ts : TileSet size (Tile (Color.WithBorder s))}
    (tsv : Encoding.TileSetVariables ts) (enc : EncCNF.State) : m (SignCorrs size)

def SignCorrSolver.ofModelSample [Monad m] [Solver.ModelSample m]
      (samples := 1000) : SignCorrSolver m where
  getCorrs {size _ _} tsv enc :=
  open Notation in do

  let samples ← Solver.ModelSample.modelSample enc.toFormula samples
  let sampleCount := samples.length

  let mut corrs := Std.HashMap.empty
  let mut undefs := 0
  for p1 in List.fins (size*size) do
    for p2 in List.fins (size*size) do
      if p1 > p2 then
        continue
      let undef_count := samples.countp (fun assn =>
        assn.find? (tsv.sign_vars p1) = none || assn.find? (tsv.sign_vars p2) = none)
      let same_count := samples.countp (fun assn =>
        assn.find? (tsv.sign_vars p1) = assn.find? (tsv.sign_vars p2))
      let diff_count := sampleCount - same_count - undef_count
      undefs := undefs + undef_count
      corrs := corrs.insert (p1,p2) ⟨same_count,diff_count⟩
  if undefs > 0 then
    dbgTrace s!"undefs: {undefs}" fun () => pure ()
  return (λ p1 p2 =>
    if p1 ≤ p2 then corrs.find! (p1,p2) else corrs.find! (p2,p1)
  )

def SignCorrs.inBiasOrder (sc : SignCorrs size) : List (Fin (size*size) × Fin (size*size) × SignCorr) :=
  if h:size<2 then [] else
  let allPairs := (List.fins _).product (List.fins _) |>.filter (fun (x,y) => x ≠ y)
  have : allPairs ≠ [] := by
    cases size <;> simp at *
    next size =>
    cases size <;> simp at *
    rw [Nat.succ_mul, Nat.add_succ, Nat.succ_mul, Nat.add_succ]
    simp [List.fins_succ, List.product, List.filter]
    split <;> simp
    next h =>
    cases h
  let (x,y) :=
    allPairs.maxBy (fun (i,j) => (sc i j).mag)
    |>.get (by unfold Option.isSome; split <;> simp; rw [List.maxBy_eq_none] at *; contradiction)
  let res := aux (List.fins _ |>.filter (fun i => i ≠ x ∧ i ≠ y)) [x,y] (by simp) [(x,y,sc x y)]
  res.reverse
where aux toAssign assigned (h : assigned ≠ []) acc :=
  match
    toAssign.removeOne'.maxByMap (fun (i,_) =>
      let (j, sc) := assigned.maxByMap (fun j => let sc := sc i j; (sc, sc.mag))
                      |>.get (by simp; cases assigned <;> simp [List.isEmpty] at *)
      ((j, sc), sc.mag))
  with
  | none => acc
  | some ((i,toAssign),j,sc) =>
  have := toAssign.property
  aux toAssign.val (i::assigned) (by simp) ((i,j,sc) :: acc)
termination_by aux toAssign _ _ _ => toAssign.length
