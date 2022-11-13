import Eternity2.Board
import Eternity2.SATSolve.CardinalityHelpers

namespace Eternity2.Constraints

open EncCNF

/-- Given a list of (potentially unsigned) tiles, encode that
for each color `0 < c ≤ k`, the `c`-colored triangles must be
half `+` and half `-`.
-/
def colorCardConstraints(L : List Tile) (k : Nat) : EncCNF (List (Tile × Var)) := do
  let varList ← L.foldrM (fun t rest => do
    let var ← mkVar s!"tile_sign{t.up}{t.right}{t.down}{t.left}"
    return (t,var) :: rest
    ) []
  for c in [1:k+1] do
    let c := some c
    let border_cVars := varList.bind (fun (t,var) =>
      t.getBorderColors.filter (fun c' => c = c')|>.map (fun _ => var))
    let center_cVars := varList.bind (fun (t,var) =>
      t.getCenterColors.filter (fun c' => c = c')|>.map (fun _ => var))
    let border_pos : Array Literal := Array.mk <| border_cVars.map (⟨·,false⟩)
    let center_pos : Array Literal := Array.mk <| center_cVars.map (⟨·,false⟩)
    assert! (border_pos.size % 2 = 0) -- handshake lemma :)
    assert! (center_pos.size % 2 = 0) -- also handshake lemma :)
    equalK border_pos (border_pos.size / 2)
    equalK center_pos (center_pos.size / 2)

  -- Break polarity symmetry by assigning first tile to positive
  for (_, v) in varList.head? do
    addClause [v]

  return varList
