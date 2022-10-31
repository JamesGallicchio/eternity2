import Eternity2.Board
import Eternity2.CardinalityHelpers

namespace Eternity2.ColorCardinality

open EncCNF

/-- Given a list of (potentially unsigned) tiles, encode that
for each color `0 < c ≤ k`, the `c`-colored triangles must be
half `+` and half `-`.
-/
def colorCardConstraints (L : List Tile) (k : Nat) : EncCNF (List (Tile × Var)) := do
  let varList ← L.foldrM (fun t rest => do
    let var ← mkVar s!"tile_sign{t.up}{t.right}{t.down}{t.left}"
    return (t,var) :: rest
    ) []
  for c in [1:k+1] do
    let cVars := varList.bind (fun (t,var) =>
      [ if t.up    = c then [var] else []
      , if t.down  = c then [var] else []
      , if t.left  = c then [var] else []
      , if t.right = c then [var] else []
      ].join)
    let pos : Array Literal := Array.mk <| cVars.map (⟨·,false⟩)
    assert! (pos.size % 2 = 0) -- handshake lemma :)
    let neg : Array Literal := pos.map (·.not)
    equalK pos (pos.size / 2)
    equalK neg (pos.size / 2)

  return varList
