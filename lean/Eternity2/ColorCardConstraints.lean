import Eternity2.Board
import Eternity2.SATSolve.CardinalityHelpers

namespace Eternity2.Constraints

open EncCNF

/-- Given a list of tiles, encode that for each
border- or center-color, the `c`-colored triangles
must be half `+` and half `-`.
-/
def colorCardConstraints (L : List (Tile (Color.withBorder b c))) : EncCNF (List (Tile (Color.withBorder b c) × Var)) := do
  let varList ← L.foldrM (fun t rest => do
    let var ← mkVar s!"tile_sign{t.up}{t.right}{t.down}{t.left}"
    return (t,var) :: rest
    ) []

  for color in Color.borderColors ++ Color.centerColors do
    let cVars := varList.bind (fun (t,var) =>
      t.colors.filter (· = color) |>.map (fun _ => var))
    let pos : Array Literal := Array.mk <| cVars.map (⟨·,false⟩)
    assert! (pos.size % 2 = 0) -- handshake lemma :)
    equalK pos (pos.size / 2)

  return varList
