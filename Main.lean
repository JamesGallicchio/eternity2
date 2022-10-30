import Eternity2

def main : IO Unit := do
  let b ← DiamondBoard.gen_dboard 6 9
  let t := DiamondBoard.dboard_to_tboard b true
  IO.print t

#eval main
