import Eternity2.Plots.BoardSuite
import Eternity2.Plots.SolveAndOutput
import LeanSAT.Solver

namespace Eternity2

def solveBoardSuite [LeanSAT.Solver IO] (n : Nat) (suite : System.FilePath) : Log IO Unit := do
  Log.info s!"Loading board suite from directory {suite}"
  let bs ← BoardSuite.ofDirectory suite
  Log.info s!"Board suite loaded with {bs.boards.size} puzzles"
  
  -- sort by board size (increasing), then by number of center colors (decreasing)
  let bs := bs.boards.insertionSort (fun x y =>
    x.size < y.size ||
      x.size = y.size && x.colors.center.length > y.colors.center.length)

  let handle ← Log.getHandle
  
  -- solve each board in parallel, using `n` threads
  let (_ : List Unit) ← WorkQueue.launch n bs.toList (fun bdir => do
    Log.run handle <| Log.info s!"Board {bdir.puzFile}: starting"
    try (do
      Log.run handle <| solveAndOutput bdir {}
   ) catch
    | e => (do
      let msg := e.toString.dropWhile (·.isWhitespace) |>.takeWhile (· ≠ '\n')
      Log.run handle <| Log.error s!"Board {bdir.puzFile}:\n\t{msg}"
    )
  )
