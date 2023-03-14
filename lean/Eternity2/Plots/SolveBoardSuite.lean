import Eternity2.Plots.BoardSuite
import Eternity2.Plots.SolveAndOutput
import LeanSAT.Solver

namespace Eternity2

def solveBoardSuite [LeanSAT.Solver IO] (suite : BoardSuite) (parallelize : Bool := false) : Log IO Unit := do  
  -- look only at boards that are not fully solved yet
  let unsolved := suite.boards.filter (!·.allSols)

  Log.info s!"{suite.boards.size - unsolved.size} boards already solved, {unsolved.size} to be solved"

  -- sort by board size (increasing), then by number of center colors (decreasing)
  let bs := unsolved.insertionSort (fun x y =>
    x.size < y.size ||
      x.size = y.size && x.colors.center.length > y.colors.center.length)

  let handle ← Log.getHandle
  
  -- solve each board in parallel
  let (_ : List Unit) ← bs.toList.parMap (fun bdir => do
    Log.run handle <| Log.info s!"Board {bdir.puzFile}: starting"
    try
      Log.run handle <| solveAndOutput bdir (parallelize := parallelize) {}
    catch e =>
      let msg := e.toString.dropWhile (·.isWhitespace) |>.takeWhile (· ≠ '\n')
      Log.run handle <| Log.error s!"Board {bdir.puzFile}:\n\t{msg}"
  )
