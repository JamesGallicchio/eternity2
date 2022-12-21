
open System
-- asAS
def calcMedians (input : FilePath) (output : FilePath) : IO Unit := do
  let inText ← IO.FS.readFile input
  match inText.splitOn "\n" with
  | "size,colors,iter,runtime(ms)" :: data =>
    let outDat :=
      data.filter (!·.isEmpty)
        |>.map (fun line =>
          match line.splitOn "," |>.map String.toNat? with
          | [some a,some b,some c, some d] => (a,b,c,d)
          | _ => panic! s!"wrong: `{line}`"
        )
        |> List.toArray
        |>.insertionSort (fun
          | (s1,c1,_,_), (s2,c2,_,_) => s1 < s2 || s1 = s2 && c1 < c2
          )
        |>.toList
        |>.groupBy (fun
          | (s1,c1,_,_), (s2,c2,_,_) => s1 = s2 && c1 = c2
          )
        |>.map (fun group =>
          let (s,c,_,_) := group.head!
          --let avg := group.map (fun (_,_,_,t) => t) |>.foldl (·+·) 0 |> (· / group.length)
          let median :=
            group.toArray.map (·.2.2.2 : Nat × Nat × Nat × Nat → Nat)
              |>.insertionSort (· < ·)
              |> (fun a => a[a.size/2]!)
          s!"{s},{c},median,{median}"
          --s!"{s},{c},avg,{avg}"
          )
    IO.FS.withFile output .write (fun handle => do
      handle.putStrLn "size,colors,iter,runtime(ms)"
      for line in outDat do
        handle.putStrLn line
    )
  | _ => panic! "bad"

--#eval calcMedians "../log/test_times_with_sol_sign_1hr.csv" "../log/test_times_with_sol_sign_1hr_medians.csv"