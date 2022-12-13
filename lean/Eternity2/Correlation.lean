import Eternity2.Puzzle

open Eternity2

def getCorrs (enc : EncCNF.State)
             (tsv : Constraints.TileSetVariables size b c)
             (iters timeout : Nat)
           : IO (List (SquareIndex size × SquareIndex size × Nat × Nat)) := do
  let signsols ← (do
    let mut signsols ← IO.mkRef []
    for i in [0:iters] do
      let enc ← enc.scramble
      let start ← IO.monoMsNow
      let count ← IO.mkRef 0
      let () ← SATSolve.allSols enc tsv.signVarList
        (termCond := some (do
          let now := (← IO.monoMsNow)
          let doTimeout := (start + timeout) < now
          if doTimeout then
            IO.println s!"timing out iteration {i} after finding {←count.get} sols"
            (←IO.getStdout).flush
          return doTimeout
          ))
        (perItem := fun assn => do
          count.modify (· + 1)
          signsols.modify (assn :: ·))
    signsols.get)

  let corrs :=
    SquareIndex.all size |>.bind fun p1 =>
    SquareIndex.all size |>.bind fun p2 =>
    let idx1 := SquareIndex.toFin p1
    let idx2 := SquareIndex.toFin p2
    if idx1 ≥ idx2 then []
    else [
      let sameCount :=
        signsols.countp (fun assn =>
          assn.find? (tsv.sign_vars idx1) == assn.find? (tsv.sign_vars idx2))
      let diffCount :=
        signsols.countp (fun assn =>
          assn.find? (tsv.sign_vars idx1) != assn.find? (tsv.sign_vars idx2))
      (p1, p2, sameCount, diffCount)
    ]
  return corrs

def runCorrelation (enc : EncCNF.State)
                   (tsv : Constraints.TileSetVariables size b c)
                   (iters timeout : Nat)
                   (assigned : List (SquareIndex size × SquareIndex size))
                   (piece_set : List (SquareIndex size))
                 : IO (Option (SquareIndex size × SquareIndex size × Nat × Nat)) := do
  let corrs ← getCorrs enc tsv iters timeout
  let guess :=
    corrs.foldl (fun acc (p1,p2,s,d) =>
      match acc with
      | none =>
        if !assigned.contains (p1,p2)
          &&( (piece_set.contains p1 && !piece_set.contains p2)
            ||(!piece_set.contains p1 && piece_set.contains p2)
            || piece_set.isEmpty )
        then some (p1,p2,s,d)
        else none

      | some (_,_,ms,md) =>
        if !assigned.contains (p1,p2)
          &&( (piece_set.contains p1 && !piece_set.contains p2)
            ||(!piece_set.contains p1 && piece_set.contains p2)
            || piece_set.isEmpty )
          && min s d < min ms md
        then some (p1,p2,s,d)
        else acc
    ) none
  return guess


partial def searchSpace (enc : EncCNF.State)
                (tsv : Constraints.TileSetVariables size b c)
                (iters timeout : Nat)
                (assigned : List (SquareIndex size × SquareIndex size))
                (piece_set : List (SquareIndex size))
                (rights : Nat)
                (fail : Unit → IO Unit)
              : IO Unit := do
  let guess ← runCorrelation enc tsv iters timeout assigned piece_set
  match guess with
  | none =>
    -- todo check whether we are at a sol, if we are return, otherwise call fc
    sorry
  | some (p1,p2,same,diff) =>
    let (p1v, p2v) := (tsv.sign_vars p1.toFin, tsv.sign_vars p2.toFin)
    let (enc_same, enc_diff) :=
        ( (·.2) <| EncCNF.run! enc do
            EncCNF.addClause [.not p1v, p2v]
            EncCNF.addClause [p1v, .not p2v]
        , (·.2) <| EncCNF.run! enc do
            EncCNF.addClause [p1v, p2v]
            EncCNF.addClause [.not p1v, .not p2v]
        )
    let (encl, encr) :=
      if same > diff then (enc_same, enc_diff) else (enc_diff, enc_same)

    let assigned'  := (p1, p2) :: assigned
    let piece_set' := p1 :: p2 :: piece_set

    if rights > 0 then
      searchSpace encr tsv iters timeout assigned' piece_set' (rights - 1)
        (fun () =>
          searchSpace encl tsv iters timeout assigned' piece_set' rights fail
        )
    else
      searchSpace encl tsv iters timeout assigned' piece_set' rights fail

partial def findCorrs (ts : TileSet size (Color.withBorder b c)) (iters timeout : Nat) : IO Unit := do
  match EncCNF.new? do
    let tsv ← Constraints.mkVars ts
    Constraints.colorCardConstraints tsv
    Constraints.signCardConstraints tsv
    if h:0 < size*size then EncCNF.addClause [tsv.sign_vars ⟨0,h⟩]
    return tsv
  with
  | .error s => panic! s!"failed to encode: {s}"
  | .ok (tsv, enc) =>
  let mut enc := enc
  let boardSols ← (do
    let mut boardSols ← IO.mkRef []
    match EncCNF.new? <| encodePuzzle ts {} with
    | .error s =>
      IO.println s!"aborting, failed to encode tileset. error:\n{s}"
    | .ok (tsv, enc) =>
      SATSolve.allSols enc
        (tsv.pieceVarList ++ tsv.diamondVarList)
        tsv.diamondVarList
        (perItem := fun assn => do
          let poses : Fin size → Fin size → SquareIndex size := fun i j =>
              let idx1 := SquareIndex.toFin ⟨i,j⟩
              match
                List.find?
                  (assn.find! <| tsv.piece_vars idx1 ·)
                  (SquareIndex.all size)
              with
              | some x => x
              | none =>
                letI : Inhabited (SquareIndex size) := (match size, i with | 0, i => i.elim0 | _+1, _ => ⟨⟨0,0⟩⟩)
                panic! "piece not placed?"
          boardSols.modify (poses :: ·)
        )
    return ←boardSols.get)

  IO.println ts
  IO.println ""

  for sol in boardSols do
    for i in List.fins _ do
      for j in List.fins _ do
        IO.print (sol i j)
        IO.print " "
      IO.println ""
    IO.println ""


  let mut lefts := 0
  let mut assigned := []
  let mut piece_set := []
  while true do
    let guess ← runCorrelation enc tsv iters timeout assigned piece_set

    match guess with
    | none =>
        break
    | some (p1,p2, same,diff) =>
      let pct := (Nat.toFloat <| min same diff) / (Nat.toFloat <| same + diff)
      let actSame :=
        boardSols.countp (fun placement =>
            let q1 := placement p1.1 p1.2
            let q2 := placement p2.1 p2.2
            (q1.row + q1.col + q2.row + q2.col : Nat) % 2 == 0)
      let actDiff :=
        boardSols.countp (fun placement =>
            let q1 := placement p1.1 p1.2
            let q2 := placement p2.1 p2.2
            (q1.row + q1.col + q2.row + q2.col : Nat) % 2 == 1)

      let (p1v, p2v) := (tsv.sign_vars p1.toFin, tsv.sign_vars p2.toFin)
      IO.println s!"({assigned.length})\t{p1} {p2}: {same}, {diff} ({pct*100}%); actual {actSame}, {actDiff}"
      -- if same > diff then
      if actSame > actDiff then
        IO.println s!"\tAssigning {p1}, {p2} to be the same.\t(matches {actSame} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause [.not p1v, p2v]
          EncCNF.addClause [p1v, .not p2v]

        if same > diff then lefts := lefts + 1
      else
        IO.println s!"\tAssigning {p1}, {p2} to be different.\t(matches {actDiff} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause [p1v, p2v]
          EncCNF.addClause [.not p1v, .not p2v]

        if same <= diff then lefts := lefts + 1
      assigned := (p1, p2) :: assigned
      piece_set := p1 :: p2 :: piece_set
  IO.println s!"Lefts {lefts} out of {assigned.length}"
