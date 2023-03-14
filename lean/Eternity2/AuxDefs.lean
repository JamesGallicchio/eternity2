import Std
import LeanSAT

def IO.asTaskTimeout (time : Nat) (t : IO α) : IO (Except Unit α) :=
  show IO _ from do
  let task : Task (Except IO.Error (Except Unit α)) ←
    IO.asTask (do
      let a ← t
      return .ok a)
  let sleep : Task (Except IO.Error (Except Unit α)) ←
    IO.asTask (do
      IO.sleep time.toUInt32
      return .error ())
  let res ← IO.waitAny [task, sleep]
  let res ← IO.ofExcept res
  return res

 
def Log (m) [Monad m] [MonadLiftT IO m] (α) := IO.FS.Handle → m α

namespace Log
variable {m} [Monad m] [MonadLiftT IO m]

instance : Monad (Log m) where
  pure a := fun _ => pure a
  bind la f := fun logfile =>
    bind (la logfile) (fun a => f a logfile)

instance : MonadLift m (Log m) where
  monadLift ma := fun _ => ma

private def write (type : String) (s : String) : Log m Unit :=
  fun logfile => do
  let time ← (IO.monoMsNow : IO _)
  let ms := toString <| time % 1000
  logfile.putStrLn s!"[{time / 1000}.{"".pushn '0' (3-ms.length) ++ ms}] {type}: {s}"
  logfile.flush

def info : String → Log m Unit := write "INFO"
def warn : String → Log m Unit := write "WARN"
def error : String → Log m Unit := write "ERROR"

def run (logfile : IO.FS.Handle) (la : Log m α) : m α := la logfile
def getHandle : Log m IO.FS.Handle := λ path => pure path

instance [Monad m] [Monad n] [MonadLift m n] : MonadLift (Log m) (Log n) where
  monadLift mla := fun handle => liftM <| Log.run handle mla

instance [Monad m] [ForIn m ρ α] : ForIn (Log m) ρ α where
  forIn r acc f := fun handle => ForIn.forIn r acc (f · · handle)

end Log


def LeanSAT.Encode.EncCNF.State.cleanup : State → State × (Var → Var)
| {nextVar, clauses, names, varCtx} =>
  let usedVars :=
    clauses.foldl
      (fun set clause =>
        clause.lits.foldl
          (fun set lit =>
            set.insert lit.var ())
          set)
      (Std.HashMap.empty)

  let (varRemap, namesRemap, nextVarRemap) := Id.run do
    let mut varRemap : Std.HashMap Var Var := .empty
    let mut namesRemap : Std.HashMap Var String := .empty
    let mut nextVarRemap := 0
    for i in [0:nextVar] do
      if usedVars.contains i then
        varRemap := varRemap.insert i nextVarRemap
        if names.contains i then
          namesRemap := namesRemap.insert nextVarRemap (names.find! i)
        nextVarRemap := nextVarRemap.succ
    return (varRemap, namesRemap, nextVarRemap)

  let clausesRemap := clauses.map (⟨·.lits.map (fun
    | .pos v => .pos <| varRemap.find! v
    | .neg v => .neg <| varRemap.find! v
    )⟩)

  ( { nextVar := nextVarRemap
      names := namesRemap
      clauses := clausesRemap
      varCtx := varCtx}
  , varRemap.find! )

def List.pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], _ => []
  | a :: l, H => f a (H a (List.Mem.head _)) :: pmap f l (fun a h => H a (List.Mem.tail _ h))

def List.attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l fun _ => id

@[simp] theorem List.length_pmap : List.length (List.pmap f L h) = List.length L := by
  induction L with
  | nil => simp [pmap]
  | cons x xs ih => simp [pmap, ih]

def RandomM (τ) := ∀ g, RandomGen g → StateM g τ

namespace RandomM

instance [RandomGen g] : Monad RandomM where
  pure a    := λ _ _ => pure a
  bind r f  := λ G R => bind (r G R) (fun a => f a G R)

def run [R : RandomGen G] (g : G) (r : RandomM τ) : τ × G :=
  StateT.run (r G R) g

instance : MonadLift RandomM IO where
  monadLift r := do
    let gen ← IO.stdGenRef.get
    let (res, seed) := run gen r
    IO.stdGenRef.set seed
    return res

@[inline]
def randIndep (p1 : RandomM α) : RandomM α :=
  λ _ R r => let (r1,r2) := RandomGen.split r
             let (a,_) := p1 _ R r1
             (a,r2)

@[inline]
def randFin (n : Nat) (hn : n > 0 := by trivial) : RandomM (Fin n) :=
  λ G R g =>
    let (res, g) := @randNat G R g 0 n.pred
    if h : res < n then
      (⟨res, h⟩, g)
    else
      have : Inhabited (Fin n × G) := ⟨⟨⟨0,hn⟩, g⟩⟩
      panic! s!"randFin wrong: n={n}, res={res}"

/- Generate a random permutation of the list.
Implementation is quadratic in length of L. -/
def randPerm (L : List α) : RandomM (List α) :=
  randPermTR L [] 0
where randPermTR (L acc n) := do
  match L with
  | [] => return acc
  | x::xs =>
    let idx ← RandomM.randFin (n+1) (Nat.zero_lt_succ _)
    let acc' := acc.insertNth idx x
    randPermTR xs acc' (n+1)

end RandomM

def List.parMap (jobs : List α) (f : α → IO β) : IO (List β) := do
  let tasks ← jobs.mapM (IO.asTask <| f ·)
  let res ← IO.mapTasks (·.mapM IO.ofExcept) tasks
  return ← IO.ofExcept res.get

def List.removeOne : List α → List (α × List α)
| [] => []
| x::xs => (x,xs) :: (xs.removeOne.map (fun (x',xs') => (x', x::xs')))

def List.removeOne' : (L : List α) → List (α × { L' : List α // L'.length < L.length })
| [] => []
| x::xs => (x,⟨xs, by simp⟩) :: (xs.removeOne'.map (fun (x',⟨xs',h⟩) => (x', ⟨x::xs', Nat.succ_lt_succ h⟩)))

def List.minBy [LT β] [DecidableRel (@LT.lt β _)] (f : α → β) (L : List α) : Option α :=
  L.foldl (fun o a =>
    let b := f a
    match o with
    | none => some (a, f a)
    | some (a',b') =>
      if b < b' then
        some (a,b)
      else
        some (a',b')) none
  |>.map (·.1)
