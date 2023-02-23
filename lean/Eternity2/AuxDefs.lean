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

instance [Monad m] [Monad n] [MonadLift m n] : MonadLift (Log m) (Log n) where
  monadLift mla := fun handle => liftM <| Log.run handle mla

end Log


def LeanSAT.Encode.EncCNF.State.cleanup : State → State
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

  { nextVar := nextVarRemap
    names := namesRemap
    clauses := clausesRemap
    varCtx := varCtx}

def List.pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], _ => []
  | a :: l, H => f a (H a (List.Mem.head _)) :: pmap f l (fun a h => H a (List.Mem.tail _ h))

def List.attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l fun _ => id

@[simp] theorem List.length_pmap : List.length (List.pmap f L h) = List.length L := by
  induction L with
  | nil => simp [pmap]
  | cons x xs ih => simp [pmap, ih]

def RandomM (τ) := ∀ g [RandomGen g], StateM g τ

instance [RandomGen g] : Monad RandomM where
  pure a    := λ _ => pure a
  bind r f  := λ G => bind (r G) (fun a => f a G)

def RandomM.run [RandomGen G] (g : G) (r : RandomM τ) : τ × G :=
  StateT.run (r G) g

def RandomM.randFin (n : Nat) : n > 0 → RandomM (Fin n) :=
  λ hn G R g =>
    let (res, g) := @randNat G R g 0 n
    if h : res < n then
      (⟨res, h⟩, g)
    else
      have : Inhabited (Fin n × G) := ⟨⟨⟨0,hn⟩, g⟩⟩
      panic! s!"randFin wrong: n={n}, res={res}"
