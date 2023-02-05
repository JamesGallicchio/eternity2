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
