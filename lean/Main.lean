import Cred

open Cred.Foundation.Structure

/-- Standalone certificate checker: runs the real-free `checkBool` on a concrete
    certificate and prints the verdict. The executable trusted base is the
    computable `checkBool`; its agreement with the verified checker
    (`checkBool_eq_isSome`) and the soundness bridge (`checkBool_true_sound`) are
    proved in Lean, but the binary itself materializes no reals. -/
def main : IO Unit := do
  IO.println "Cred standalone certificate checker (real-free executable)."
  IO.println s!"checkBool exampleTree = {checkBool exampleTree}"
