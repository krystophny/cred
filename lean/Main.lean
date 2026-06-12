import Cred

open Cred.Foundation.Structure

/-- The executable trusted base is the real-free `checkBool` / `checkCodeNat`
    path: the checker runs on a natural-number Goedel code of a foundation
    certificate, materializes no reals, and its agreement with the verified
    checker (`checkBool_eq_isSome`) and soundness (`checkCodeNat_sound`) are
    proved in Lean. The certificate format is a single decimal code per file. -/

def usage : String :=
  "cred: real-free foundation certificate checker\n\n" ++
  "usage:\n" ++
  "  cred check FILE            check the certificate code in FILE\n" ++
  "                             exit 0 if accepted, 1 if rejected, 2 on bad input\n" ++
  "  cred check --explain FILE  check and print a human-readable verdict\n" ++
  "  cred examples              print a bundled example certificate code\n" ++
  "  cred                       run the checker on the bundled example\n"

/-- Read a file and parse its trimmed contents as a decimal certificate code.
    A missing or unreadable file, or non-numeric contents, yields `none`. -/
def readCode (path : String) : IO (Option Nat) := do
  try
    let contents ← IO.FS.readFile path
    pure contents.trim.toNat?
  catch _ =>
    pure none

/-- Check the code in `path`. Returns the process exit code: 0 accepted,
    1 rejected, 2 on malformed input. -/
def runCheck (path : String) (explain : Bool) : IO UInt32 := do
  match ← readCode path with
  | none =>
    IO.eprintln s!"error: {path} is missing or does not hold a decimal certificate code"
    pure 2
  | some code =>
    if explain then IO.println (explainCode code)
    if checkCodeNat code then
      unless explain do IO.println "accepted"
      pure 0
    else
      unless explain do IO.println "rejected"
      pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", path] => runCheck path false
  | ["check", "--explain", path] => runCheck path true
  | ["examples"] =>
    IO.println "# bundled example certificate (forallElim)."
    IO.println "# save the number below to a file and run: cred check FILE"
    IO.println (toString exampleCode)
    pure 0
  | [] =>
    IO.println "Cred standalone certificate checker (real-free executable)."
    IO.println s!"checkBool exampleTree   = {checkBool exampleTree}"
    IO.println s!"checkCodeNat exampleCode = {checkCodeNat exampleCode}"
    IO.println ""
    IO.print usage
    pure 0
  | _ =>
    IO.eprint usage
    pure 2
