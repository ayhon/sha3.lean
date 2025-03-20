import Sha3.Spec
import Sha3.Utils
open Spec (Bit)

inductive Sha3FuncType where
| SHA3_224
| SHA3_256
| SHA3_384
| SHA3_512
| SHAKE128
| SHAKE256

instance: ToString Sha3FuncType where
  toString
  | .SHA3_224 => "SHA3_224"
  | .SHA3_256 => "SHA3_256"
  | .SHA3_384 => "SHA3_384"
  | .SHA3_512 => "SHA3_512"
  | .SHAKE128 => "SHAKE128"
  | .SHAKE256 => "SHAKE256"

def runPython(ty: Sha3FuncType)(S: String): IO String := do
  let args := #[
      "python",
      "sha3.py",
      toString ty,
      S
    ]
  let out ← IO.Process.output {
    cmd := "/usr/bin/env",
    args
  }
  if ¬ out.stderr.isEmpty then
    dbg_trace out.stderr
    dbg_trace args

  return out.stdout.trim

def ArrayBit.toHex(arrs: Array Bit): String :=
  let n := arrs.reverse.mapIdx (2^· * if · then 1 else 0) |>.sum
  let s := (Nat.toDigits 16 n).asString
  s

def testOn(msg: String): IO (Except String Unit) := do
  let expected ← runPython .SHA3_224 msg
  let actual := toString <| Spec.SHA3_224 msg.toUTF8Bits
  if expected ≠ actual then
    return .error s!"On {msg}, expected = {expected} actual = {actual}"
  else
    return .ok ()



def main(_args: List String): IO Unit := do
  let msgs := [
    "Lean",
    "Aeneas",
    "Charon",
  ]
  let mut errors := #[]
  for msg in msgs do
    if let .error e ← testOn msg then
      errors := errors.push e
  if ¬ errors.isEmpty then
    IO.println "ERRORS"
    IO.println <| "\n".intercalate errors.toList
  else
    IO.println "SUCCESS"
