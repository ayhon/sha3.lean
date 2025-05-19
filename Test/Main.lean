import Sha3.Spec
import Sha3.Utils
/- import Test.TestVectors -/
/- import Test.TestVectors -/
/- import Test.IntermediateValues -/
open Spec (Bit)


inductive Sha3FuncType where
| SHA3_224
| SHA3_256
| SHA3_384
| SHA3_512
| SHAKE128 (d: Nat)
| SHAKE256 (d: Nat)

instance: ToString Sha3FuncType where
  toString
  | .SHA3_224 => "SHA3_224"
  | .SHA3_256 => "SHA3_256"
  | .SHA3_384 => "SHA3_384"
  | .SHA3_512 => "SHA3_512"
  | .SHAKE128 _ => "SHAKE128"
  | .SHAKE256 _ => "SHAKE256"

def extraArgs: Sha3FuncType → Array String
  | .SHA3_224   
  | .SHA3_256   
  | .SHA3_384   
  | .SHA3_512 => #[]
  | .SHAKE128 d 
  | .SHAKE256 d => #[toString (d/8)]

def Sha3FuncType.toFunc: Sha3FuncType → Array Bit → String
| .SHA3_224 => toString ∘ Utils.dump ∘ Spec.SHA3_224
| .SHA3_256 => toString ∘ Utils.dump ∘ Spec.SHA3_256
| .SHA3_384 => toString ∘ Utils.dump ∘ Spec.SHA3_384
| .SHA3_512 => toString ∘ Utils.dump ∘ Spec.SHA3_512
| .SHAKE128 d => toString ∘ Utils.dump ∘ Spec.SHAKE128 (d := d)
| .SHAKE256 d => toString ∘ Utils.dump ∘ Spec.SHAKE256 (d := d)

def runPython(ty: Sha3FuncType)(S: String): IO String := do
  let args := #[
    "python",
    "sha3.py",
    toString ty,
    S
  ] ++ extraArgs ty
  dbg_trace s!"Running {args}"
  let out ← IO.Process.output {
    cmd := "/usr/bin/env",
    args
  }
  if ¬ out.stderr.isEmpty then
    dbg_trace out.stderr
    dbg_trace args

  return out.stdout.trim

def testOn(msg: String)(ty: Sha3FuncType)(getExpected: IO String): IO (Except String Unit) := do
/- def testOn(ty: Sha3FuncType)(msg: String): IO (Except String Unit) := do -/
  let expected ← getExpected
  let actual := ty.toFunc msg.toBitVecLE.toArray
  if expected ≠ actual then
    return .error s!"{ty}: Error on {msg}, \n\texpected = {expected}\n\tactual = {actual}"
  else
    return .ok ()

def randomChar: IO Char := do
  let hi1 := 0xd800
  let lo2 := 0x110000
  let hi2 := 0xdfff
  let val ← IO.rand 0 ↑(hi1-1 + (hi2-lo2-1))
  let val := UInt32.mk <| BitVec.ofFin <| Fin.ofNat' _ val
  if h: val < 0xd800 then
    have valid := by 
      obtain ⟨⟨⟨val, val_lt⟩⟩⟩ := val
      simp [UInt32.lt_def, BitVec.lt_def, Fin.lt_def] at h
      simp only [UInt32.isValidChar, UInt32.toNat, UInt32.toBitVec, BitVec.toNat, Nat.isValidChar]
      omega
    return {val, valid}
  else
    throw <| IO.userError "Random number generated doesn't work as expected"
    
def randomString(len?: Option Nat := none): IO String := do
  let len ← len?.getDM (IO.rand 0 100)
  let res ← List.range len
    |>.mapM (fun _ => randomChar)
  return res.asString

def testBasic: IO (Array String) := do
  let msgs := [
      "Lean",
      "Aeneas",
      "Charon",
  ]
  let mut errors := #[]
  for msg in msgs do
    let types: List Sha3FuncType := [.SHA3_224, .SHA3_256, .SHA3_384, .SHA3_512]
    for ty in types do
      if let .error e ← testOn msg ty (runPython ty msg) then
        dbg_trace e
        errors := errors.push <| e

    let d := (←IO.rand 10 100) * 8
    let types: List Sha3FuncType := [.SHAKE128 d, .SHAKE256 d]
    for ty in types do
      if let .error e ← testOn msg ty (runPython ty msg) then
        errors := errors.push <| e ++ s!"(d={d})"
  return errors

def testRandom: IO (Array String) := do
  let msgs ← List.range 10 
    |>.mapM (fun _ => randomString)

  let mut errors := #[]
  for msg in msgs do
    let types: List Sha3FuncType := [.SHA3_224, .SHA3_256, .SHA3_384, .SHA3_512]
    for ty in types do
      if let .error e ← testOn msg ty (runPython ty msg) then
        dbg_trace e
        errors := errors.push <| e

    let d := (←IO.rand 10 100) * 8
    let types: List Sha3FuncType := [.SHAKE128 d, .SHAKE256 d]
    for ty in types do
      if let .error e ← testOn msg ty (runPython ty msg) then
        errors := errors.push <| e ++ s!"(d={d})"
  return errors

def testVectors: IO (Array String) := do
  let mut errors := #[]
  let mut count := 1
  for info in TEST_VECTORS do
    let serialize{d} M := toString ∘ @Utils.dump d M
    dbg_trace s!"Running test vector {count}"
    let SHA3_224 := Spec.SHA3_224 info.message.toBitVecLE.toArray
    if serialize SHA3_224 ≠ info.SHA3_224 then
      errors := errors.push s!"SHA3_224: Error on {info.message}"
    let SHA3_256 := Spec.SHA3_256 info.message.toBitVecLE.toArray
    if serialize SHA3_256 ≠ info.SHA3_256 then
      errors := errors.push s!"SHA3_256: Error on {info.message}"
    let SHA3_384 := Spec.SHA3_384 info.message.toBitVecLE.toArray
    if serialize SHA3_384 ≠ info.SHA3_384 then
      errors := errors.push s!"SHA3_384: Error on {info.message}"
    let SHA3_512 := Spec.SHA3_512 info.message.toBitVecLE.toArray
    if serialize SHA3_512 ≠ info.SHA3_512 then
      errors := errors.push s!"SHA3_512 Error on {info.message}"
    count := count + 1
  return errors


def main(_args: List String): IO Unit := do
  let errors ← testBasic
  if ¬errors.isEmpty then
    IO.println "ERRORS:"
    IO.println <| "\n".intercalate errors.toList
    throw <| IO.userError "Errors found (see command output)"

  let errors ← testVectors
  if ¬errors.isEmpty then
    IO.println "ERRORS:"
    IO.println <| "\n".intercalate errors.toList
    throw <| IO.userError "Errors found (see command output)"

  let errors ← testRandom
  if ¬ errors.isEmpty then
    IO.println "ERRORS:"
    IO.println <| "\n".intercalate errors.toList
    throw <| IO.userError "Errors found (see command output)"

  IO.println "SUCCESS"

#check Spec.Keccak.ι.RC
#eval show _ from Id.run do
  let mut res := []
  for t in [0:24] do
    let x := @Spec.Keccak.ι.RC 6 t
    res := res ++ [x.toNat]
  dbg_trace s!"{res}"
  return 42
    
