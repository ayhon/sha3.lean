import Sha3.Spec
import Sha3.Utils
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
| .SHA3_224 => toString ∘ Spec.SHA3_224
| .SHA3_256 => toString ∘ Spec.SHA3_256
| .SHA3_384 => toString ∘ Spec.SHA3_384
| .SHA3_512 => toString ∘ Spec.SHA3_512
| .SHAKE128 d => toString ∘ Spec.SHAKE128 (d := d)
| .SHAKE256 d => toString ∘ Spec.SHAKE256 (d := d)

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

def ArrayBit.toHex(arrs: Array Bit): String :=
  let n := arrs.reverse.mapIdx (2^· * if · then 1 else 0) |>.sum
  let s := (Nat.toDigits 16 n).asString
  s

def testOn(ty: Sha3FuncType)(msg: String): IO (Except String Unit) := do
  let expected ← runPython ty msg
  let actual := toString <| ty.toFunc msg.toUTF8Bits
  if expected ≠ actual then
    return .error s!"On {msg}, expected = {expected} actual = {actual}"
  else
    return .ok ()

def randomChar: IO Char := do
  let hi1 := 0xd800
  let lo2 := 0x110000
  let hi2 := 0xdfff
  let val ← IO.rand 0 ↑(hi1-1 + (hi2-lo2-1))
  let val := UInt32.ofBitVec <| BitVec.ofFin <| Fin.ofNat' _ val
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

def main(_args: List String): IO Unit := do
  let msgs := [
    "Lean",
    "Aeneas",
    "Charon",
  ] ++ (←List.range 10 |>.mapM (fun _ => randomString))

  let mut errors := #[]
  for msg in msgs do
    if let .error e ← testOn (.SHA3_224) msg then
      errors := errors.push <| "SHA3_224: " ++ e
    if let .error e ← testOn (.SHA3_256) msg then
      errors := errors.push <| "SHA3_256: " ++ e
    if let .error e ← testOn (.SHA3_384) msg then
      errors := errors.push <| "SHA3_384: " ++ e
    if let .error e ← testOn (.SHA3_512) msg then
      errors := errors.push <| "SHA3_512: " ++ e
    let d := (←IO.rand 10 100) * 8
    if let .error e ← testOn (.SHAKE128 d) msg then
      errors := errors.push <| "SHAKE128 (d={d}): " ++ e
    if let .error e ← testOn (.SHAKE256 d) msg then
      errors := errors.push <| "SHAKE256 (d={d}): " ++ e
  if ¬ errors.isEmpty then
    IO.println "ERRORS"
    IO.println <| "\n".intercalate errors.toList
  else
    IO.println "SUCCESS"

#eval Spec.SHAKE128 "Lean".toUTF8Bits (d := 333)
