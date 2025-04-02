import Sha3.Spec
import Sha3.Utils
import Test.TestVectors
import Test.IntermediateValues
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
  let actual := toString <| ty.toFunc msg.toBitVecLE.toArray
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

def testRandom: IO (Array String) := do
  let msgs := [
      "Lean",
      "Aeneas",
      "Charon",
  ].append <| ← List.range 10 
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
    dbg_trace s!"Running test vector {count}"
    let SHA3_224 := Spec.SHA3_224 info.message.toBitVecLE.toArray
    if toString SHA3_224 ≠ info.SHA3_224 then
      errors := errors.push s!"SHA3_224: Error on {info.message}"
    let SHA3_256 := Spec.SHA3_256 info.message.toBitVecLE.toArray
    if toString SHA3_256 ≠ info.SHA3_256 then
      errors := errors.push s!"SHA3_256: Error on {info.message}"
    let SHA3_384 := Spec.SHA3_384 info.message.toBitVecLE.toArray
    if toString SHA3_384 ≠ info.SHA3_384 then
      errors := errors.push s!"SHA3_384: Error on {info.message}"
    let SHA3_512 := Spec.SHA3_512 info.message.toBitVecLE.toArray
    if toString SHA3_512 ≠ info.SHA3_512 then
      errors := errors.push s!"SHA3_512 Error on {info.message}"
    count := count + 1
  return errors


def main(_args: List String): IO Unit := do
  let mut errors := #[]
  errors := errors.append <| ←testRandom
  errors := errors.append <| ←testVectors

  if ¬ errors.isEmpty then
    IO.println "ERRORS:"
    IO.println <| "\n".intercalate errors.toList
    throw <| IO.userError "Errors found (see command output)"
  else
    IO.println "SUCCESS"

-- Testing hex
/- #eval show _ from Id.run do -/
/-   let x: Spec.BitString _ := "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toUTF8Bits |> Vector.ofArray -/
/-   dbg_trace s!"let input = {x.toList};" -/
/-   dbg_trace s!"let expected = \"{x}\";" -/
/-   42 -/
  
-- Testing theta
/- #eval show _ from Id.run do -/
/-   let input := "Lean".toUTF8Bits |> Vector.ofArray |>.adjust (Spec.b 6) false -/
/-   dbg_trace s!"let mut buff = StateArray({input.toList});" -/
/-   let output := Spec.Keccak.θ <| Spec.Keccak.StateArray.ofVector input -/
/-   dbg_trace s!"let expected = {output.toVector.toList};" -/
/-   dbg_trace s!"let expected = \"{output.toVector}\";" -/
/-   42 -/

/- #eval show _ from Id.run do -/
/-   let input := "werfvbnmkjhgvcxsertghnmki98u".toUTF8Bits |> Vector.ofArray |>.adjust (Spec.b 6) false -/
/-   /1- dbg_trace s!"let mut buff = StateArray({input.toList});" -1/ -/
/-   let iᵣ := 23 -/
/-   let output := Spec.Keccak.ι iᵣ <| Spec.Keccak.StateArray.ofVector input -/
/-   /1- dbg_trace s!"let expected = {output.toVector.toList};" -1/ -/
/-   dbg_trace s!"let expected = \"{output.toVector}\";" -/
/-   /1- dbg_trace s!"let actual = iota(&mut buff, {iᵣ});" -1/ -/
/-   42 -/

/- #eval show _ from Id.run do -/
/-   let input := "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toUTF8Bits -/
/-   dbg_trace s!"let mut buff = vec!{input.toList};" -/
/-   let output := Spec.SHA3_224 <| input -/
/-   /1- dbg_trace s!"let expected = {output.toVector.toList};" -1/ -/
/-   dbg_trace s!"let expected = \"{output.toVector}\";" -/
/-   42 -/


/- #eval show IO _ from do -/
/-   for _ in [0:10] do -/
/-     let m ← IO.rand 0 100 -/
/-     let x ← IO.rand 0 100 -/
/-     dbg_trace s!"let (x,m) = {(x,m)};" -/
/-     let output := Spec.«pad10*1» x m -/
/-     dbg_trace s!"let expected ={output.size};" -/
/-     /1- dbg_trace s!"let actual = pad10_1(x,m).len();" -1/ -/
/-     /1- dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -1/ -/
/-     dbg_trace s!"let expected = vec!{output.toList};" -/
/-     dbg_trace s!"let actual = pad10_1(x,m);" -/
/-     dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -/
/-   let m := 10 -/
/-   let x := 12 -/
/-   dbg_trace s!"let (x,m) = {(x,m)};" -/
/-   let output := Spec.«pad10*1» x m -/
/-   dbg_trace s!"let expected ={output.size};" -/
/-   /1- dbg_trace s!"let actual = pad10_1(x,m).len();" -1/ -/
/-   /1- dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -1/ -/
/-   dbg_trace s!"let expected = vec!{output.toList};" -/
/-   dbg_trace s!"let actual = pad10_1(x,m);" -/
/-   dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -/

/-   let m := 11 -/
/-   let x := 12 -/
/-   dbg_trace s!"let (x,m) = {(x,m)};" -/
/-   let output := Spec.«pad10*1» x m -/
/-   dbg_trace s!"let expected ={output.size};" -/
/-   /1- dbg_trace s!"let actual = pad10_1(x,m).len();" -1/ -/
/-   /1- dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -1/ -/
/-   dbg_trace s!"let expected = vec!{output.toList};" -/
/-   dbg_trace s!"let actual = pad10_1(x,m);" -/
/-   dbg_trace s!"assert_eq!(actual, expected, \"Failed with m={m} and x={x}\");" -/
/-   return 42 -/

/- #eval show IO _ from do -/
/-   /1- let input := "".toUTF8Bits ++ #[false, true] -1/ -/
/-   /1- let r ← IO.rand 1 ((Spec.b 6) - 1) -1/ -/
/-   /1- if h: r = 0 then throw $ IO.Error.userError "WTF" else -1/ -/ 
/-   /1- let output := @Spec.sponge.absorb 6 (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r ⟨h⟩ input -1/ -/
/-   /1- dbg_trace s!"let input = vec!{input.toList};" -1/ -/
/-   /1- dbg_trace s!"let r = {r};" -1/ -/
/-   /1- dbg_trace s!"let expected = \"{output.toVector}\";" -1/ -/
/-   /1- dbg_trace s!"sponge_absorb(&input, r, &mut actual);" -1/ -/
/-   /1- dbg_trace s!"assert_eq!(actual, expected);" -1/ -/

/-   let test_on_r (r: Nat) (h: r ≠ 0 := by decide) := do -/
/-     let input := "asd".toUTF8Bits -/
/-     let output := @Spec.sponge.absorb 6 (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r ⟨h⟩ input -/
/-     dbg_trace s!"let input = vec!{input.toList};" -/
/-     dbg_trace s!"let r = {r};" -/
/-     dbg_trace s!"let expected = \"{output.toVector}\";" -/
/-     dbg_trace s!"let mut actual = [false; B];" -/
/-     dbg_trace s!"sponge_absorb(&input, r, &mut actual);" -/
/-     dbg_trace s!"assert_eq!(crate::hex_of_vec_of_bits(&actual), expected, \"Failed with r = {r} and input.size = {input.size}\");" -/
/-     return output -/
/-   let _ ← test_on_r 27 -/
/-   let _ ← test_on_r 26 -/
/-   let _ ← test_on_r 25 -/
/-   let _ ← test_on_r 24 -/

/- #eval show IO _ from do -/
/-   /1- let input := "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toUTF8Bits |> Vector.ofArray |>.adjust (Spec.b 6) false -1/ -/
/-   let input := "asdfsdfgdfghfghjghjkhjklqwerwertertyrtyutyuiyuio".toBitVec.setWidth (Spec.b 6) -/
/-   /1- let r ← IO.rand 1 ((Spec.b 6) - 1) -1/ -/
/-   /1- let r ← IO.rand 1 ((Spec.b 6) - 1) -1/ -/
/-   let r ← IO.rand 1 32 -/
/-   let d := 20 * 8 -/
/-   if h: r = 0 then throw $ IO.Error.userError "WTF" else -/ 
/-   let output := @Spec.sponge.squeeze 6 _ d (f := Spec.Keccak.P 6 (nᵣ := 24)) r ⟨h⟩ (input.truncate r) input -/
/-   dbg_trace s!"// {input}" -/
/-   dbg_trace s!"let mut input = {input.toArray.toList};" -/
/-   dbg_trace s!"let r = {r};" -/
/-   dbg_trace s!"let d = {d};" -/
/-   dbg_trace s!"let expected = \"{output.toHex}\";" -/
/-   dbg_trace s!"actual.clear();" -/
/-   dbg_trace s!"sponge_squeeze(d, r, &mut actual, &mut input);" -/
/-   dbg_trace s!"assert_eq!(crate::hex_of_vec_of_bits(&actual), expected);" -/

/- #eval show IO _ from do -/
/-   let input := "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".toUTF8Bits |> Vector.ofArray |>.adjust (Spec.b 6) false -/
/-   /1- let input := "asdfsdfgdfghfghjghjkhjklqwerwertertyrtyutyuiyuio".toUTF8Bits |> Vector.ofArray |>.adjust (Spec.b 6) false -1/ -/
/-   let output := Spec.Keccak.P 6 24 input -/
/-   dbg_trace s!"let input = {input.toList};" -/
/-   dbg_trace s!"let expected = \"{output.toVector}\";" -/
/-   dbg_trace s!"let mut actual = input;" -/
/-   dbg_trace s!"keccak_p(&mut actual);" -/
/-   dbg_trace s!"assert_eq!(crate::hex_of_vec_of_bits(&actual), expected);" -/


/- #eval Spec.SHA3_224 "".toBitVec.toArray -/
