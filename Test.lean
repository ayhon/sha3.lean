import Sha3.Spec
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

def ArrayBit.decode(s: String): Array Bit :=
  let res := s.toList.filterMap fun c => if c = '0' then some false else if c = '1' then some true else none
  assert! (res.length == s.trim.length)
  ⟨res⟩
  
def ArrayBit.encode(bs: Array Bit): String := bs.toList.map (if · then "1" else "0") |> String.join


def runPython(ty: Sha3FuncType)(S: Array Bit) (flipEndianness?: Bool := false): IO (Array Bit) := do
  let args := #[
      "python",
      "sha3.py",
      toString ty,
      ArrayBit.encode S
    ] ++ (if flipEndianness? then #["FLIP"] else #[])
  let out ← IO.Process.output {
    cmd := "/usr/bin/env",
    args
  }
  if ¬ out.stderr.isEmpty then
    dbg_trace out.stderr
    dbg_trace args

  return ArrayBit.decode out.stdout


def main(_args: List String): IO Unit := do
  /- let bs := ArrayBit.decode "1001100011001010110000101101110" -/
  let bs := ArrayBit.decode "00000001"
  let expected ← runPython .SHA3_224 bs
  let actual := Spec.SHA3_224 bs |>.toArray
  if expected ≠ actual then
    IO.println s!"epxected = {ArrayBit.encode expected}"
    IO.println s!"actual = {ArrayBit.encode actual}"
    let expected_fliped ← runPython .SHA3_224 bs (flipEndianness? := true)
    if expected ≠ expected_fliped then
      IO.println s!"epxected(flip) = {ArrayBit.encode expected_fliped}"
    assert!(expected_fliped == actual)

  assert!(expected == actual)
