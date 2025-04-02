import Sha3.Spec
import Sha3.Utils

def main(args: List String): IO Unit := do
  let op::args := args
    | throw <| IO.userError "Not enough arguments"
  let output ← match op with
    | "SHA_224"
    | "SHA_256"
    | "SHA_384"
    | "SHA_512" => do
      let [input] := args
        | throw <| IO.userError s!"Expected one last argument, found {args}"
      let bits := input.toBitVecLE.toArray
      match op with
        | "SHA_224" => do
          pure $ Utils.dump <| Spec.SHA3_224 bits
        | "SHA_256" => do
          pure $ Utils.dump <| Spec.SHA3_256 bits
        | "SHA_384" => do
          pure $ Utils.dump <| Spec.SHA3_384 bits
        | "SHA_512" => do
          pure $ Utils.dump <| Spec.SHA3_512 bits
        | _ => throw <| IO.userError s!"Unreachable"
    | "SHAKE128"
    | "SHAKE256" => do
      let [input, d_str] := args
        | throw <| IO.userError s!"Expected two last arguments, found {args}"
      let some d := d_str.toNat?
        | throw <| IO.userError s!"Expected number, found {d_str}"
      let bits := input.toBitVecLE.toArray
      match op with
        | "SHAKE128" => do
          pure $ Utils.dump <| Spec.SHAKE128 bits d
        | "SHAKE256" => do
          pure $ Utils.dump <| Spec.SHAKE256 bits d
        | _ => throw <| IO.userError s!"Unreachable"
      pure ""
    | _ => throw $ IO.userError s!"Invalid option {op}"

  IO.println output

