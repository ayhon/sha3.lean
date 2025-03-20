
import Sha3.Spec

open Spec Keccak.StateArray in 
theorem encode_decode(x: Fin 5)(y: Fin 5)(z: Fin (w l))
: decodeIndex (encodeIndex x y z) = (x,y,z) := by
  obtain ⟨x,x_lt⟩:= x
  obtain ⟨y,y_lt⟩:= y
  obtain ⟨z,z_lt⟩:= z
  simp [encodeIndex, decodeIndex]
  apply And.intro; case' right => apply And.intro
  · rw [Nat.add_comm]
    rw [Nat.add_mul_div_left z _ (by simp [w]; exact Nat.two_pow_pos ↑l), Nat.div_eq_of_lt z_lt]
    simp
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left x _ (by decide), Nat.div_eq_of_lt x_lt]
    simp
  · simp [Nat.mod_eq_iff]; right; simp [z_lt]; exists 0
  · rw [Nat.add_comm]
    rw [Nat.add_mul_div_left z _ (by simp [w]; exact Nat.two_pow_pos ↑l), Nat.div_eq_of_lt z_lt]
    simp [Nat.mod_eq_iff]; simp [x_lt]; exists 0
