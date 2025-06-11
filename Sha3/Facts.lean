import Sha3.Vector

@[simp]
theorem Spec.Keccak.StateArray.encode_decode(x: Fin 5)(y: Fin 5)(z: Fin (w l))
: decodeIndex (encodeIndex x y z) = (x,y,z) := by
  obtain ⟨x,x_lt⟩:= x
  obtain ⟨y,y_lt⟩:= y
  obtain ⟨z,z_lt⟩:= z
  simp [encodeIndex, decodeIndex]
  apply And.intro; case' right => apply And.intro
  · rw [Nat.add_comm]
    rw [Nat.add_mul_div_left z _ (by simp only [w]; exact Nat.two_pow_pos ↑l), Nat.div_eq_of_lt z_lt]
    simp
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left x _ (by decide), Nat.div_eq_of_lt x_lt]
    simp
  · simp [Nat.mod_eq_of_lt z_lt]
  · rw [Nat.add_comm]
    rw [Nat.add_mul_div_left z _ (by simp only [w]; exact Nat.two_pow_pos ↑l), Nat.div_eq_of_lt z_lt]
    simp [Nat.mod_eq_of_lt x_lt]

theorem Spec.Keccak.StateArray.decode_encode(c: Fin (b l))
: let (x,y,z) := decodeIndex c
  encodeIndex x y z = c
:= by
  obtain ⟨c, c_lt⟩ := c
  simp [decodeIndex, encodeIndex]
  rw [Nat.div_add_mod (c / w l) 5]
  rw [Nat.div_add_mod (c) (w l)]

@[simp]
theorem Spec.Keccak.StateArray.decode_encode'(c: Fin (b l))
: let xyz := decodeIndex c
  encodeIndex xyz.1 xyz.2.1 xyz.2.2 = c
:= by
  obtain ⟨c, c_lt⟩ := c
  simp [decodeIndex, encodeIndex]
  rw [Nat.div_add_mod (c / w l) 5]
  rw [Nat.div_add_mod (c) (w l)]


theorem Spec.Keccak.StateArray.encode_inj(x x' y y': Fin 5)(z z': Fin (w l))
: encodeIndex x y z = encodeIndex x' y' z' ↔ x = x' ∧ y = y' ∧ z = z'
:= by
  apply Iff.intro
  case mp =>
    intro hyp
    have h : decodeIndex (encodeIndex x y z) = _ := rfl
    conv at h => arg 2; rw [hyp]
    rw [encode_decode, encode_decode] at h
    simp at h; assumption
  case mpr => rintro ⟨rfl, rfl, rfl⟩; rfl

theorem Spec.Keccak.ι.rc_mod_eq_rc(t: Nat)
: Spec.Keccak.ι.rc (t % 255) = Spec.Keccak.ι.rc t
:= by
  have: Fin.ofNat' 255 (↑t % 255) = Fin.ofNat' 255 ↑t := by simp [Fin.ofNat']
  rw [rc, this, ←rc]
