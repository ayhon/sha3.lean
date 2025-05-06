import Sha3.Utils

@[simp] local instance(x: Fin n): NeZero (n - x) where out := by omega

namespace Spec/- {{{ -/
section Data/- {{{ -/
abbrev Bit := Bool
abbrev Bitstring n := Vector Bit n

instance(n: Nat): Xor (Bitstring n) where xor a b := .ofFn (fun i => a[i] ^^ b[i])
end Data/- }}} -/

variable {l: Fin 7}               -- Possible values:  0,  1,   2,   3,   4,   5,    6
abbrev w (l: Fin 7) := 2^l.val    -- Possible values:  1,  2,   4,   8,  16,  32,   64
abbrev b (l: Fin 7) := 5 * 5 * w l-- Possible values: 25, 50, 100, 200, 400, 800, 1600

namespace Keccak/- {{{ -/
section Data/- {{{ -/

/-- The state of the KeccakP function -/
structure StateArray (l: Fin 7) where
  ofVector ::
  toVector : Bitstring (b l)
  deriving Inhabited

namespace StateArray/- {{{ -/
variable (x: Fin 5)(y: Fin 5)(z: Fin (w l))(c: Fin (b l))

/-- Transforms an index in the in-memory representation of the StateArray
    to the indices in the 3-dimensional presentation of the specification. -/
def decodeIndex: Fin 5 × Fin 5 × Fin (w l) :=
    have x_lt := by apply Nat.mod_lt; decide
    have y_lt := by
      obtain ⟨_, _⟩ := c
      apply Nat.div_lt_iff_lt_mul (by decide) |>.mpr
      apply Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos) |>.mpr
      assumption
    have z_lt := by apply Nat.mod_lt; simp [w]; exact Nat.two_pow_pos l

    let x: Fin 5 := ⟨(c / w l) % 5, x_lt⟩
    let y: Fin 5 := ⟨(c / w l) / 5, y_lt⟩
    let z: Fin (w l) := ⟨c % w l, z_lt⟩
    (x,y,z)

/-- Transforms the indices in the 3-dimensional presentation of the specification
    to the in-memory representation of the StateArray. -/
def encodeIndex: Fin (b l) :=
  have := by
    have: z / w l = (0 : Nat) := by
      obtain ⟨_,_⟩ := z; simp
      apply Nat.div_eq_zero_iff_lt (by apply Nat.two_pow_pos : 0 < w l) |>.mpr (by assumption)
    apply Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos l) |>.mp
    rw [Nat.mul_add_div (by apply Nat.two_pow_pos l) _ z.val, this, Nat.add_zero]
    have: x / 5 = (0: Nat) := by
      obtain ⟨_,_⟩ := x; simp
      apply Nat.div_eq_zero_iff_lt (by decide: 0 < 5) |>.mpr (by assumption)
    apply Nat.div_lt_iff_lt_mul (by decide: 0 < 5) |>.mp
    rw [Nat.mul_add_div (by decide: 0 < 5) _ x.val, this, Nat.add_zero]
    exact y.isLt
  ⟨w l * (5 * y + x) + z, this⟩

/-- Given a function f which takes x, y and z, return a state array A' where
    A'[x,y,z] = f x y z -/
def ofFn(f: Fin 5 × Fin 5 × Fin (w l) → Bit): StateArray l :=
  .ofVector <| Vector.ofFn (f ∘ decodeIndex)

def get(A: StateArray l): Bit := A.toVector[encodeIndex x y z]

def set(val: Bit)(A: StateArray l): StateArray l := .ofVector <| A.toVector.set (encodeIndex x y z) val

def row (A: StateArray l): Bitstring 5     := Vector.ofFn (A.get · y z)
def col (A: StateArray l): Bitstring 5     := Vector.ofFn (A.get x · z)
def lane(A: StateArray l): Bitstring (w l) := Vector.ofFn (A.get x y ·)

instance: Repr (StateArray l) where reprPrec A _ := Utils.dump (spacing? := true) (BitVec.ofBoolListLE A.toVector.toList)

end StateArray/- }}} -/
end Data/- }}} -/

section «Step Mappings»/- {{{ -/

def θ.C (A: StateArray l) x z := A.get x 0 z ^^ A.get x 1 z ^^ A.get x 2 z ^^ A.get x 3 z ^^ A.get x 4 z
def θ.D (A: StateArray l) x z := C A (x-1) z ^^ C A (x+1) (z-1)
def θ(A: StateArray l): StateArray l :=
  StateArray.ofFn fun (x,y,z) => (A.get x y z) ^^ θ.D A x z


def ρ.offset(t: Nat) := Fin.ofNat' (w l) $ (t + 1) * (t + 2) / 2
def ρ(A: StateArray l): StateArray l :=
  Id.run do
  let mut (x, y): Fin 5 × Fin 5 := (1,0)
  let mut A' := A
  for t in List.finRange 24 do
    for z in List.finRange (w l) do
      A' := A'.set x y z <| A.get x y (z - ρ.offset t)
    (x, y) := (y, 2*x + 3*y)
  return A'

def π(A: StateArray l): StateArray l := StateArray.ofFn fun (x,y,z) => A.get (x + 3*y) x z

def χ(A: StateArray l): StateArray l :=
  StateArray.ofFn fun (x,y,z) => A.get x y z ^^ ((A.get (x+1) y z ^^ true) && A.get (x+2) y z)

def ι.rc (t: Nat) := Id.run do
  let t := Fin.ofNat' 255 t
  if t = 0 then return true
  let mut R: Bitstring 8 := #v[true, false, false, false, false, false, false, false]
  for i in [1:t+1] do -- inclusive range!
    let R': Bitstring 9 := #v[false] ++ R
    let R' := R'.set 0 <| R'[0] ^^ R'[8]
    let R' := R'.set 4 <| R'[4] ^^ R'[8]
    let R' := R'.set 5 <| R'[5] ^^ R'[8]
    let R' := R'.set 6 <| R'[6] ^^ R'[8]
    R := R'.take 8
  return R[0]

def ι.RC {l: Fin 7}(iᵣ: Nat): Bitstring (w l) := Id.run do
  let mut RC: Bitstring (w l) := .ofFn (fun _ => false)
  for j in List.finRange (l.val + 1) do -- inclusive range!
    have j_valid_idx := calc  2 ^ ↑j - 1
        _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
        _ ≤ 2 ^ ↑l := Nat.pow_le_pow_iff_right (by decide) |>.mpr <| Fin.is_le j
    RC := RC.set (2^j.val - 1) (ι.rc (↑j + 7*iᵣ)) j_valid_idx
  RC

def ι(iᵣ: Nat)(A: StateArray l): StateArray l := Id.run do
  let RC := ι.RC iᵣ
  return StateArray.ofFn fun
    | (0, 0, z) => A.get 0 0 z ^^ RC[z]
    | (x, y, z) => A.get x y z

end «Step Mappings»/- }}} -/

def Rnd(A: StateArray l)(iᵣ: Nat) :=
  let A' := A
  let A' := θ A'
  let A' := ρ A'
  let A' := π A'
  let A' := χ A'
  let A' := ι iᵣ A'
  A'

/-- The permutation function Keccak-p[b,nᵣ], defined in terms of l instead of b. -/
def P(l: Fin 7)(nᵣ: Nat)(S: Bitstring (b l)): Bitstring (b l) := Id.run do
  let mut A := StateArray.ofVector S
  for iᵣ in [(12 + 2*↑l) - nᵣ: (12 + 2*↑l) - 1 + 1] do -- inclusive range!
    A := Rnd A iᵣ
  return A.toVector

/-- The Keccak-f[b] family of permutations, defined in terms of l instead of b. -/
def F l := Keccak.P l (nᵣ:= 12 + 2*l)

end Keccak/- }}} -/

section Sponge/- {{{ -/

/-- The padding rule for Keccak, called multi-rate padding -/
def «pad10*1»(x m: Nat): Array Bit :=
  let j := Int.toNat <| (- (m: Int) - 2) % x
  #[true] ++ mkArray j false ++ #[true]

def sponge.absorb{l: Fin 7}
  (f: Bitstring (b l) → Bitstring (b l))
  (pad: Nat → Nat → Array Bit)
  (r: Nat) [NeZero r]
  (N: Array Bit)
: Bitstring (b l) :=
  let P := N ++ pad r N.size
  /- assert! P.size % r == 0 -/
  let n := P.size / r
  let c := (b l) - r
  let Ps := P.chunks_exact r
  /- assert! Ps.size = n -/
  Id.run do
  let mut S: Bitstring (b l) := .ofFn (fun _ => false)
  for Pᵢ in Ps do
    S := f (S ^^^ (Pᵢ.setWidth (b l)))
    /- assert! ((BitVec.ofBoolListLE Pᵢ.toList).setWidth (b l)).toArray == -/
    /-         (BitVec.fill c false ++ (BitVec.ofBoolListLE Pᵢ.toList)).toArray -/
  return S

def sponge.squeeze
    (f: Bitstring (b l) → Bitstring (b l))
    (r: Nat) [NeZero r]
    (Z: Bitstring m)
    (S: Bitstring (b l))
: Bitstring d
:=
  if d <= m then
    Z.setWidth d
  else
    sponge.squeeze f r (Z ++ S.setWidth r) (f S)

termination_by d - m
decreasing_by
  have: (b l) >= 1 := Nat.mul_pos (by decide) (Nat.two_pow_pos l.val)
  have: r >= 1 := Nat.pos_of_ne_zero NeZero.out
  simp
  omega

/--
The sponge construction is a framework for specifying functions on binary data with
arbitrary output length. The construction employs the following three components:
 · An underlying function on fixed-length strings, denoted by f,
 · A parameter called the rate, denoted by r, and
 · A padding rule, denoted by pad.
-/
def sponge{l: Fin 7}
  (f: Bitstring (b l) → Bitstring (b l))
  (pad: Nat → Nat → Array Bit)
  (r: Nat) [NeZero r]
  (N: Array Bit)
  (d: Nat)
: Bitstring d :=
  let S := sponge.absorb f pad r N
  let Z := #v[]
  let hash := sponge.squeeze f r Z S
  hash

end Sponge/- }}} -/

/-- The Keccak[c] family of sponge functions, restricted to b = 1600 (or l = 6) -/
def Keccak(c: Fin (b 6)):= sponge (f := Keccak.P 6 (nᵣ := 24)) (pad := «pad10*1») (r := (b 6) - c)


private abbrev SHA3_suffix:     Array Bit := #[false, true]
private abbrev RawSHAKE_suffix: Array Bit := #[true,  true]
private abbrev SHAKE_suffix:    Array Bit := RawSHAKE_suffix ++ #[true,  true]

-- Hash functions
def SHA3_224   (M : Array Bit)         := Keccak (c := ( 448: Fin 1600)) (M ++ SHA3_suffix    ) 224
def SHA3_256   (M : Array Bit)         := Keccak (c := ( 512: Fin 1600)) (M ++ SHA3_suffix    ) 256
def SHA3_384   (M : Array Bit)         := Keccak (c := ( 768: Fin 1600)) (M ++ SHA3_suffix    ) 384
def SHA3_512   (M : Array Bit)         := Keccak (c := (1024: Fin 1600)) (M ++ SHA3_suffix    ) 512

-- XOF functions
def SHAKE128   (M : Array Bit)(d: Nat) := Keccak (c := (256: Fin 1600)) (M ++ SHAKE_suffix   )   d
def SHAKE256   (M : Array Bit)(d: Nat) := Keccak (c := (512: Fin 1600)) (M ++ SHAKE_suffix   )   d

def RawSHAKE128(M : Array Bit)(d: Nat) := Keccak (c := (256: Fin 1600)) (M ++ RawSHAKE_suffix)   d
def RawSHAKE256(M : Array Bit)(d: Nat) := Keccak (c := (512: Fin 1600)) (M ++ RawSHAKE_suffix)   d
-- ≤

end Spec/- }}} -/
