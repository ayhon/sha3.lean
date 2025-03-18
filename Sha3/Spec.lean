
/- private def Vector.xor(v: Vector Bool n): Bool := v.foldl (·^^·) false -/
/- private def Vector.modify(v: Vector α n)(i: Fin n)(modif: α → α) : Vector α n := -/
/-   ⟨v.toArray.modify i modif, by simp only [Array.size_modify, size_toArray] ⟩ -/
private def Vector.adjust(acc: Vector α n)(len: Nat)(fill: α): Vector α len := 
  let res := acc.toArray.take len ++ (Array.mkArray (len - n) fill)
  ⟨res, by 
    simp [res]
    cases h: decide (len > n) <;> simp at *
    · simp [Nat.min_eq_left h]
      exact Nat.sub_eq_zero_iff_le.mpr h
    · simp [Nat.min_eq_right (Nat.le_of_lt h)]
      simp [←Nat.add_sub_assoc (Nat.le_of_lt h) n]
      simp [Nat.add_sub_cancel_left]
    ⟩

private def Vector.ofArray(arr: Array α): Vector α arr.size := ⟨arr, rfl⟩

private def Array.chunks(k: Nat)(arr: Array α): Array (Vector α k) :=
  if h: arr.size < k ∨ k = 0 then 
    #[]
  else
    #[⟨arr.extract (stop := k), by simp_all [Nat.min_eq_left]⟩] ++ (arr.extract (start := k)).chunks k
termination_by arr.size

local instance: OfNat Bool 0 where ofNat := false
local instance: OfNat Bool 1 where ofNat := true


namespace Spec/- {{{ -/
abbrev Bit := Bool
abbrev BitString (n: Nat) := Vector Bit n

def BitString.filled(n: Nat)(default: Bit) := Vector.mkVector n default

local instance: Xor (BitString n)  where
  xor as bs := as.zipWith (·^^·) bs


variable {l: Fin 7}               -- Possible values:  0,  1,   2,   3,   4,   5,    6
abbrev w (l: Fin 7) := 2^l.val    -- Possible values:  1,  2,   4,   8,  16,  32,   64
abbrev b (l: Fin 7) := 5 * 5 * w l-- Possible values: 25, 50, 100, 200, 400, 800, 1600

namespace Keccak/- {{{ -/
/-- The state of the KeccakP function -/
structure StateArray (l: Fin 7) where
  ofVector ::
  toVector : BitString (b l)
  deriving Inhabited

namespace StateArray/- {{{ -/
variable (x: Fin 5)(y: Fin 5)(z: Fin (w l))(c: Fin (b l))

private def decodeIndex: Fin 5 × Fin 5 × Fin (w l) := 
  -- NOTE: The order of the indices is Y, X, Z so that lanes are placed
  -- closer together in memory.
    have x_lt := by apply Nat.mod_lt; decide
    have y_lt := by -- TODO: Try scalar_tac
      obtain ⟨_, _⟩ := c
      apply Nat.div_lt_iff_lt_mul (by decide) |>.mpr
      apply Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos) |>.mpr
      assumption
    have z_lt := by apply Nat.mod_lt; simp [w]; exact Nat.two_pow_pos l

    let x: Fin 5 := ⟨(c / w l) % 5, x_lt⟩
    let y: Fin 5 := ⟨(c / w l) / 5, y_lt⟩
    let z: Fin (w l) := ⟨c % w l, z_lt⟩
    (x,y,z)

private def encodeIndex: Fin (b l) := 
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

def map(f: Bit → Bit)(A: StateArray l): StateArray l := .ofVector <| A.toVector.map f

/-- Given a function f which takes x, y and z, return a state array A' where
    A'[x,y,z] = f x y z -/
def ofFn(f: Fin 5 → Fin 5 → Fin (w l) → Bit): StateArray l := 
  .ofVector <| Vector.ofFn fun c =>
    let (x,y,z) := decodeIndex c
    f y x z

def get(A: StateArray l): Bit := A.toVector.get <| encodeIndex x y z

/- instance: GetElem (StateArray l) (Fin 5 × Fin 5 × Fin (w l)) Bit (fun _ _ => True) where -/
/-   getElem | A, (x,y,z), _ => A.get x y z -/
/- macro A:term noWs "[" xs:term,* "]" : term => `( $A[($[$xs],*)] ) -/

def set(val: Bit)(A: StateArray l): StateArray l := .ofVector <| A.toVector.set (encodeIndex x y z) val

def row (A: StateArray l): BitString 5     := Vector.ofFn fun x => A.get x y z
def col (A: StateArray l): BitString 5     := Vector.ofFn fun y => A.get x y z
def lane(A: StateArray l): BitString (w l) := Vector.ofFn fun z => A.get x y z

end StateArray/- }}} -/

section «Step Mappings»/- {{{ -/

def θ(A: StateArray l): StateArray l := 
  let C x z := A.get x 0 z ^^ A.get x 1 z ^^ A.get x 2 z ^^ A.get x 3 z ^^ A.get x 4 z
  let D x z := C (x-1) z ^^ C (x+1) (z-1)
  StateArray.ofFn fun x y z => (A.get x y z) ^^ D x z

def ρ.offset(t: Nat) := Fin.ofNat' (w l) $ (t + 1) * (t + 2) / 2
def ρ(A: StateArray l): StateArray l := 
  Id.run do
  let mut x: Fin 5 := 1
  let mut y: Fin 5 := 0
  -- NOTE: We could have it be simply A, since we don't care about the default values
  let mut A' := A -- StateArray.ofFn fun x y z => if x = 0 ∧ y = 0 then A.get 0 0 z else default
  for t in List.finRange 24 do -- from 0 until 23
    for z in List.finRange (w l) do
      A' := A'.set x y z <| A.get x y <| z - ρ.offset t
      x := y
      y := 2*x + 3*y
  return A'

def π(A: StateArray l): StateArray l := StateArray.ofFn fun x y z => A.get (x + 3*y) x z

def χ(A: StateArray l): StateArray l := 
  StateArray.ofFn fun x y z => A.get x y z ^^ ((A.get (x+1) y z ^^ 1) && A.get (x+2) y z)

def ι.rc (t: Nat) := Id.run do
  let t := Fin.ofNat' 255 t
  if t = 0 then return true  
  let mut R: BitString 8 := #v[1,0,0,0, 0,0,0,0]
  for i in [1:t+1] do -- From 1 to t, inclusive!
    let R': BitString 9 := ⟨#[0] ++ R.toArray, by simp⟩
    let R' := R'.set 0 <| R'[0] ^^ R'[8]
    let R' := R'.set 4 <| R'[4] ^^ R'[8]
    let R' := R'.set 5 <| R'[5] ^^ R'[8]
    let R' := R'.set 6 <| R'[6] ^^ R'[8]
    R := R'.take 8
  return R.get 0

def ι(iᵣ: Nat)(A: StateArray l): StateArray l := Id.run do
  let mut RC: BitString (w l) := BitString.filled (w l) 0
  for j in List.finRange (l.val + 1) do
    have j_valid_idx := calc  2 ^ ↑j - 1
        _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
        _ ≤ 2 ^ ↑l := Nat.pow_le_pow_iff_right (by decide) |>.mpr <| Fin.is_le j
    RC := RC.set (2^↑j - 1) (ι.rc (↑j + 7*iᵣ)) j_valid_idx
  return StateArray.ofFn fun
    | 0, 0, z => A.get 0 0 z ^^ RC.get z
    | x, y, z => A.get x y z

end «Step Mappings»/- }}} -/

def Rnd(A: StateArray l)(iᵣ: Nat) := ι iᵣ <| χ <| π <| ρ <| θ <| A

def P(l: Fin 7)(nᵣ: Nat)(S: BitString (b l)): BitString (b l) := Id.run do
  let mut A := StateArray.ofVector S
  for iᵣ in [12 + 2*l - nᵣ: 12 + 2*l - 1 + 1] do -- inclusive range!
    A := Rnd A iᵣ
  return A.toVector

def F l := Keccak.P l (nᵣ:= 12 + 2*l)

end Keccak/- }}} -/

section Sponge/- {{{ -/

/- section Pad -/

/- /1- structure PadFn where -1/ -/
/- /1-   -- x > 0 -1/ -/
/- /1-   len:   (x:Nat) → (m:Nat) → Nat -1/ -/
/- /1-   apply: (x:Nat) → (m:Nat) → BitString (len x m) -1/ -/
/- /1-   prop{x m}: x ∣ (len x m) -1/ -/

/- end Pad -/

def sponge.squeze
    (f: BitString (b l) → BitString (b l))
    (r: Nat)
    /- [NeZero r] -/
    (Z: Array Bit)
    (S: BitString (b l))
: BitString d
:= 
    if h: Z.size >= d then
      ⟨Z.take d, by simp [Nat.min_eq_left h]⟩
    else
      sponge.squeze f r (Z ++ S.toArray.take r) (f S)
partial_fixpoint -- NOTE: Needed because without `r>0` we cannot prove termination
-- Alternatively:
/- termination_by d - Z.size -/
/- decreasing_by -/
/-   have : (b l) >= 1 :=by -/
/-     simp [b, w] -/
/-     apply Nat.mul_pos -/
/-     · decide -/
/-     · exact Nat.two_pow_pos l.val -/
/-   rename_i r_ne_zero -/
/-   have : r >= 1 := Nat.pos_of_ne_zero r_ne_zero.out -/
/-   simp -/
/-   omega -/

def sponge{l: Fin 7}
  (f: BitString (b l) → BitString (b l))
  (pad: Nat → Nat → Array Bit)
  (r: Nat) -- non-negative integer
  /- [NeZero r] -/
  ⦃m: Nat⦄
  (N: BitString m)
  (d: Nat) -- non-negative integer
: BitString d := 
  let P := N.toArray ++ pad r N.size
  let n := P.size / r
  let c := (b l) - r -- NOTE: Deprecated by use of `Vector.adjust`
  let Ps := P.chunks r
  assert! Ps.size = n
  Id.run do
  let mut S: BitString (b l) := BitString.filled (b l) false
  for Pᵢ in Ps do
    S := f (S ^^^ (Pᵢ.adjust (b l) false))
    assert! (Pᵢ.adjust (b l) false).toArray ==
            (Pᵢ ++ BitString.filled c false).toArray
  return sponge.squeze f r (S.toArray.take r) S


def «pad10*1»(x m: Nat): Array Bit := 
  let j := Int.toNat <| (- (m: Int) - 2) % x
  (#v[true] ++ BitString.filled j false ++ #v[true]).toArray

end Sponge/- }}} -/

def Keccak(c: Nat):= sponge (f := Keccak.P 6 (nᵣ := 24)) (pad := «pad10*1») (r := 1600 - c)

private abbrev SHA3_suffix: Array Bit := #[0,1]
private abbrev RawSHAKE_suffix: Array Bit := #[1,1]
private abbrev SHAKE_suffix: Array Bit := RawSHAKE_suffix ++ #[1,1]

def SHA3_224(M : Array Bit) := Keccak (c := 448) (Vector.ofArray <| M ++ SHA3_suffix) 224
def SHA3_256(M : Array Bit) := Keccak (c := 512) (Vector.ofArray <| M ++ SHA3_suffix) 256
def SHA3_384(M : Array Bit) := Keccak (c := 768) (Vector.ofArray <| M ++ SHA3_suffix) 384
def SHA3_512(M : Array Bit) := Keccak (c :=1024) (Vector.ofArray <| M ++ SHA3_suffix) 512

def SHAKE128(M : Array Bit)(d: Nat) := Keccak (c := 256) (Vector.ofArray <| M ++ SHAKE_suffix) d
def SHAKE256(M : Array Bit)(d: Nat) := Keccak (c := 512) (Vector.ofArray <| M ++ SHAKE_suffix) d

def RawSHAKE128(M : Array Bit)(d: Nat) := Keccak (c := 256) (Vector.ofArray <| M ++ RawSHAKE_suffix) d
def RawSHAKE256(M : Array Bit)(d: Nat) := Keccak (c := 512) (Vector.ofArray <| M ++ RawSHAKE_suffix) d

end Spec/- }}} -/
