
private def Vector.xor(v: Vector Bool n): Bool := v.foldl (·^^·) false
private def Vector.modify(v: Vector α n)(i: Fin n)(modif: α → α) : Vector α n :=
  ⟨v.toArray.modify i modif, by simp only [Array.size_modify, size_toArray] ⟩

local instance: OfNat Bool 0 where
  ofNat := false
local instance: OfNat Bool 1 where
  ofNat := true

namespace Spec
abbrev Bit := Bool

namespace KeccakP

variable (l: Fin 7)    -- Allowed values are:  0,  1,   2,   3,   4,   5,    6
abbrev w := 2^l.val    -- Allowed values are:  1,  2,   4,   8,  16,  32,   64
abbrev b := 5 * 5 * w l-- Allowed values are: 25, 50, 100, 200, 400, 800, 1600

/-- The state of the KeccakP function -/
structure StateArray where
  ofVector ::
  toVector : Vector Bool (b l)
  deriving Inhabited

namespace StateArray/- {{{ -/
variable {l: Fin 7}
variable (x: Fin 5)(y: Fin 5)(z: Fin (w l))

private def decodeIndex(c: Fin (b l)): Fin 5 × Fin 5 × Fin (w l) := 
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

def map(f: Bool → Bool)(A: StateArray l): StateArray l := .ofVector <| A.toVector.map f

/-- Given a function f which takes x, y and z, return a state array A' where
    A'[x,y,z] = f x y z -/
def ofFn(f: Fin 5 → Fin 5 → Fin (w l) → Bool): StateArray l := 
  .ofVector <| Vector.ofFn fun c =>
    let (x,y,z) := decodeIndex c
    f y x z

def get(A: StateArray l): Bool := Vector.get A.toVector <| encodeIndex x y z

/- instance: GetElem (StateArray l) (Fin 5 × Fin 5 × Fin (w l)) Bool (fun _ _ => True) where -/
/-   getElem | A, (x,y,z), _ => A.get x y z -/
/- macro A:term noWs "[" xs:term,* "]" : term => `( $A[($[$xs],*)] ) -/

def set(val: Bool)(A: StateArray l): StateArray l :=
  StateArray.ofFn fun x₂ y₂ z₂ => if x₂ == x ∧ y₂ == y ∧ z₂ == z then val else A.get x y z

def row (A: StateArray l): Vector Bool 5     := Vector.ofFn fun x => A.get x y z
def col (A: StateArray l): Vector Bool 5     := Vector.ofFn fun y => A.get x y z
def lane(A: StateArray l): Vector Bool (w l) := Vector.ofFn fun z => A.get x y z

end StateArray/- }}} -/

section «Step Mappings»/- {{{ -/
variable {l: Fin 7}

def θ(A: StateArray l): StateArray l := 
  StateArray.ofFn fun x y z => (A.get x y z) ^^ (A.col (x-1) z).xor ^^ (A.col (x+1) (z-1)).xor

def ρ.offset(t: Nat) := Fin.ofNat' (w l) $ (t + 1) * (t + 2) / 2
def ρ(A: StateArray l): StateArray l := 
  Id.run do
  let mut x: Fin 5 := 1
  let mut y: Fin 5 := 0
  let mut A' := StateArray.ofFn fun x y z => if x = 0 ∧ y = 0 then A.get 0 0 z else default
  for t in List.finRange 24 do
    for z in List.finRange (w l) do
      A' := A'.set x y z <| A.get x y <| z - ρ.offset t
      x := y
      y := (2*x + 3*y)
  return A'

def π(A: StateArray l): StateArray l := StateArray.ofFn fun x y z => A.get (x + 3*y) x z

def χ(A: StateArray l): StateArray l := 
  StateArray.ofFn fun x y z => A.get x y z ^^ ((A.get (x+1) y z ^^ true) && A.get (x+2) y z)

def ι.rc (t: Nat) := Id.run do
  let t := Fin.ofNat' 255 t
  if t = 0 then return true  
  let mut R: Vector Bool 8 := #v[1,0,0,0, 0,0,0,0]
  for i in [1:t] do
    let R': Vector Bool 9 := ⟨#[0] ++ R.toArray, by simp⟩
    let R' := R'.modify 0 (· ^^ R'.get! 8)
    let R' := R'.modify 4 (· ^^ R'.get! 8)
    let R' := R'.modify 5 (· ^^ R'.get! 8)
    let R' := R'.modify 6 (· ^^ R'.get! 8)
    R := R'.take 8
  return R.get 0

def ι(iᵣ: Nat)(A: StateArray l): StateArray l := Id.run do
  let mut A' := A
  let mut RC := Vector.mkVector (w l) false
  for j in List.finRange (l.val + 1) do
    have h := 
      calc  2 ^ ↑j - 1
        _ < 2 ^ ↑j := by 
          have := j.is_lt
          have := Nat.two_pow_pos j.val
          omega
        _ ≤ 2 ^ ↑l := by 
          apply Nat.pow_le_pow_iff_right (by decide: 1 < 2) |>.mpr
          exact Fin.is_le j
    RC := RC.set (2^j.val - 1) (ι.rc (j.val + 7*iᵣ)) (h)
  A' := StateArray.ofFn fun
          | 0, 0, z => A'.get 0 0 z ^^ RC.get z
          | x, y, z => A'.get x y z
  return A'

end «Step Mappings»/- }}} -/

end KeccakP

end Spec
