import Init.Data.Nat.Div.Lemmas

/- private def Vector.xor(v: Vector Bool n): Bool := v.foldl (·^^·) false -/
/- private def Vector.modify(v: Vector α n)(i: Fin n)(modif: α → α) : Vector α n := -/
/-   ⟨v.toArray.modify i modif, by simp only [Array.size_modify, size_toArray] ⟩ -/
/- def Vector.adjust(acc: Vector α n)(len: Nat)(fill: α): Vector α len := -/ 
/-   let res := acc.toArray.take len ++ (Array.mkArray (len - n) fill) -/
/-   ⟨res, by -/ 
/-     simp [res] -/
/-     cases h: decide (len > n) <;> simp at * -/
/-     · simp [Nat.min_eq_left h] -/
/-       exact Nat.sub_eq_zero_iff_le.mpr h -/
/-     · simp [Nat.min_eq_right (Nat.le_of_lt h)] -/
/-       simp [←Nat.add_sub_assoc (Nat.le_of_lt h) n] -/
/-       simp [Nat.add_sub_cancel_left] -/
/-     ⟩ -/

def Array.chunks_exact(k: Nat)(arr: Array α): Array (Vector α k) :=
  assert! arr.size % k == 0
  if h: arr.size < k ∨ k = 0 then 
    #[]
  else
    #[⟨arr.extract (start:= 0) (stop := k), by simp_all [Nat.min_eq_left]⟩] ++ (arr.extract (start := k) (stop:= arr.size)).chunks_exact k
termination_by arr.size

/- def Vector.chunks_exact(k: Nat)[NeZero k](v: Vector α n): Vector (Vector α k) (n / k) := -/
/-   if h: v.size < k then -/ 
/-     have: n / k = 0 := Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero NeZero.out) |>.mpr (v.size_toArray ▸ h) -/
/-     this ▸ #v[] -/
/-   else -/
/-     let curr := v.extract (stop := k) -/
/-     let res := (arr.extract (start := k)).chunks_exact k -/

def Array.extract_size_of_chunks_exact(P: Array α)(r: Nat)
: let n := P.size / r
  ∀ (i: Fin n), (P.extract (r*i) (r*(i+1))).size = r
:= by
  intro n i
  obtain ⟨i, iLt⟩ := i
  simp
  if h: n = 0 then 
    rw [h] at iLt
    cases iLt
  else
    have: r*(i+1) <= P.size := by
      calc r*(i+1)
        _ <= r*(n-1+1) := by 
          apply Nat.mul_le_mul (Nat.le_of_eq rfl)
          simp
          apply Nat.le_sub_one_of_lt
          assumption
        _ =  r*n := by 
          have: 1 <= n := Nat.pos_of_ne_zero h
          have: (n + 1 - 1) = (n-1 + 1) := Nat.sub_add_comm this
          simp [←this]
        _ <= P.size := by simp [n]; rw [Nat.mul_comm]; exact Nat.div_mul_le_self P.size r
    simp [Nat.min_eq_left this]
    simp [←Nat.mul_sub_left_distrib _ _ _]
    simp [Nat.add_sub_self_left]

def Array.chunks (k: Nat)(arr: Array α): Array (Array α) := 
  if arr.size = 0 ∨ k = 0 then #[] else #[arr.take k] ++ (arr.extract k arr.size |>.chunks k)
termination_by arr.size

/- def String.zfill(s: String)(len: Nat) := List.asString <| -/
/-   (List.replicate (len - s.length) '0') ++ (s.take len).toList -/


def UInt8.toBitString(u: UInt8): Vector Bool 8 :=
  let bv := u.toBitVec
  #v[ (bv >>> 0) % 2 == 1,
      (bv >>> 1) % 2 == 1,
      (bv >>> 2) % 2 == 1,
      (bv >>> 3) % 2 == 1,
      (bv >>> 4) % 2 == 1,
      (bv >>> 5) % 2 == 1,
      (bv >>> 6) % 2 == 1,
      (bv >>> 7) % 2 == 1 ]

def Vector.ofArray(arr: Array α): Vector α arr.size := ⟨arr, rfl⟩

def Vector.joinBitVec(v: Vector (BitVec n) m): BitVec (n*m) := 
  if h: n = 0 then 
    by simpa [h] using 0#0
  else
    match m with
    | 0 => by simpa using 0#0
    | n+1 => let val := v[0]'(Nat.zero_lt_succ n) ++ joinBitVec (v.drop 1)
      by
        rw [Nat.mul_add, Nat.add_comm]
        simpa [Nat.add_sub_cancel] using val

def ByteArray.toBitVecLE(arr: ByteArray): BitVec (8*arr.size) :=
  (Vector.ofArray arr.data).map (·.toBitVec) |>.reverse |>.joinBitVec
def ByteArray.toBitVecBE(arr: ByteArray): BitVec (8*arr.size) :=
  (Vector.ofArray arr.data).map (·.toBitVec) |>.joinBitVec

def String.toBitVecLE(s: String) := ByteArray.toBitVecLE <| toUTF8 s
def String.toBitVecBE(s: String) := ByteArray.toBitVecBE <| toUTF8 s

def BitVec.toArray(bv: BitVec n): Array Bool := Array.finRange n |>.map (bv[·])
def BitVec.ofFn(f: Fin n → Bool): BitVec n := by simpa using BitVec.ofBoolListLE <| List.ofFn f
def BitVec.set(i:Fin n)(b: Bool)(bv: BitVec n): BitVec n := bv ^^^ (((bv[i] ^^ b).toNat : BitVec n) <<< i.val)

/- def Utils.toNat(S: Vector Bool n): Nat := S.mapIdx (2^· * if · then 1 else 0) |>.toList |>.sum -/
/- #eval Utils.toNat #v[true, false, true, true] -/
/- #eval BitVec.ofBoolListLE [true, false, true, true] |>.toNat -/
/- #eval BitVec.ofBoolListLE [true, false, false, false] |>.toNat -/
/- #eval BitVec.ofBoolListBE [true, false, false, false] |>.toNat -/
/- #eval 1#1 ++ 0#1 ++ 0#1 ++ 1#1 ++ 0#1 |>.toArray -/
/- #eval (0b10010#5).toArray -/
/- #check BitVec.high_truncate -- ??? -/

/- def Utils.toHex (S: Vector Bool n): String := S -/ 
/-   |> Utils.toNat -/
/-   |>.toDigits (base := 16) |>.asString -/

/- #eval Utils.toHex #v[true, false, true, true] -/
/- #eval (1101#4)[1:10] -/

def BitVec.toByteArray(bv: BitVec n): ByteArray :=
  let paddedLen := (n + 7)/8
  let bv' := bv.setWidth (paddedLen*8)
  ByteArray.mk <| Array.finRange paddedLen
    |>.map fun i =>
      let x := List.finRange 8 |>.map (fun o => 
        2^o.val * if bv'[8*i.val+o.val]'(by omega) then 1 else 0
      ) |>.sum
      UInt8.ofNat x

open Std.Format in 
def Utils.dump (S: BitVec n)(spacing? : Bool := false): Std.Format :=
  let final := S.toByteArray.data
    |>.map (·.toBitVec.toHex)
    |>.toList
    |> "".intercalate
  let singleSpace? := if spacing? then text " " else nil
  let lineBreak? := if spacing? then align false else nil
  let formatted := Array.mk final.toList
    |>.chunks 16
    |>.map (·.chunks 2 
      |>.map (fun v => text  <| v.toList.asString) 
      |>.toList 
      |> singleSpace?.joinSep
      |> group)
    |>.chunks 2
    |>.map (·.toList |> singleSpace?.joinSep)
    |>.toList
    |> lineBreak?.joinSep
    if spacing? then 
      nest 8 <| lineBreak? ++ formatted
    else
      formatted

/- open Std.Format in -/ 
/- def Utils.dump (S: BitVec n)(spacing? : Bool := false): Std.Format := --S.toNat.toDigits (base := 16) |>.asString -/
/-     let S: Vector Bool n := ⟨⟨List.finRange n |>.map (S[·])⟩, by simp⟩ -/
/-     let width := 8 -/
/-     let singleSpace? := if spacing? then text " " else nil -/
/-     let lineBreak? := if spacing? then align false else nil -/

/-     let final := S.adjust (width * ((S.size + width-1)/width)) false -/
/-       |>.chunks_exact width -/
/-       |>.map (fun lane => Utils.toHex lane |>.zfill (width/4)) -/
/-       |>.toList -/
/-       |> "".intercalate -/
/-       |>.zfill ((S.size + 3) / 4) -/
/-     let formatted := Array.mk final.toList -/
/-       |>.chunks 16 -/
/-       |>.map (·.chunks 2 -/ 
/-         |>.map (fun v => text  <| v.toList.asString) -/ 
/-         |>.toList -/ 
/-         |> singleSpace?.joinSep -/
/-         |> group) -/
/-       |>.chunks 2 -/
/-       |>.map (·.toList |> singleSpace?.joinSep) -/
/-       |>.toList -/
/-       |> lineBreak?.joinSep -/
/-     if spacing? then -/ 
/-       nest 8 <| lineBreak? ++ formatted -/
/-     else -/
/-       formatted -/

/- #eval Utils.dump (0b10010011#8) -/
/- #eval Utils.dump' (0b10010011#8) -/

/- #eval Utils.dump (0b1001001110101111#16) -/
/- #eval Utils.dump' (0b1001001110101111#16) -/

/- #eval Utils.dump (0b100100111010111101001011#24) -/
/- #eval Utils.dump' (0b100100111010111101001011#24) -/

/- #eval Utils.dump (0b10010011101011110100101100001000#22) -/
/- #eval Utils.dump' (0b10010011101011110100101100001000#32) -/
