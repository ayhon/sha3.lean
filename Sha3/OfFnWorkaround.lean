def Array.ofFn' {n} (f : Fin n → α) : Array α := go (Array.emptyWithCapacity n) n (Nat.le_refl n) where
  go (acc : Array α) : (i : Nat) → i ≤ n → Array α
  | i + 1, h =>
     have w : n - i - 1 < n :=
       Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.sub_ne_zero_iff_lt.mpr h)) (Nat.sub_le n i)
     go (acc.push (f ⟨n - i - 1, w⟩)) i (Nat.le_of_succ_le h)
  | 0, _ => acc

@[simp] theorem Array.size_ofFn'_go {n} {f : Fin n → α} {i acc h} :
    (ofFn'.go f acc i h).size = acc.size + i := by
  induction i generalizing acc with
  | zero => simp [ofFn'.go]
  | succ i ih =>
    simpa [ofFn'.go, ih] using Nat.succ_add_eq_add_succ acc.size i
@[simp] theorem Array.size_ofFn' {n : Nat} {f : Fin n → α} : (ofFn' f).size = n := by simp [ofFn']

theorem Array.getElem_ofFn'_go {f : Fin n → α} {acc: Array α}{i k}(h : i ≤ n) (w₁ : k < acc.size + i) :
    (ofFn'.go f acc i h)[k]'(by simpa using w₁) =
      if w₂ : k < acc.size then acc[k] else f ⟨n - i + k - acc.size, by omega⟩ := by
  induction i generalizing acc k with
  | zero =>
    simp at w₁
    simp_all [ofFn'.go]
  | succ i ih =>
    unfold ofFn'.go
    rw [ih]
    · simp only [Array.size_push]
      split <;> rename_i h'
      · rw [Array.getElem_push]
        split
        · rfl
        · congr 2
          omega
      · split
        · omega
        · congr 2
          omega
    · simp
      omega

@[simp] theorem Array.getElem_ofFn' {f : Fin n → α} {i : Nat} (h : i < (ofFn' f).size) :
    (ofFn' f)[i] = f ⟨i, Array.size_ofFn' (f := f) ▸ h⟩ := by
  unfold ofFn'
  rw [getElem_ofFn'_go] <;> simp_all

@[inline] def Vector.ofFn' (f : Fin n → α) : Vector α n := ⟨Array.ofFn' f, by simp⟩

@[simp] theorem Vector.getElem_ofFn' {f : Fin n → α} {i : Nat} (h : i < n) :
    (Vector.ofFn' f)[i] = f ⟨i, h⟩ := by
  unfold ofFn'; rw [Vector.getElem_mk, Array.getElem_ofFn']

@[simp] theorem Vector.getElem!_ofFn' [Inhabited α]{f : Fin n → α} {i : Nat} (h : i < n) :
    (Vector.ofFn' f)[i]! = f ⟨i, h⟩ := by rw [getElem!_pos, Vector.getElem_ofFn']
