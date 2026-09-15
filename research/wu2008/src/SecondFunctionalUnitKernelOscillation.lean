import SecondFunctionalUnitKernelVariation

open scoped BigOperators Classical
namespace SecondFunctionalUnitKernel
open Set Wu2008DoubleSieve SecondFunctionalUnitFiniteKernel

/-- The actual lower strict gate changes only in the accepted lower face. -/
theorem lower_change_face {m : ℕ} (phi : ℝ) (x y : Fin (m+1) → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i-y i| ≤ d)
    (hc : ¬ (x (Fin.last m) < phi - ∑ i, x i ↔
      y (Fin.last m) < phi - ∑ i, y i)) :
    x ∈ continuousLowerFace phi ((m+2 : ℝ)*d) := by
  have hv : |((∑ i, x i)+x (Fin.last m)) - ((∑ i, y i)+y (Fin.last m))| ≤
      (m+2 : ℝ)*d := by
    convert lower_variation phi x y hxy using 1
    rw [show (phi - ∑ i, x i - x (Fin.last m)) -
      (phi - ∑ i, y i - y (Fin.last m)) =
      -(((∑ i, x i)+x (Fin.last m)) - ((∑ i, y i)+y (Fin.last m))) by ring, abs_neg]
  have hc' : ¬ (row true ((∑ i, x i)+x (Fin.last m)) phi ↔
      row true ((∑ i, y i)+y (Fin.last m)) phi) := by
    simp only [row, ↓reduceIte]
    intro he
    apply hc
    constructor <;> intro h
    · have hh := he.mp (by linarith)
      linarith
    · have hh := he.mpr (by linarith)
      linarith
  have hh := row_change_band true hv hc'
  change |phi - ∑ i, x i - x (Fin.last m)| ≤ _
  rwa [show phi - ∑ i, x i - x (Fin.last m) = -(((∑ i, x i)+x (Fin.last m))-phi) by ring, abs_neg]

theorem cap_change_face {n : ℕ} (phi b : ℝ) (x y : Fin n → ℝ) {d : ℝ}
    (hxy : ∀ i, |x i-y i| ≤ d)
    (hc : ¬ (phi - ∑ i, x i < b ↔ phi - ∑ i, y i < b)) :
    x ∈ continuousCapFace phi b ((n : ℝ)*d) := by
  have hv : |(phi - ∑ i, x i) - (phi - ∑ i, y i)| ≤ (n : ℝ)*d := by
    simpa using cap_variation phi 0 x y hxy
  exact row_change_band true hv hc

/-- Both strict gates are supplied as active facts, never crossed by a Lipschitz claim. -/
theorem U_shared_active {m : ℕ} (phi b : ℝ) (x y : Fin (m+1) → ℝ) {d : ℝ}
    (hx : x ∈ continuousCube (m+1)) (hy : y ∈ continuousCube (m+1))
    (hxy : ∀ i, |x i-y i| ≤ d)
    (hax : x (Fin.last m) < phi - ∑ i, x i ∧ phi - ∑ i, x i < b)
    (hay : y (Fin.last m) < phi - ∑ i, y i ∧ phi - ∑ i, y i < b) :
    |U phi b x - U phi b y| ≤ 100*(m+1 : ℝ)*d := by
  rw [U_literal, U_literal, if_pos hax, if_pos hay]
  have hv := reciprocal_variation
    ((hx (Fin.last m) (mem_univ _)).1.trans hax.1.le)
    ((hy (Fin.last m) (mem_univ _)).1.trans hay.1.le)
  have hs := cap_variation phi 0 x y hxy
  simp only [sub_zero] at hs
  push_cast at hs
  nlinarith

/-- A jump costs ten, using the actual nonnegative range rather than twice a norm bound. -/
theorem G_jump_bound {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (x y : Fin (m+1) → ℝ)
    (hx : x ∈ continuousCube (m+1)) (hy : y ∈ continuousCube (m+1)) :
    |G phi b C gamma strict x - G phi b C gamma strict y| ≤ 10 := by
  have h1 := G_range phi b C gamma strict hx
  have h2 := G_range phi b C gamma strict hy
  apply abs_le.mpr
  constructor <;> linarith

/-- The complete pointwise estimate, including all literal closed jump bands. -/
theorem G_oscillation {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (x y : Fin (m+1) → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube (m+1)) (hy : y ∈ continuousCube (m+1))
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |G phi b C gamma strict x - G phi b C gamma strict y| ≤
      100*(m+1 : ℝ)*d +
      (if |phi - ∑ i, x i - x (Fin.last m)| ≤ (m+2 : ℝ)*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ (m+1 : ℝ)*d then 10 else 0) +
      ∑ q, (if |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d then 10 else 0) := by
  have hbase : 0 ≤ 100*(m+1 : ℝ)*d := by positivity
  have hl0 : 0 ≤ (if |phi - ∑ i, x i - x (Fin.last m)| ≤ (m+2 : ℝ)*d then (10 : ℝ) else 0) := by split_ifs <;> norm_num
  have hb0 : 0 ≤ (if |phi - ∑ i, x i - b| ≤ (m+1 : ℝ)*d then (10 : ℝ) else 0) := by split_ifs <;> norm_num
  have hrow0 (q : Fin r) : 0 ≤ (if |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d then (10 : ℝ) else 0) := by split_ifs <;> norm_num
  have hsum0 := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hrow0 q)
  have hj := G_jump_bound phi b C gamma strict x y hx hy
  by_cases hl : |phi - ∑ i, x i - x (Fin.last m)| ≤ (m+2 : ℝ)*d
  · rw [if_pos hl]
    linarith
  by_cases hb : |phi - ∑ i, x i - b| ≤ (m+1 : ℝ)*d
  · rw [if_pos hb]
    linarith
  by_cases hr : ∃ q, |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d
  · obtain ⟨q,hq⟩ := hr
    have hh := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => hrow0 q) (Finset.mem_univ q)
    rw [if_pos hq] at hh
    linarith
  have hs : ∀ q, ¬ |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d := by simpa using hr
  rw [if_neg hl, if_neg hb]
  simp only [if_neg (hs _), Finset.sum_const_zero, add_zero]
  have hlEq : x (Fin.last m) < phi - ∑ i, x i ↔ y (Fin.last m) < phi - ∑ i, y i := by
    by_contra hc
    exact hl (lower_change_face phi x y hxy hc)
  have hbEq : phi - ∑ i, x i < b ↔ phi - ∑ i, y i < b := by
    by_contra hc
    have hh := cap_change_face phi b x y hxy hc
    exact hb (by simpa [continuousCapFace, Nat.cast_add, Nat.cast_one] using hh)
  have hmEq : mask C gamma strict x ↔ mask C gamma strict y := by
    apply forall_congr'
    intro q
    by_contra hc
    exact hs q (affine_change_band (strict q) (C q) x y (gamma q) hxy hc)
  unfold G
  by_cases hm : mask C gamma strict x
  · rw [if_pos hm, if_pos (hmEq.mp hm)]
    by_cases ha : x (Fin.last m) < phi - ∑ i, x i ∧ phi - ∑ i, x i < b
    · exact U_shared_active phi b x y hx hy hxy ha ⟨hlEq.mp ha.1, hbEq.mp ha.2⟩
    · have hay : ¬ (y (Fin.last m) < phi - ∑ i, y i ∧ phi - ∑ i, y i < b) :=
        fun hh => ha ⟨hlEq.mpr hh.1, hbEq.mpr hh.2⟩
      rw [U_literal, U_literal, if_neg ha, if_neg hay, sub_self, abs_zero]
      exact hbase
  · rw [if_neg hm, if_neg (fun hh => hm (hmEq.mpr hh)), sub_self, abs_zero]
    exact hbase

/-- Empty extra mask: the two original strict faces remain. -/
theorem U_oscillation {m : ℕ} (phi b : ℝ) (x y : Fin (m+1) → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube (m+1)) (hy : y ∈ continuousCube (m+1))
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |U phi b x - U phi b y| ≤ 100*(m+1 : ℝ)*d +
      (if |phi - ∑ i, x i - x (Fin.last m)| ≤ (m+2 : ℝ)*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ (m+1 : ℝ)*d then 10 else 0) := by
  simpa only [G_empty, Finset.univ_eq_empty, Finset.sum_empty, add_zero] using
    G_oscillation phi b (Fin.elim0 : Fin 0 → Fin (m+1) → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Bool) x y hd hx hy hxy

/-- Zero diameter is admitted without any off-face premise. -/
theorem G_diameter_zero {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (x y : Fin (m+1) → ℝ)
    (hxy : ∀ i, |x i-y i| ≤ 0) : G phi b C gamma strict x = G phi b C gamma strict y := by
  have he : x = y := funext (fun i => sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hxy i) (abs_nonneg _))))
  rw [he]

theorem G_oscillation_fin4 {r : ℕ} (phi b : ℝ) (C : Fin r → Fin 4 → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (x y : Fin 4 → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube 4) (hy : y ∈ continuousCube 4)
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |G phi b C gamma strict x - G phi b C gamma strict y| ≤ 400*d +
      (if |phi - ∑ i, x i - x (Fin.last 3)| ≤ 5*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ 4*d then 10 else 0) +
      ∑ q, (if |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d then 10 else 0) := by
  have h := G_oscillation phi b C gamma strict x y hd hx hy hxy
  norm_num at h
  exact h

theorem U_oscillation_fin4 (phi b : ℝ) (x y : Fin 4 → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube 4) (hy : y ∈ continuousCube 4)
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |U phi b x - U phi b y| ≤ 400*d +
      (if |phi - ∑ i, x i - x (Fin.last 3)| ≤ 5*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ 4*d then 10 else 0) := by
  have h := U_oscillation phi b x y hd hx hy hxy
  norm_num at h
  exact h

theorem G_oscillation_fin5 {r : ℕ} (phi b : ℝ) (C : Fin r → Fin 5 → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (x y : Fin 5 → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube 5) (hy : y ∈ continuousCube 5)
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |G phi b C gamma strict x - G phi b C gamma strict y| ≤ 500*d +
      (if |phi - ∑ i, x i - x (Fin.last 4)| ≤ 6*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ 5*d then 10 else 0) +
      ∑ q, (if |dot (C q) x - gamma q| ≤ (∑ i, |C q i|)*d then 10 else 0) := by
  have h := G_oscillation phi b C gamma strict x y hd hx hy hxy
  norm_num at h
  exact h

theorem U_oscillation_fin5 (phi b : ℝ) (x y : Fin 5 → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (hx : x ∈ continuousCube 5) (hy : y ∈ continuousCube 5)
    (hxy : ∀ i, |x i-y i| ≤ d) :
    |U phi b x - U phi b y| ≤ 500*d +
      (if |phi - ∑ i, x i - x (Fin.last 4)| ≤ 6*d then 10 else 0) +
      (if |phi - ∑ i, x i - b| ≤ 5*d then 10 else 0) := by
  have h := U_oscillation phi b x y hd hx hy hxy
  norm_num at h
  exact h

end SecondFunctionalUnitKernel
