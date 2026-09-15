import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryModulusSupport

/-!
# Sparse-modulus exclusion in the original progression sum

The elementary progression-counting part of Fouvry (1984), p. 236, (8.5).
Coprimality is retained in the sparse modulus row until the actual bump
progression is counted. Absolute values are taken before enlarging any mask.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The sparse row retains the coprimality needed for the progression count. -/
def wOriginalSparseRow (Q S : Finset ℕ) (c : ℕ → ℝ) (a : ℤ) (n m : ℕ) : ℝ :=
  ∑ q ∈ Q, if q ∈ S ∧ n.Coprime q ∧ Int.ModEq q ((m : ℤ) * n) a
    then |c q| else 0

theorem wOriginalSparseRow_nonneg (Q S : Finset ℕ) (c : ℕ → ℝ)
    (a : ℤ) (n m : ℕ) : 0 ≤ wOriginalSparseRow Q S c a n m := by
  apply sum_nonneg
  intro q _
  split_ifs <;> positivity

/-- Harmonic mass pays the main progression count, and counting mass pays
its endpoint error. This estimate is uniform in the beta index and residue. -/
theorem sum_cutoff_wOriginalSparseRow_le {M L Z A : ℝ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hZ : 0 < Z) (hA : 0 ≤ A)
    (Q S : Finset ℕ) (hS : S ⊆ largeSquareDivisorSet ⌊L⌋₊ Z)
    (c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ A) (a : ℤ) (n : ℕ) :
    (∑ m ∈ dyadicCutoffNatSupport M,
      scaledDyadicCutoff M m * wOriginalSparseRow Q S c a n m) ≤
      A * (8 * M * (1 + Real.log L) + 2 * L) / Z := by
  let R := Q.filter (fun q => q ∈ S ∧ n.Coprime q)
  have hR : R ⊆ largeSquareDivisorSet ⌊L⌋₊ Z := by
    intro q hq
    exact hS (mem_filter.mp hq).2.1
  have hh : (∑ q ∈ R, (1 : ℝ) / q) ≤ (2 / Z) * (1 + Real.log L) :=
    (sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => by positivity)).trans
      (sum_one_div_largeSquareDivisorSet_le hL hZ)
  have hcard : (R.card : ℝ) ≤ 2 * L / Z :=
    (Nat.cast_le.mpr (card_le_card hR)).trans
      (card_largeSquareDivisorSet_le_real (by linarith) hZ)
  calc
    _ = ∑ q ∈ R, |c q| * ∑ m ∈ dyadicCutoffNatSupport M,
        if Int.ModEq q ((m : ℤ) * n) a then scaledDyadicCutoff M m else 0 := by
      simp only [wOriginalSparseRow, mul_sum, R, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      split_ifs with hq
      · apply sum_congr rfl
        intro m _
        simp only [hq.1, Nat.Coprime, hq.2, true_and]
        split_ifs <;> ring
      · apply sum_eq_zero
        intro m _
        simp only [not_and] at hq
        split_ifs with hm
        · exact False.elim (hq hm.1 hm.2.1)
        · simp
    _ ≤ ∑ q ∈ R, A * (4 * M / q + 1) := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0 < q := (mem_Ioc.mp (mem_filter.mp (hR hq)).1).1
      exact mul_le_mul (hc q (mem_filter.mp hq).1)
        (sum_cutoff_product_modEq_le hM hq0 (mem_filter.mp hq).2.2 a)
        (sum_nonneg (fun m _ => by
          split_ifs <;> first | rfl | exact scaledDyadicCutoff_nonneg M m)) hA
    _ = A * (4 * M * (∑ q ∈ R, (1 : ℝ) / q) + R.card) := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro q _
        ring
      · ring
    _ ≤ A * (4 * M * ((2 / Z) * (1 + Real.log L)) + 2 * L / Z) := by
      gcongr
    _ = _ := by ring

/-- The two sparse strips majorize any further mask. In particular no
symmetry of that mask and no sign restriction on either weight is required. -/
theorem wMaskedOriginal_abs_le_sparse_modulus_sums
    (M : ℝ) (N Q S : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.1.1 ∈ S ∨ t.1.2 ∈ S) :
    |wMaskedOriginal M N Q β c a P| ≤
      ∑ p ∈ N ×ˢ N, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (wOriginalSparseRow Q S c a p.1 m *
            (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) +
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
            wOriginalSparseRow Q S c a p.2 m) := by
  let F : WOriginalTuple → ℝ := fun t =>
    |wTupleCoefficient β c t| * ∑ m ∈ dyadicCutoffNatSupport M,
      if Int.ModEq t.1.1 ((m : ℤ) * t.2.1) a ∧
          Int.ModEq t.1.2 ((m : ℤ) * t.2.2) a then
        scaledDyadicCutoff M m *
          ((if t.1.1 ∈ S ∧ t.2.1.Coprime t.1.1 then 1 else 0) +
            (if t.1.2 ∈ S ∧ t.2.2.Coprime t.1.2 then 1 else 0)) else 0
  have hF (t : WOriginalTuple) : 0 ≤ F t := by
    apply mul_nonneg (abs_nonneg _)
    apply sum_nonneg
    intro m _
    have hm := scaledDyadicCutoff_nonneg M m
    split_ifs <;> positivity
  have hw (q r n₁ n₂ : ℕ) : 0 ≤
      productProgressionWeight (dyadicCutoffNatSupport M)
        (fun m => scaledDyadicCutoff M m) a q r n₁ n₂ := by
    apply sum_nonneg
    intro m _
    split_ifs <;> first | rfl | exact scaledDyadicCutoff_nonneg M m
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t| *
        productProgressionWeight (dyadicCutoffNatSupport M)
          (fun m => scaledDyadicCutoff M m) a t.1.1 t.1.2 t.2.1 t.2.2 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (hw _ _ _ _)]
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, F t := by
      apply sum_le_sum
      intro t ht
      obtain ⟨ho, hp⟩ := mem_filter.mp ht
      have hcompat := (mem_filter.mp ho).2
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply sum_le_sum
      intro m _
      dsimp only
      by_cases hm : Int.ModEq t.1.1 ((m : ℤ) * t.2.1) a ∧
          Int.ModEq t.1.2 ((m : ℤ) * t.2.2) a
      · simp only [if_pos hm]
        rcases hP t ho hp with hs | hs
        · rw [if_pos ⟨hs, hcompat.1⟩]
          split_ifs <;> nlinarith [scaledDyadicCutoff_nonneg M m]
        · rw [if_pos (show t.1.2 ∈ S ∧ t.2.2.Coprime t.1.2 from ⟨hs, hcompat.2.1⟩)]
          split_ifs <;> nlinarith [scaledDyadicCutoff_nonneg M m]
      · simp only [if_neg hm, le_refl]
    _ ≤ ∑ t ∈ (Q ×ˢ Q) ×ˢ (N ×ˢ N), F t := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨ho, _⟩ := mem_filter.mp ht
        obtain ⟨hqr, hn⟩ := mem_product.mp (mem_filter.mp ho).1
        obtain ⟨hq, hr⟩ := mem_product.mp hqr
        exact mem_product.mpr ⟨mem_product.mpr
          ⟨(mem_filter.mp hq).1, (mem_filter.mp hr).1⟩, hn⟩
      · intro t _ _
        exact hF t
    _ = _ := by
      rw [sum_product, sum_comm]
      apply sum_congr rfl
      intro p _
      simp only [sum_product, F, mul_sum]
      rw [sum_comm]
      conv_lhs => arg 2; ext r; rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      simp only [wOriginalSparseRow, mul_add, mul_sum, sum_mul,
        ← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro q _
      dsimp [wTupleCoefficient]
      simp only [abs_mul, ← and_assoc]
      by_cases hq : q ∈ S ∧ p.1.Coprime q <;>
        by_cases hr : r ∈ S ∧ p.2.Coprime r <;>
        by_cases hqm : Int.ModEq q ((m : ℤ) * p.1) a <;>
        by_cases hrm : Int.ModEq r ((m : ℤ) * p.2) a <;>
        simp_all only [Nat.Coprime, and_true, and_false, if_true, if_false,
          mul_one, mul_zero, zero_mul, add_zero, zero_add] <;> ring

/-- A finite row-cap estimate for the original sum. The unrestricted row
cap is only required where both beta and the actual bump are nonzero. -/
theorem wMaskedOriginal_abs_le_sparse_row_cap {M L Z A B : ℝ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hZ : 0 < Z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (N Q S : Finset ℕ) (hS : S ⊆ largeSquareDivisorSet ⌊L⌋₊ Z)
    (β c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ A) (a : ℤ)
    (hrow : ∀ n ∈ N, β n ≠ 0 → ∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 →
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ B)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.1.1 ∈ S ∨ t.1.2 ∈ S) :
    |wMaskedOriginal M N Q β c a P| ≤
      2 * A * B * (8 * M * (1 + Real.log L) + 2 * L) *
        (∑ n ∈ N, |β n|) ^ 2 / Z := by
  let E := A * (8 * M * (1 + Real.log L) + 2 * L) / Z
  have hE (n : ℕ) :
      (∑ m ∈ dyadicCutoffNatSupport M,
        scaledDyadicCutoff M m * wOriginalSparseRow Q S c a n m) ≤ E :=
    sum_cutoff_wOriginalSparseRow_le hM hL hZ hA Q S hS c hc a n
  calc
    _ ≤ ∑ p ∈ N ×ˢ N, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (wOriginalSparseRow Q S c a p.1 m *
            (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) +
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
            wOriginalSparseRow Q S c a p.2 m) :=
      wMaskedOriginal_abs_le_sparse_modulus_sums M N Q S β c a P hP
    _ ≤ ∑ p ∈ N ×ˢ N, |β p.1 * β p.2| * B * (E + E) := by
      apply sum_le_sum
      intro p hp
      calc
        _ ≤ ∑ m ∈ dyadicCutoffNatSupport M,
            |β p.1 * β p.2| * B *
              (scaledDyadicCutoff M m * wOriginalSparseRow Q S c a p.1 m +
                scaledDyadicCutoff M m * wOriginalSparseRow Q S c a p.2 m) := by
          apply sum_le_sum
          intro m _
          by_cases hb₁ : β p.1 = 0
          · simp [hb₁]
          by_cases hb₂ : β p.2 = 0
          · simp [hb₂]
          by_cases hm : scaledDyadicCutoff M m = 0
          · simp [hm]
          have hh := add_le_add
            (mul_le_mul_of_nonneg_left
              (hrow p.2 (mem_product.mp hp).2 hb₂ m hm)
              (wOriginalSparseRow_nonneg Q S c a p.1 m))
            (mul_le_mul_of_nonneg_right
              (hrow p.1 (mem_product.mp hp).1 hb₁ m hm)
              (wOriginalSparseRow_nonneg Q S c a p.2 m))
          calc
            _ ≤ |β p.1 * β p.2| * scaledDyadicCutoff M m *
                (wOriginalSparseRow Q S c a p.1 m * B +
                  B * wOriginalSparseRow Q S c a p.2 m) :=
              mul_le_mul_of_nonneg_left hh
                (mul_nonneg (abs_nonneg _) (scaledDyadicCutoff_nonneg M m))
            _ = _ := by ring
        _ = |β p.1 * β p.2| * B *
            ((∑ m ∈ dyadicCutoffNatSupport M,
              scaledDyadicCutoff M m * wOriginalSparseRow Q S c a p.1 m) +
              ∑ m ∈ dyadicCutoffNatSupport M,
                scaledDyadicCutoff M m * wOriginalSparseRow Q S c a p.2 m) := by
          rw [← mul_sum, sum_add_distrib]
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hE p.1) (hE p.2))
          (mul_nonneg (abs_nonneg _) hB)
    _ = _ := by
      simp only [E, sum_product, abs_mul, ← mul_sum, ← sum_mul, pow_two]
      ring

/-- Uniform original-W square-root saving for either canonical supported
modulus factor. The constant depends only on the divisor order and exponent,
not on the changing residue, supports, scales, signed weights, or further mask.
No relation between `L` and `M` is imposed. -/
theorem wMaskedOriginal_abs_le_modulus_support (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T L x Y : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → M * T ≤ x → L ≤ x → 0 < Y →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t →
          Y < ((wGCDTuple t).δ₁ : ℝ) ∨ Y < ((wGCDTuple t).δ₂ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * (1 + Real.log L) + L) *
          (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 2 by linarith)
  refine ⟨16 * D ^ 2 * (4 : ℝ) ^ ε, by positivity, ?_⟩
  intro M T L x Y hM hT hL hMT hLx hY N Q hN hQ β c hc a ha hs P hP
  have hx : 1 ≤ x := hL.trans hLx
  let A := D * (4 * x) ^ (ε / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc' (q : ℕ) (hq : q ∈ Q) : |c q| ≤ A := by
    have hqx : (q : ℝ) ≤ x :=
      (by exact_mod_cast (mem_Ioc.mp (hQ hq)).2 : (q : ℝ) ≤ ⌊L⌋₊).trans
        ((Nat.floor_le (by linarith)).trans hLx)
    calc
      _ ≤ (fouvryTau j q : ℝ) := hc q hq
      _ ≤ (fouvryTau (j + 1) q : ℝ) := by exact_mod_cast fouvryTau_le_succ j q
      _ ≤ D * (q : ℝ) ^ (ε / 2) := hdiv q (mem_Ioc.mp (hQ hq)).1
      _ ≤ A := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)) hD.le
  have hrow (n : ℕ) (hn : n ∈ N) (hβn : β n ≠ 0)
      (m : ℕ) (hm : scaledDyadicCutoff M m ≠ 0) :
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ A := by
    have hne := mul_sub_ne_zero_of_not_dvd m n a (hs n hn hβn)
    have hnT : (n : ℝ) ≤ T :=
      (by exact_mod_cast (mem_Ioc.mp (hN hn)).2 : (n : ℝ) ≤ ⌊T⌋₊).trans
        (Nat.floor_le (by linarith))
    calc
      _ ≤ (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) :=
        sum_modEq_abs_le_fouvryTau j Q c hc m n a hne
      _ ≤ D * (((m : ℤ) * n - a).natAbs : ℝ) ^ (ε / 2) :=
        hdiv _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
      _ ≤ A := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity)
          (natAbs_mul_sub_le_of_cutoff (by linarith) hMT hnT hm a ha)
          (by linarith)) hD.le
  have hAsq : A ^ 2 = D ^ 2 * (4 : ℝ) ^ ε * x ^ ε := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * x)]
    norm_num
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 0 ≤ x)]
    ring
  let S := largeSquareDivisorSet ⌊L⌋₊ (Real.sqrt Y)
  have hPS : ∀ t ∈ wOriginalTuples N Q a, P t → t.1.1 ∈ S ∨ t.1.2 ∈ S := by
    intro t ht hp
    obtain ⟨hqr, _⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨hq, hr⟩ := mem_product.mp hqr
    rcases hP t ht hp with hδ | hδ
    · exact Or.inl (deltaOne_mem_largeSquareDivisorSet _ _ _
        (hQ (mem_filter.mp hq).1) hY.le hδ)
    · exact Or.inr (deltaTwo_mem_largeSquareDivisorSet _ _ _
        (hQ (mem_filter.mp hr).1) hY.le hδ)
  calc
    _ ≤ 2 * A * A * (8 * M * (1 + Real.log L) + 2 * L) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y :=
      wMaskedOriginal_abs_le_sparse_row_cap hM hL (Real.sqrt_pos.mpr hY)
        hA hA N Q S (fun _ h => h) β c hc' a hrow P hPS
    _ ≤ 2 * A * A * (8 * (M * (1 + Real.log L) + L)) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by
      gcongr
      linarith
    _ = 16 * A ^ 2 * (M * (1 + Real.log L) + L) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by ring
    _ = _ := by rw [hAsq]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
