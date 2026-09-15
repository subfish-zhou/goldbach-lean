import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDOriginal

/-!
# Large common modulus in the original W progression sum

Compatibility is retained until the common modulus has become a divisor
of the beta difference. The diagonal is separated before this divisor set
is formed. All additional arithmetic masks and signed weights are allowed.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Coprimality makes the product progression occupy at most one point
in each interval of length `d`. -/
theorem card_product_modEq_le (K d n : ℕ) (a : ℤ) (hn : n.Coprime d) :
    ((Icc 0 K).filter (fun m : ℕ ↦ Int.ModEq d ((m : ℤ) * n) a)).card ≤
      K / d + 1 := by
  calc
    _ ≤ (range (K / d + 1)).card := by
      apply card_le_card_of_injOn (fun m : ℕ ↦ m / d)
      · intro m hm
        exact mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hm).1).2))
      · intro m hm b hb he
        apply Nat.ext_div_modEq he
        apply Int.natCast_modEq_iff.mp
        exact (product_modEq_iff_of_coprime hn (mem_filter.mp hb).2).mp
          (mem_filter.mp hm).2
    _ = _ := card_range _

/-- A bound for the actual bump, not a postulated progression asymptotic. -/
theorem sum_cutoff_product_modEq_le {M : ℝ} (hM : 1 ≤ M)
    {d n : ℕ} (hd : 0 < d) (hn : n.Coprime d) (a : ℤ) :
    (∑ m ∈ dyadicCutoffNatSupport M,
      if Int.ModEq d ((m : ℤ) * n) a then scaledDyadicCutoff M m else 0) ≤
      4 * M / d + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hceil : (⌈3 * M⌉₊ : ℝ) ≤ 4 * M := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * M)
    linarith
  calc
    _ ≤ ∑ m ∈ dyadicCutoffNatSupport M,
        if Int.ModEq d ((m : ℤ) * n) a then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro m _
      split_ifs
      · exact scaledDyadicCutoff_le_one M m
      · rfl
    _ = (((Icc 0 ⌈3 * M⌉₊).filter
        (fun m : ℕ ↦ Int.ModEq d ((m : ℤ) * n) a)).card : ℝ) := by
      simp [dyadicCutoffNatSupport, sum_boole]
    _ ≤ (⌈3 * M⌉₊ / d + 1 : ℕ) := by
      exact_mod_cast card_product_modEq_le ⌈3 * M⌉₊ d n a hn
    _ ≤ (⌈3 * M⌉₊ : ℝ) / d + 1 := by
      push_cast
      gcongr
      exact Nat.cast_div_le
    _ ≤ _ := by gcongr

/-- An off-diagonal witness includes the progression condition on `m`.
Discarding that condition would lose the common-modulus saving. -/
def WLargeDeltaWitness (Y : ℝ) (a : ℤ) (n₁ n₂ m : ℕ) : Prop :=
  n₁ = n₂ ∨ ∃ d ∈ ((n₁ : ℤ) - n₂).natAbs.divisors,
    Y < (d : ℝ) ∧ n₁.Coprime d ∧ Int.ModEq d ((m : ℤ) * n₁) a

theorem wLargeDeltaWitness_of_compatible {Y : ℝ} {a : ℤ}
    {q r n₁ n₂ m : ℕ} (hc : WCompatible q r n₁ n₂)
    (hY : Y < (q.gcd r : ℝ)) (hm : Int.ModEq q ((m : ℤ) * n₁) a) :
    WLargeDeltaWitness Y a n₁ n₂ m := by
  by_cases he : n₁ = n₂
  · exact Or.inl he
  · apply Or.inr
    refine ⟨q.gcd r, Nat.mem_divisors.mpr ⟨?_, ?_⟩, hY,
      hc.1.of_dvd_right (Nat.gcd_dvd_left q r), ?_⟩
    · have hd := Int.modEq_iff_dvd.mp
        (Int.natCast_modEq_iff.mpr hc.2.2.symm)
      exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
    · apply Int.natAbs_ne_zero.mpr
      exact sub_ne_zero.mpr (by exact_mod_cast he)
    · exact hm.of_dvd (by exact_mod_cast Nat.gcd_dvd_left q r)

/-- The off-diagonal union bound is over divisors of a nonzero difference.
Each divisor is paid with its own product progression. -/
theorem sum_cutoff_largeDeltaWitness_le {M Y : ℝ} (hM : 1 ≤ M) (hY : 0 < Y)
    (a : ℤ) (n₁ n₂ : ℕ) (hne : n₁ ≠ n₂) :
    (∑ m ∈ dyadicCutoffNatSupport M,
      if WLargeDeltaWitness Y a n₁ n₂ m then scaledDyadicCutoff M m else 0) ≤
      (4 * M / Y + 1) * (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) := by
  let D := ((n₁ : ℤ) - n₂).natAbs.divisors.filter
    (fun d : ℕ ↦ Y < (d : ℝ) ∧ n₁.Coprime d)
  calc
    _ ≤ ∑ m ∈ dyadicCutoffNatSupport M, ∑ d ∈ D,
        if Int.ModEq d ((m : ℤ) * n₁) a then scaledDyadicCutoff M m else 0 := by
      apply sum_le_sum
      intro m _
      split_ifs with hw
      · obtain ⟨d, hd, hYd, hnd, hmd⟩ := hw.resolve_left hne
        have hs := single_le_sum (s := D)
          (f := fun d : ℕ ↦
            if Int.ModEq d ((m : ℤ) * n₁) a then scaledDyadicCutoff M m else 0)
          (fun e _ ↦ by split_ifs <;>
            first | rfl | exact scaledDyadicCutoff_nonneg M m)
          (mem_filter.mpr ⟨hd, hYd, hnd⟩)
        simpa only [if_pos hmd] using hs
      · exact sum_nonneg (fun d _ ↦ by
          split_ifs <;> first | rfl | exact scaledDyadicCutoff_nonneg M m)
    _ = ∑ d ∈ D, ∑ m ∈ dyadicCutoffNatSupport M,
        if Int.ModEq d ((m : ℤ) * n₁) a then scaledDyadicCutoff M m else 0 :=
      sum_comm
    _ ≤ ∑ _d ∈ D, (4 * M / Y + 1) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_, hYd, hnd⟩ := mem_filter.mp hd
      have hdR : (0 : ℝ) < d := hY.trans hYd
      exact (sum_cutoff_product_modEq_le hM (by exact_mod_cast hdR) hnd a).trans
        (by gcongr)
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul, mul_comm, fouvryTau_two]
      gcongr
      exact filter_subset _ _

/-- The modulus rows can be enlarged independently only after retaining
the existence of the large common divisor and its progression. -/
theorem wMaskedOriginal_abs_le_largeDelta_modulus_sums
    (M Y : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) :
    |wMaskedOriginal M N Q β c a P| ≤
      ∑ p ∈ N ×ˢ N, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) *
          (if WLargeDeltaWitness Y a p.1 p.2 m then 1 else 0) := by
  let F : WOriginalTuple → ℝ := fun t ↦ |wTupleCoefficient β c t| *
    ∑ m ∈ dyadicCutoffNatSupport M,
      if Int.ModEq t.1.1 ((m : ℤ) * t.2.1) a ∧
          Int.ModEq t.1.2 ((m : ℤ) * t.2.2) a then
        scaledDyadicCutoff M m *
          (if WLargeDeltaWitness Y a t.2.1 t.2.2 m then 1 else 0) else 0
  have hF (t : WOriginalTuple) : 0 ≤ F t := by
    apply mul_nonneg (abs_nonneg _)
    apply sum_nonneg
    intro m _
    split_ifs <;> simp [scaledDyadicCutoff_nonneg]
  have hw (q r n₁ n₂ : ℕ) : 0 ≤
      productProgressionWeight (dyadicCutoffNatSupport M)
        (fun m ↦ scaledDyadicCutoff M m) a q r n₁ n₂ := by
    apply sum_nonneg
    intro m _
    split_ifs <;> first | rfl | exact scaledDyadicCutoff_nonneg M m
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t| *
        productProgressionWeight (dyadicCutoffNatSupport M)
          (fun m ↦ scaledDyadicCutoff M m) a t.1.1 t.1.2 t.2.1 t.2.2 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (hw _ _ _ _)]
    _ = ∑ t ∈ wMaskedTuples N Q a P, F t := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨ho, hp⟩ := mem_filter.mp ht
      congr 1
      apply sum_congr rfl
      intro m _
      by_cases hm : Int.ModEq t.1.1 ((m : ℤ) * t.2.1) a ∧
          Int.ModEq t.1.2 ((m : ℤ) * t.2.2) a
      · simp only [if_pos hm, if_pos (wLargeDeltaWitness_of_compatible
          (mem_filter.mp ho).2 (hP t ho hp) hm.1), mul_one]
      · simp only [if_neg hm]
    _ ≤ ∑ t ∈ (Q ×ˢ Q) ×ˢ (N ×ˢ N), F t := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨ho, _⟩ := mem_filter.mp ht
        obtain ⟨hs, _⟩ := mem_filter.mp ho
        obtain ⟨hqr, hn⟩ := mem_product.mp hs
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
      simp only [sum_mul]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro q _
      dsimp [wTupleCoefficient]
      simp only [abs_mul]
      split_ifs <;> simp_all
      ring

/-- A finite quantitative estimate, separating the diagonal before forming
divisors of the difference. The row cap is needed only on the actual support. -/
theorem wMaskedOriginal_abs_le_largeDelta_row_cap
    {M Y A : ℝ} (hM : 1 ≤ M) (hY : 0 < Y) (hA : 0 ≤ A)
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hrow : ∀ n ∈ N, β n ≠ 0 → ∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 →
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ A)
    (P : WOriginalTuple → Prop)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) :
    |wMaskedOriginal M N Q β c a P| ≤
      A ^ 2 * ∑ p ∈ N ×ˢ N, |β p.1 * β p.2| *
        (if p.1 = p.2 then 5 * M else
          (4 * M / Y + 1) * (fouvryTau 2 ((p.1 : ℤ) - p.2).natAbs : ℝ)) := by
  have hr0 (m n : ℕ) : 0 ≤
      ∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0 := by
    apply sum_nonneg
    intro q _
    split_ifs <;> positivity
  calc
    _ ≤ ∑ p ∈ N ×ˢ N, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) *
          (if WLargeDeltaWitness Y a p.1 p.2 m then 1 else 0) :=
      wMaskedOriginal_abs_le_largeDelta_modulus_sums M Y N Q β c a P hP
    _ ≤ ∑ p ∈ N ×ˢ N, A ^ 2 * (|β p.1 * β p.2| *
        ∑ m ∈ dyadicCutoffNatSupport M,
          if WLargeDeltaWitness Y a p.1 p.2 m then scaledDyadicCutoff M m else 0) := by
      apply sum_le_sum
      intro p hp
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro m _
      by_cases hb₁ : β p.1 = 0
      · simp [hb₁]
      by_cases hb₂ : β p.2 = 0
      · simp [hb₂]
      by_cases hm : scaledDyadicCutoff M m = 0
      · simp [hm]
      split_ifs
      · simp only [mul_one]
        have hh := mul_le_mul (hrow _ (mem_product.mp hp).1 hb₁ m hm)
          (hrow _ (mem_product.mp hp).2 hb₂ m hm) (hr0 _ _) hA
        have hnon := mul_nonneg (abs_nonneg (β p.1 * β p.2))
          (scaledDyadicCutoff_nonneg M m)
        nlinarith [mul_le_mul_of_nonneg_left hh hnon]
      · simp
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      split_ifs with he
      · simpa only [WLargeDeltaWitness, he, true_or, if_true] using
          sum_scaledDyadicCutoff_le hM
      · exact sum_cutoff_largeDeltaWitness_le hM hY a p.1 p.2 he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
