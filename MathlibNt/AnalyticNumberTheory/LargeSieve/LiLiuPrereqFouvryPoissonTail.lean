import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWZeroMode

/-!
# Uniform rapid truncation of the retained Poisson series

The error constant depends only on the requested power and the fixed bump.
The estimate remains uniform when the period exceeds the smoothing scale.
-/

noncomputable section

open scoped FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def dyadicPoissonTail (t x : ℝ) (H : ℕ) (h : ℤ) : ℂ :=
  if h.natAbs ≤ H then 0 else dyadicCutoffPoissonRemainder t x h

theorem dyadicPoissonTail_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ, ∀ H : ℕ,
      Summable (fun h : ℤ ↦ ‖dyadicPoissonTail t x H h‖) ∧
        ‖∑' h : ℤ, dyadicPoissonTail t x H h‖ ≤ C / (1 + t * H) ^ k := by
  obtain ⟨C, hC, hdecay⟩ :=
    schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) (k + 2)
  refine ⟨2 * C, by positivity, fun t ht x H ↦ ?_⟩
  obtain ⟨hs, hb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hp (h : ℤ) :
      ‖dyadicPoissonTail t x H h‖ ≤
        (C / (1 + t * H) ^ k) * poissonNonzeroDecay t h := by
    by_cases hh : h.natAbs ≤ H
    · simp only [dyadicPoissonTail, if_pos hh, norm_zero]
      unfold poissonNonzeroDecay
      split_ifs <;> positivity
    · have hne : h ≠ 0 := by intro hz; subst h; simp at hh
      have hH : (H : ℝ) ≤ |(h : ℝ)| := by
        have hi : (H : ℤ) ≤ |h| := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hh))
        exact_mod_cast hi
      have hbase : 1 + t * (H : ℝ) ≤ 1 + |t * (h : ℝ)| := by
        rw [abs_mul, abs_of_pos ht]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hH ht.le) 1
      have hpow : (1 + t * (H : ℝ)) ^ k ≤ (1 + |t * (h : ℝ)|) ^ k :=
        pow_le_pow_left₀ (by positivity) hbase k
      simp only [dyadicPoissonTail, if_neg hh, dyadicCutoffPoissonRemainder,
        if_neg hne, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one, poissonNonzeroDecay]
      calc
        _ ≤ t * (C / (1 + |t * (h : ℝ)|) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left (hdecay (t * h)) ht.le
        _ = (C * t / (1 + |t * (h : ℝ)|) ^ 2) /
            (1 + |t * (h : ℝ)|) ^ k := by
          simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ (C * t / (1 + |t * (h : ℝ)|) ^ 2) / (1 + t * H) ^ k :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = _ := by ring
  have hn : Summable (fun h : ℤ ↦ ‖dyadicPoissonTail t x H h‖) :=
    (hs.mul_left (C / (1 + t * H) ^ k)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) hp
  refine ⟨hn, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  calc
    _ ≤ ∑' h : ℤ, (C / (1 + t * H) ^ k) * poissonNonzeroDecay t h :=
      hn.tsum_le_tsum hp (hs.mul_left _)
    _ = (C / (1 + t * H) ^ k) * ∑' h : ℤ, poissonNonzeroDecay t h :=
      tsum_mul_left
    _ ≤ (C / (1 + t * H) ^ k) * 2 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Splitting off finitely many frequencies does not discard their phases. -/
theorem dyadicPoissonRemainder_eq_truncation {t : ℝ} (ht : 0 < t)
    (x : ℝ) (H : ℕ) :
    (∑' h : ℤ, dyadicCutoffPoissonRemainder t x h) =
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, dyadicCutoffPoissonRemainder t x h) +
        ∑' h : ℤ, dyadicPoissonTail t x H h := by
  classical
  let g : ℤ → ℂ := fun h ↦
    if h ∈ Finset.Icc (-(H : ℤ)) H then dyadicCutoffPoissonRemainder t x h else 0
  have hmem (h : ℤ) : h ∈ Finset.Icc (-(H : ℤ)) H ↔ h.natAbs ≤ H := by
    rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs]
    exact_mod_cast (Iff.rfl : h.natAbs ≤ H ↔ h.natAbs ≤ H)
  have hg : Summable g := summable_of_ne_finset_zero
    (s := Finset.Icc (-(H : ℤ)) H) (fun h hh ↦ by simp only [g, if_neg hh])
  obtain ⟨C, _, htail⟩ := dyadicPoissonTail_uniform 0
  have hr := (htail t ht x H).1.of_norm
  have he : dyadicCutoffPoissonRemainder t x =
      fun h ↦ g h + dyadicPoissonTail t x H h := by
    funext h
    by_cases hh : h.natAbs ≤ H <;> simp [g, hmem, dyadicPoissonTail, hh]
  calc
    _ = ∑' h : ℤ, (g h + dyadicPoissonTail t x H h) := congrArg tsum he
    _ = (∑' h : ℤ, g h) + ∑' h : ℤ, dyadicPoissonTail t x H h := hg.tsum_add hr
    _ = _ := by
      congr 1
      rw [tsum_eq_sum (s := Finset.Icc (-(H : ℤ)) H)
        (fun h hh ↦ by simp only [g, if_neg hh])]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [g, if_pos hh]

theorem wPoissonFrequency_truncation_error (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ q r : ℕ, q ≠ 0 → r ≠ 0 →
      ∀ a : ℤ, ∀ n₁ n₂ H : ℕ,
      ‖(∑' h : ℤ, wPoissonFrequency M a q r n₁ n₂ h) -
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H, wPoissonFrequency M a q r n₁ n₂ h‖ ≤
        C / (1 + (M / (q.lcm r : ℝ)) * H) ^ k := by
  obtain ⟨C, hC, htail⟩ := dyadicPoissonTail_uniform k
  refine ⟨C, hC, fun M hM q r hq hr a n₁ n₂ H ↦ ?_⟩
  have ht : 0 < M / (q.lcm r : ℝ) :=
    div_pos hM (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq hr)))
  unfold wPoissonFrequency
  rw [dyadicPoissonRemainder_eq_truncation ht, add_sub_cancel_left]
  exact (htail _ ht _ H).2

/-- The finite oscillatory sum, with a separate cutoff for each modulus pair. -/
def truncatedWNonzeroMode (M : ℝ) (H : ℕ → ℕ → ℕ)
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    ∑ n₁ ∈ N, ∑ n₂ ∈ N,
      if WCompatible q r n₁ n₂ then
        (c q * c r * β n₁ * β n₂) *
          (∑ h ∈ Finset.Icc (-(H q r : ℤ)) (H q r),
            wPoissonFrequency M a q r n₁ n₂ h).re
      else 0

/-- A quantitative truncation of the actual W remainder. No cancellation of
the retained finite Kloosterman-type sum is assumed. -/
theorem smoothWNonzeroMode_truncation_error (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ H : ℕ → ℕ → ℕ,
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ, (∀ q ∈ Q, q ≠ 0) →
      |smoothWNonzeroMode M N Q β c a - truncatedWNonzeroMode M H N Q β c a| ≤
        C * ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          ∑ n₁ ∈ N, ∑ n₂ ∈ N,
            if WCompatible q r n₁ n₂ then
              |c q * c r * β n₁ * β n₂| /
                (1 + (M / (q.lcm r : ℝ)) * H q r) ^ k
            else 0 := by
  classical
  obtain ⟨C, hC, hbound⟩ := wPoissonFrequency_truncation_error k
  refine ⟨C, hC, fun M hM H N Q β c a hQ ↦ ?_⟩
  unfold smoothWNonzeroMode truncatedWNonzeroMode
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n₁ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n₂ _
  by_cases hc : WCompatible q r n₁ n₂
  · simp only [if_pos hc]
    rw [← mul_sub, abs_mul, ← Complex.sub_re]
    calc
      _ ≤ |c q * c r * β n₁ * β n₂| *
          (C / (1 + (M / (q.lcm r : ℝ)) * H q r) ^ k) :=
        mul_le_mul_of_nonneg_left
          ((Complex.abs_re_le_norm _).trans
            (hbound M hM q r (hQ q (Finset.mem_filter.mp hq).1)
              (hQ r (Finset.mem_filter.mp hr).1) a n₁ n₂ (H q r))) (abs_nonneg _)
      _ = _ := by ring
  · simp only [if_neg hc, sub_self, abs_zero, mul_zero, le_refl]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
