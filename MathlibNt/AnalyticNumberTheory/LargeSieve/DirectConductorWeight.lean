

import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear

/-!
 # Direct reciprocal-totient conductor multiplicity

This module proves the finite arithmetic estimate needed by the direct L¹
conductor regrouping.  It is independent of the Vaughan decomposition.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The exact conductor multiplicity for a direct `1 / φ(q)` character sum. -/
def directConductorWeight (Q d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q with d ∣ q, ((q.totient : ℝ)⁻¹)

/-- Rewrite the levels divisible by a positive `d` as `q = d r`. -/
theorem directConductorWeight_eq_sum_multiples
    (Q d : ℕ) (hd : 0 < d) :
    directConductorWeight Q d =
      ∑ r ∈ Finset.Icc 1 (Q / d), (((d * r).totient : ℝ)⁻¹) := by
  rw [directConductorWeight]
  symm
  refine Finset.sum_bij (fun r _ => d * r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨Nat.mul_pos hd hr'.1,
      (Nat.mul_le_mul_left d hr'.2).trans (Nat.mul_div_le Q d)⟩,
      dvd_mul_right d r⟩
  · intro r₁ hr₁ r₂ hr₂ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine ⟨q / d, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hq'.1).1 hq'.2) hd,
        Nat.div_le_div_right (Finset.mem_Icc.mp hq'.1).2⟩
    · exact Nat.mul_div_cancel' hq'.2
  · intro r hr
    rfl

/-- Totient supermultiplicativity separates a reciprocal totient. -/
theorem multiple_inv_totient_le_product
    (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    (((d * r).totient : ℝ)⁻¹) ≤
      ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
  have hφnat : d.totient * r.totient ≤ (d * r).totient :=
    Nat.totient_super_multiplicative d r
  have hφ : (d.totient : ℝ) * (r.totient : ℝ) ≤ ((d * r).totient : ℝ) := by
    exact_mod_cast hφnat
  have hprod : (0 : ℝ) < (d.totient : ℝ) * (r.totient : ℝ) := by positivity
  calc
    (((d * r).totient : ℝ)⁻¹)
      ≤ (((d.totient : ℝ) * (r.totient : ℝ))⁻¹) :=
        inv_anti₀ hprod hφ
    _ = ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
      rw [mul_inv]

/-- The reciprocal totient is bounded by `τ(r) / r`. -/
theorem inv_totient_le_card_divisors_div
    (r : ℕ) (hr : 0 < r) :
    ((r.totient : ℝ)⁻¹) ≤ (r.divisors.card : ℝ) / r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := totientRatio_le_card_divisors r hr
  calc
    ((r.totient : ℝ)⁻¹) = ((r : ℝ) / (r.totient : ℝ)) / r := by
      field_simp
    _ ≤ (r.divisors.card : ℝ) / r :=
      div_le_div_of_nonneg_right h hrR.le

/-- Reciprocal sum over multiples of `e`, written with the complementary factor. -/
private theorem sum_inv_multiples_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0) =
      (e : ℝ)⁻¹ * conductorHarmonicFactor (R / e) := by
  rw [← Finset.sum_filter]
  symm
  rw [conductorHarmonicFactor, Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => e * k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    exact ⟨⟨Nat.mul_pos he hk.1,
      (Nat.mul_le_mul_left e hk.2).trans (Nat.mul_div_le R e)⟩,
      dvd_mul_right e k⟩
  · intro k₁ hk₁ k₂ hk₂ h
    exact Nat.eq_of_mul_eq_mul_left he h
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    refine ⟨r / e, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd hr.1.1 hr.2) he,
        Nat.div_le_div_right hr.1.2⟩
    · exact Nat.mul_div_cancel' hr.2
  · intro k hk
    push_cast
    rw [← mul_inv]

/-- The finite divisor-harmonic double sum is at most the square of the harmonic sum. -/
theorem sum_card_divisors_div_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r) ≤
      conductorHarmonicFactor R ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r)
      = ∑ r ∈ Finset.Icc 1 R,
          ∑ e ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hset : r.divisors = (Finset.Icc 1 R).filter (fun e => e ∣ r) := by
          ext e
          rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · intro he
            exact ⟨⟨Nat.pos_of_dvd_of_pos he.1 (Finset.mem_Icc.mp hr).1,
              (Nat.le_of_dvd (by omega : 0 < r) he.1).trans
                (Finset.mem_Icc.mp hr).2⟩, he.1⟩
          · intro he
            exact ⟨he.2, Nat.ne_of_gt (Finset.mem_Icc.mp hr).1⟩
        rw [hset, div_eq_mul_inv]
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul,
          Finset.sum_filter]
        simp
    _ = ∑ e ∈ Finset.Icc 1 R,
          ∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        exact Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * conductorHarmonicFactor (R / e) := by
        apply Finset.sum_congr rfl
        intro e he
        exact sum_inv_multiples_Icc R e (Finset.mem_Icc.mp he).1
    _ ≤ ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * conductorHarmonicFactor R := by
        apply Finset.sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left
        · unfold conductorHarmonicFactor
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.div_le_self R e)
          · intro k hk hnot
            positivity
        · positivity
    _ = conductorHarmonicFactor R ^ 2 := by
        rw [conductorHarmonicFactor, ← Finset.sum_mul]
        ring

/-- Finite average reciprocal-totient bound. -/
theorem sum_inv_totient_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, ((r.totient : ℝ)⁻¹)) ≤
      conductorHarmonicFactor R ^ 2 := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r := by
      apply Finset.sum_le_sum
      intro r hr
      exact inv_totient_le_card_divisors_div r (Finset.mem_Icc.mp hr).1
    _ ≤ _ := sum_card_divisors_div_le_harmonic_sq R

/-- The harmonic factor is monotone in its natural cutoff. -/
theorem conductorHarmonicFactor_mono {R S : ℕ} (hRS : R ≤ S) :
    conductorHarmonicFactor R ≤ conductorHarmonicFactor S := by
  unfold conductorHarmonicFactor
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hRS
  · intro e he hnot
    positivity

/-- Strong unconditional direct conductor-weight bound, including `d = 0`,
`d > Q`, and hence all empty-fibre cases.  Unlike the compatibility majorant
below, the primitive weight is exactly `1 / φ(d)`: no factor `d` is inserted. -/
theorem directConductorWeight_le (Q d : ℕ) :
    directConductorWeight Q d ≤
      conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ) := by
  by_cases hd : d = 0
  · subst d
    have hempty : (Finset.Icc 1 Q).filter (fun q => 0 ∣ q) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
        iff_false]
      intro hq
      obtain ⟨c, hc⟩ := hq.2
      simp only [Nat.zero_mul] at hc
      omega
    rw [directConductorWeight, hempty]
    simp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  rw [directConductorWeight_eq_sum_multiples Q d hdpos]
  calc
    (∑ r ∈ Finset.Icc 1 (Q / d), (((d * r).totient : ℝ)⁻¹))
      ≤ ∑ r ∈ Finset.Icc 1 (Q / d),
          ((d.totient : ℝ)⁻¹) * ((r.totient : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro r hr
        exact multiple_inv_totient_le_product d r hdpos (Finset.mem_Icc.mp hr).1
    _ = ((d.totient : ℝ)⁻¹) *
          ∑ r ∈ Finset.Icc 1 (Q / d), ((r.totient : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ ((d.totient : ℝ)⁻¹) * conductorHarmonicFactor (Q / d) ^ 2 := by
        gcongr
        exact sum_inv_totient_le_harmonic_sq (Q / d)
    _ ≤ ((d.totient : ℝ)⁻¹) * conductorHarmonicFactor Q ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact sq_le_sq₀ (conductorHarmonicFactor_nonneg _) (conductorHarmonicFactor_nonneg _) |>.2
            (conductorHarmonicFactor_mono (Nat.div_le_self Q d))
        · positivity
    _ = conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ) := by
        rw [div_eq_mul_inv]
        ring

/-- Compatibility-only weakening to the historical square-large-sieve weight
`d / φ(d)`.  New direct L¹ assembly should use `directConductorWeight_le` and
the AP-normalized primitive mean instead. -/
theorem directConductorWeight_le_compatibility_majorant (Q d : ℕ) :
    directConductorWeight Q d ≤
      conductorHarmonicFactor Q ^ 2 * ((d : ℝ) / (d.totient : ℝ)) := by
  refine (directConductorWeight_le Q d).trans ?_
  by_cases hd : d = 0
  · subst d
    simp
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
  have hinv : 0 ≤ (d.totient : ℝ)⁻¹ := by positivity
  have hH : 0 ≤ conductorHarmonicFactor Q ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hinv]

end

end AnalyticNumberTheory.LargeSieve
