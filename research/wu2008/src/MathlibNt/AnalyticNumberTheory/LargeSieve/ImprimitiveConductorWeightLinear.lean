

import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeight

/-!
 # Linear-polylogarithmic control of imprimitive conductor multiplicity

This independent strengthening replaces the quadratic fibre estimate by the
average order of the divisor function.  The proof is completely finite:
`n = ∑ d ∣ n, φ(d)` bounds `n / φ(n)` by the number of divisors, the divisor
sum is transposed, and the resulting harmonic sum is bounded by a telescoping
logarithm.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- A finite harmonic factor, including exactly the terms `1, ..., R`. -/
def conductorHarmonicFactor (R : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 R, (e : ℝ)⁻¹

theorem conductorHarmonicFactor_nonneg (R : ℕ) :
    0 ≤ conductorHarmonicFactor R := by
  unfold conductorHarmonicFactor
  positivity

/-- Enlarging the finite harmonic range can only increase its sum. -/
private theorem conductorHarmonicFactor_mono : Monotone conductorHarmonicFactor := by
  intro R S hRS
  unfold conductorHarmonicFactor
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hRS
  · intro e _ _
    positivity

private theorem harmonic_step (k : ℕ) (hk : 0 < k) :
    (((k + 1 : ℕ) : ℝ)⁻¹) ≤
      Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkspos : (0 : ℝ) < k + 1 := by positivity
  have hratio : (0 : ℝ) < (k : ℝ) / (k + 1 : ℝ) := div_pos hkpos hkspos
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hkspos)] at hlog
  have hid : (k : ℝ) / (k + 1 : ℝ) - 1 = -((k + 1 : ℝ)⁻¹) := by
    field_simp
    ring
  rw [hid] at hlog
  norm_num only [Nat.cast_add, Nat.cast_one] at hlog ⊢
  linarith

/-- The elementary telescoping logarithm bound for the finite harmonic factor. -/
theorem conductorHarmonicFactor_le (R : ℕ) :
    conductorHarmonicFactor R ≤ 1 + Real.log (R : ℝ) := by
  induction R with
  | zero => simp [conductorHarmonicFactor]
  | succ R ih =>
      by_cases hR : R = 0
      · subst R; norm_num [conductorHarmonicFactor]
      · rw [conductorHarmonicFactor, Finset.sum_Icc_succ_top (by omega)]
        rw [conductorHarmonicFactor] at ih
        have hs := harmonic_step R (Nat.pos_of_ne_zero hR)
        norm_num only [Nat.cast_add, Nat.cast_one] at hs ⊢
        linarith

/-- Divisor-sum control of one totient ratio. -/
theorem totientRatio_le_card_divisors (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) ≤ (n.divisors.card : ℝ) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  nth_rw 1 [← Nat.sum_totient n]
  rw [Nat.cast_sum, Finset.sum_div]
  calc
    (∑ d ∈ n.divisors, (d.totient : ℝ) / (n.totient : ℝ))
      ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        apply (div_le_one hφ).2
        exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hn)
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = (n.divisors.card : ℝ) := by simp

/-- For fixed positive `e`, count its multiples up to `R`. -/
theorem sum_dvd_indicator_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0) = (R / e : ℕ) := by
  symm
  rw [← Finset.sum_filter]
  calc
    ((R / e : ℕ) : ℝ) = ∑ k ∈ Finset.Icc 1 (R / e), (1 : ℝ) := by simp
    _ = ∑ r ∈ (Finset.Icc 1 R).filter (fun r => e ∣ r), (1 : ℝ) := by
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
        simp

/-- The finite average order of `r / φ(r)`, with an explicit harmonic factor. -/
theorem sum_totientRatio_le_linear_harmonic (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (r : ℝ) / (r.totient : ℝ)) ≤
      (R : ℝ) * conductorHarmonicFactor R := by
  calc
    (∑ r ∈ Finset.Icc 1 R, (r : ℝ) / (r.totient : ℝ))
      ≤ ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact totientRatio_le_card_divisors r (Finset.mem_Icc.mp hr).1
    _ = ∑ r ∈ Finset.Icc 1 R,
          ∑ e ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hset : r.divisors = (Finset.Icc 1 R).filter (fun e => e ∣ r) := by
          ext e
          rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · intro he
            exact ⟨⟨Nat.pos_of_dvd_of_pos he.1 (Finset.mem_Icc.mp hr).1,
              (Nat.le_of_dvd (by omega : 0 < r) he.1).trans (Finset.mem_Icc.mp hr).2⟩, he.1⟩
          · intro he
            exact ⟨he.2, (Nat.ne_of_gt (Finset.mem_Icc.mp hr).1)⟩
        rw [hset]
        simp
    _ = ∑ e ∈ Finset.Icc 1 R,
          ∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0 := by
        exact Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 R, ((R / e : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        exact sum_dvd_indicator_Icc R e (Finset.mem_Icc.mp he).1
    _ ≤ ∑ e ∈ Finset.Icc 1 R, (R : ℝ) * (e : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro e he
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = (R : ℝ) * conductorHarmonicFactor R := by
        rw [conductorHarmonicFactor, Finset.mul_sum]


/-- Multiplication by a conductor separates at the cost of `r / φ(r)`. -/
theorem multiple_totient_ratio_le_product
    (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ) ≤
      ((d : ℝ) / (d.totient : ℝ)) * ((r : ℝ) / (r.totient : ℝ)) := by
  have hφnat : d.totient * r.totient ≤ (d * r).totient :=
    Nat.totient_super_multiplicative d r
  have hφ : (d.totient : ℝ) * (r.totient : ℝ) ≤ ((d * r).totient : ℝ) := by
    exact_mod_cast hφnat
  have hden : (0 : ℝ) < (d.totient : ℝ) * (r.totient : ℝ) := by
    positivity
  calc
    ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ)
      ≤ ((d * r : ℕ) : ℝ) / ((d.totient : ℝ) * (r.totient : ℝ)) := by
        exact div_le_div_of_nonneg_left (by positivity) hden hφ
    _ = ((d : ℝ) / (d.totient : ℝ)) * ((r : ℝ) / (r.totient : ℝ)) := by
        push_cast
        field_simp

/-- Strong imprimitive conductor bound: linear, rather than quadratic, in `Q/d`. -/
theorem imprimitiveConductorWeight_le_linear_harmonic
    (Q d : ℕ) (hd : 0 < d) :
    imprimitiveConductorWeight Q d ≤
      ((d : ℝ) / (d.totient : ℝ)) *
        ((Q / d : ℕ) : ℝ) * conductorHarmonicFactor (Q / d) := by
  rw [imprimitiveConductorWeight_eq_sum_multiples Q d hd]
  calc
    (∑ r ∈ Finset.Icc 1 (Q / d),
        ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ))
      ≤ ∑ r ∈ Finset.Icc 1 (Q / d),
          ((d : ℝ) / (d.totient : ℝ)) * ((r : ℝ) / (r.totient : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact multiple_totient_ratio_le_product d r hd (Finset.mem_Icc.mp hr).1
    _ = ((d : ℝ) / (d.totient : ℝ)) *
          ∑ r ∈ Finset.Icc 1 (Q / d), ((r : ℝ) / (r.totient : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ((d : ℝ) / (d.totient : ℝ)) *
          (((Q / d : ℕ) : ℝ) * conductorHarmonicFactor (Q / d)) := by
        gcongr
        exact sum_totientRatio_le_linear_harmonic (Q / d)
    _ = _ := by ring

/-- Linear-harmonic conductor transport for an arbitrary nonnegative family.
The existing prefix theorem is a specialization of this finite inequality. -/
theorem imprimitive_conductor_window_le_weighted_primitive_linear
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hF : ∀ d ψ, 0 ≤ F d ψ) (Q C : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C),
      imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
        ∑ d ∈ Finset.Icc 1 (2 * C),
          ((d : ℝ) / (d.totient : ℝ)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
  have hsum (d : ℕ) : 0 ≤ ∑ ψ : PrimitiveCharacter d, F d ψ :=
    Finset.sum_nonneg fun ψ _ => hF d ψ
  calc
    _ ≤ ∑ d ∈ Finset.Icc C (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : 0 < d := hC.trans_le (Finset.mem_Icc.mp hd).1
      have hdiv : Q / d ≤ Q / C :=
        Nat.div_le_div_left (Finset.mem_Icc.mp hd).1 hC
      have hharm : conductorHarmonicFactor (Q / d) ≤ conductorHarmonicFactor (Q / C) := by
        unfold conductorHarmonicFactor
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hdiv
        · intro e he hnot
          positivity
      have hharm0 : 0 ≤ conductorHarmonicFactor (Q / d) :=
        conductorHarmonicFactor_nonneg _
      apply mul_le_mul_of_nonneg_right _ (hsum d)
      refine (imprimitiveConductorWeight_le_linear_harmonic Q d hd0).trans ?_
      gcongr
    _ ≤ ∑ d ∈ Finset.Icc 1 (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨hC.trans_le (Finset.mem_Icc.mp hd).1,
          (Finset.mem_Icc.mp hd).2⟩
      · intro d hd hnot
        have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
        have hφ0 : (0 : ℝ) < d.totient := by
          exact_mod_cast Nat.totient_pos.mpr hd0
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg (by positivity) hφ0.le) (by positivity))
            (conductorHarmonicFactor_nonneg _)) (hsum d)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring


/-- Dyadic-window transport with only the linear-harmonic conductor loss. -/
theorem imprimitive_conductor_window_prefix_le_linear
    (b : ℤ → ℂ) (M : ℤ) (N Q D : ℕ) (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D (2 * D),
      imprimitiveConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare b M N d ψ) ≤
      ((Q / D : ℕ) : ℝ) * conductorHarmonicFactor (Q / D) *
        ∑ d ∈ Finset.Icc 1 (2 * D),
          ((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d,
              primitiveCharacterPrefixMaxSquare b M N d ψ := by
  exact imprimitive_conductor_window_le_weighted_primitive_linear
    (fun d ψ => primitiveCharacterPrefixMaxSquare b M N d ψ)
    (fun d ψ => primitiveCharacterPrefixMaxSquare_nonneg b M N d ψ) Q D hD



end

end AnalyticNumberTheory.LargeSieve
