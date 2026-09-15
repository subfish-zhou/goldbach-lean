import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureTriple

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- Actual closed prime interval mass; the discrepancy includes endpoint atoms. -/
theorem primeSlab_interval_mass {R A B : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
    (∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤
      4 + primeOrderedDiscrepancy R := by
  have hd := (le_abs_self _).trans
    (primeOrdered_reciprocal_Icc_uniform_bound hR hs hA hAB hB)
  have hi := (primeOrdered_exponent_density_bounds hA hAB hB).2
  linarith

/-- Width-sensitive density bound on the fixed exponent cube. -/
theorem primeSlab_density_width {A B : ℝ}
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) :
    (∫ t in A..B, 1 / t) ≤ 10 * (B - A) := by
  have ha : 0 < A := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1 / t) (uIcc A B) :=
    continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (ha.trans_le ((uIcc_of_le hAB ▸ ht).1)))
  have h := intervalIntegral.integral_mono_on (μ := volume) hAB hc.intervalIntegrable
    (intervalIntegrable_const (c := (10 : ℝ)))
    (fun t ht => (div_le_iff₀ (ha.trans_le ht.1)).2 (by linarith [ht.1]))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- Public closed-coordinate bridge, including both endpoints. -/
theorem primeSlab_coordinate_mem {R A B : ℝ} (hR : 1 < R)
    {p : ℕ} (hp : p ∈ primesIcc (R ^ A) (R ^ B)) :
    log p / log R ∈ Icc A B := by
  have hR0 : 0 < R := by linarith
  have h := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hp
  have hl := log_le_log (rpow_pos_of_pos hR0 _) h.2.1
  have hu := log_le_log (by exact_mod_cast h.1.pos : (0 : ℝ) < p) h.2.2
  rw [log_rpow hR0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hR)).2 hl, (div_le_iff₀ (log_pos hR)).2 hu⟩

/-- The genuine one-coordinate affine slab. The finite minimum and maximum
avoid sign conventions for negative coefficients and handle singleton atoms. -/
theorem primeSlab_one_coordinate {R c γ η : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hc : 1 ≤ |c|) (hη : 0 ≤ η) :
    (∑ p ∈ (primesIcc (R ^ (1 / 10 : ℝ)) (R ^ (1 / 2 : ℝ))).filter
      (fun p : ℕ => |c * (log p / log R) - γ| ≤ η), 1 / (p : ℝ)) ≤
      20 * η + primeOrderedDiscrepancy R := by
  let S := (primesIcc (R ^ (1 / 10 : ℝ)) (R ^ (1 / 2 : ℝ))).filter
    (fun p : ℕ => |c * (log p / log R) - γ| ≤ η)
  change (∑ p ∈ S, 1 / (p : ℝ)) ≤ _
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    let b := S.max' hn
    have ha := mem_filter.mp (S.min'_mem hn)
    have hb := mem_filter.mp (S.max'_mem hn)
    have hpa := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp ha.1
    have hpb := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hb.1
    let A := log a / log R
    let B := log b / log R
    have hAc := primeSlab_coordinate_mem hR ha.1
    have hBc := primeSlab_coordinate_mem hR hb.1
    have hab : a ≤ b := S.min'_le _ (S.max'_mem hn)
    have hAB : A ≤ B := div_le_div_of_nonneg_right
      (log_le_log (by exact_mod_cast hpa.1.pos) (by exact_mod_cast hab)) (log_pos hR).le
    have hw : B - A ≤ 2 * η := by
      have hd := (abs_sub_le (c * B - γ) (0 : ℝ) (c * A - γ))
      simp only [sub_zero, zero_sub, abs_neg] at hd
      have he : c * B - γ - (c * A - γ) = c * (B - A) := by ring
      rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hAB)] at hd
      have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hAB)
      dsimp [A, B, a, b] at hd hm ⊢
      linarith [ha.2, hb.2]
    have hsub : S ⊆ primesIcc (R ^ A) (R ^ B) := by
      rw [primeOrdered_coordinate_rpow hR hpa.1, primeOrdered_coordinate_rpow hR hpb.1]
      intro p hp
      rw [mem_primesIcc (Nat.cast_nonneg b)]
      refine ⟨((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp
        (mem_filter.mp hp).1).1, ?_, ?_⟩
      · exact_mod_cast S.min'_le p hp
      · exact_mod_cast S.le_max' p hp
    have hm := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity :
      ∀ p ∈ primesIcc (R ^ A) (R ^ B), p ∉ S → (0 : ℝ) ≤ 1 / p)
    have hd := (le_abs_self _).trans
      (primeOrdered_reciprocal_Icc_uniform_bound hR hs hAc.1 hAB hBc.2)
    have hi := primeSlab_density_width hAc.1 hAB
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, sum_empty]
    exact add_nonneg (mul_nonneg (by norm_num) hη) (primeOrderedDiscrepancy_nonneg hR)

end Wu2008DoubleSieve

