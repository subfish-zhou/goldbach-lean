import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetTransport

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace G12OutsideBudget

/-- A fixed positive power absorbs the entire numerical transport constant. -/
theorem scalar_log_saving (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℝ in atTop, 2 ≤ n ∧
      80 * (1 + Real.log n)^2 / n^δ ≤ 1 / (Real.log n)^B := by
  have h := (isLittleO_log_rpow_rpow_atTop (B+2 : ℕ) hδ).bound
    (by norm_num : (0 : ℝ) < 1/320)
  filter_upwards [h, eventually_ge_atTop (max 2 (Real.exp 1))] with n hn hn0
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn0
  have hnpos : 0 < n := by linarith
  have hl1 : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).mpr ((le_max_right _ _).trans hn0)
  have hlpos : 0 < Real.log n := by linarith
  have hb : (Real.log n)^(B+2) ≤ (1/320 : ℝ)*n^δ := by
    simpa only [Real.norm_eq_abs, Real.rpow_natCast,
      abs_of_nonneg (pow_nonneg hlpos.le _),
      abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] using hn
  refine ⟨hn2,?_⟩
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos δ)).mpr
  rw [show 1 / (Real.log n)^B * n^δ = n^δ / (Real.log n)^B by ring]
  apply (le_div_iff₀ (pow_pos hlpos B)).mpr
  have hs : (1 + Real.log n)^2 ≤ 4 * (Real.log n)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg hlpos.le B)
  rw [pow_add] at hb
  calc
    (80 * (1 + Real.log n)^2) * (Real.log n)^B ≤
        320 * ((Real.log n)^B * (Real.log n)^2) := by nlinarith
    _ ≤ n^δ := by linarith

/-- The external denominator has a fixed positive power at every Q >= N^sigma. -/
theorem denominator_lower {n Q η σ : ℝ} (hn : 0 ≤ n) (hη : 0 < η)
    (hηsmall : η < 1/8) (hQ : n^σ ≤ Q) :
    n^(σ*((1+η+η^9)⁻¹*η^2)) ≤ (externalInternalLevel Q η)^(η^2) := by
  have hc : 0 < 1+η+η^9 := by linarith [(external_dilation_bounds hη hηsmall).1]
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hn _) hQ
    (mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg η))
  rw [← Real.rpow_mul hn] at h
  have hQ0 : 0 ≤ Q := (Real.rpow_nonneg hn _).trans hQ
  simpa only [externalInternalLevel, ← Real.rpow_mul hQ0] using h

/-- The threshold precedes every submother, epsilon, cutoff and actual family.
The tag cardinality is retained rather than assumed bounded. -/
theorem family_log_saving (B : ℕ) {η σ : ℝ}
    (hη : 0 < η) (hηsmall : η < 1/8) (hσ : 0 < σ) :
    ∀ᶠ N : ℕ in atTop, ∀ (ε : ℝ) (A : Finset GoldbachG12LinkedAtom),
      A ⊆ goldbachG12LinkedAtoms N ε → ∀ Z Q : ℝ,
      (N : ℝ)^σ ≤ Q → Q ≤ N → 2 ≤ externalInternalLevel Q η →
      (∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z,
        |outside N A Z Q
          (externalTerm true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z t)|) ≤
        ((externalTags true (goldbachB10SiftingPrimes N Z) (externalInternalLevel Q η) η Z).card : ℝ) *
          N / (Real.log N)^B := by
  let δ := σ*((1+η+η^9)⁻¹*η^2)
  have hc : 0 < 1+η+η^9 := by linarith [(external_dilation_bounds hη hηsmall).1]
  have hδ : 0 < δ := mul_pos hσ (mul_pos (inv_pos.mpr hc) (sq_pos_of_pos hη))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (scalar_log_saving B hδ)] with N hN
  intro ε A hA Z Q hQl hQu hD
  have hN2 : 2 ≤ N := by exact_mod_cast hN.1
  have hN0 : (0 : ℝ) < N := by linarith [hN.1]
  have hQ1 : 1 ≤ Q := (Real.one_le_rpow (by linarith : (1 : ℝ) ≤ N) hσ.le).trans hQl
  have hf1 : (1 : ℝ) ≤ (⌊Q⌋₊ : ℕ) := by
    exact_mod_cast (Nat.le_floor (by simpa only [Nat.cast_one] using hQ1) : 1 ≤ ⌊Q⌋₊)
  have hfN : (⌊Q⌋₊ : ℝ) ≤ N := (Nat.floor_le (by linarith : 0 ≤ Q)).trans hQu
  have hlog : Real.log (⌊Q⌋₊ : ℕ) ≤ Real.log N :=
    Real.log_le_log (by linarith) hfN
  have hlog0 : 0 ≤ Real.log (⌊Q⌋₊ : ℕ) := Real.log_nonneg hf1
  have hs : (1 + Real.log (⌊Q⌋₊ : ℕ))^2 ≤ (1 + Real.log N)^2 := by nlinarith
  have hden := denominator_lower hN0.le hη hηsmall hQl
  have hpow : 0 < (N : ℝ)^δ := Real.rpow_pos_of_pos hN0 δ
  have hcoef : 20 * (4 / (externalInternalLevel Q η)^(η^2)) *
      (1 + Real.log (⌊Q⌋₊ : ℕ))^2 ≤ 1 / (Real.log N)^B := by
    calc
      _ ≤ 20 * (4 / (externalInternalLevel Q η)^(η^2)) * (1 + Real.log N)^2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20 * (4 / (N : ℝ)^δ) * (1 + Real.log N)^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) hpow hden)
            (by norm_num)) (sq_nonneg _)
      _ = 80 * (1 + Real.log N)^2 / (N : ℝ)^δ := by ring
      _ ≤ _ := hN.2
  have hb := family_budget hN2 ε A hA Z Q η hD hη hηsmall
  have hm := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ ((externalTags true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z).card : ℝ) * N by positivity)
  calc
    _ ≤ _ := hb
    _ ≤ _ := by
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hm

end G12OutsideBudget
