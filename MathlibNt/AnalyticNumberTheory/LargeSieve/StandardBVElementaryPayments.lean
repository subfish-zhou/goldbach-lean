

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanSmallRangeAndCharacters

/-!
 # Elementary scalar payments for Standard Bombieri--Vinogradov

This module closes the lanes which require no distributional input.  The only
analytic inputs left to a final Standard-BV consumer are the low-conductor
Siegel--Walfisz estimate and the high-conductor Type-I/II hybrid estimate.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

lemma reciprocalLogWeight_nonneg (n : ℕ) : 0 ≤ reciprocalLogWeight n := by
  unfold reciprocalLogWeight
  split_ifs
  · positivity
  · exact le_rfl

lemma reciprocalLogWeight_antitone_of_two_le
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    reciprocalLogWeight n ≤ reciprocalLogWeight m := by
  have hn : 2 ≤ n := hm.trans hmn
  simp only [reciprocalLogWeight, if_pos hm, if_pos hn]
  have hmlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast hmn)
  simpa only [one_div] using one_div_le_one_div_of_le hmlog hlog

/-- The total variation of the reciprocal-log Abel kernel is exactly its jump
at two, counted twice.  In particular the prefix maximum is uniformly bounded;
there is no logarithmic growth to pay. -/
theorem discreteAbelAmplifier_eq_two_inv_log_two
    {y : ℕ} (hy : 2 ≤ y) :
    discreteAbelAmplifier y = 2 * (Real.log 2)⁻¹ := by
  induction y, hy using Nat.le_induction with
  | base =>
      have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      simp [discreteAbelAmplifier, reciprocalLogWeight, Finset.sum_range_succ,
        abs_of_pos hlog]
      have harg : Real.log ((1 : ℝ) + 1) = Real.log 2 := by norm_num
      rw [harg, abs_of_pos hlog]
      ring
  | succ y hy ih =>
      have hmono : reciprocalLogWeight (y + 1) ≤ reciprocalLogWeight y :=
        reciprocalLogWeight_antitone_of_two_le hy (Nat.le_succ y)
      have hy0 := reciprocalLogWeight_nonneg y
      have hys0 := reciprocalLogWeight_nonneg (y + 1)
      unfold discreteAbelAmplifier at ih ⊢
      rw [abs_of_nonneg hy0] at ih
      rw [Finset.sum_range_succ, abs_of_nonneg hys0,
        abs_of_nonneg (sub_nonneg.mpr hmono)]
      linarith only [ih]

/-- Uniform explicit bound for the prefix-maximal Abel amplifier. -/
theorem discreteAbelAmplifierPrefixMax_le_two_inv_log_two (N : ℕ) :
    discreteAbelAmplifierPrefixMax N ≤ 2 * (Real.log 2)⁻¹ := by
  unfold discreteAbelAmplifierPrefixMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  by_cases h2 : 2 ≤ y
  · exact (discreteAbelAmplifier_eq_two_inv_log_two h2).le
  · have hlog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
    interval_cases y <;>
      norm_num [discreteAbelAmplifier, reciprocalLogWeight, hlog]

private lemma nonprincipalCharacters_card_le_totient
    {q : ℕ} (hq : 0 < q) :
    ((nonprincipalCharacters q).card : ℝ) ≤ q.totient := by
  have hchars : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    have horth := charOrthSum hq (1 : ZMod q) 1
    have hc : ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℂ) =
        (q.totient : ℂ) := by simpa using horth
    exact_mod_cast hc
  exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq
    (by simpa using hchars)

/-- The principal bad-prime lane is already a `Q` times polylogarithm. -/
theorem principalBadPhysical_le_explicit (N Q : ℕ) :
    principalBadPhysical N Q ≤
      (Q : ℝ) * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
  unfold principalBadPhysical
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q,
        (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφ : (1 : ℝ) ≤ q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hinv : ((q.totient : ℝ)⁻¹) ≤ 1 := by
        have hi := (inv_le_inv₀ (lt_of_lt_of_le (by norm_num) hφ)
          (by norm_num : (0 : ℝ) < 1)).2 hφ
        simpa using hi
      have hlogq : (Nat.log2 q : ℝ) ≤ Nat.log2 Q := by
        exact_mod_cast (by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right (Finset.mem_Icc.mp hq).2)
      have hrest : 0 ≤ (Nat.log2 N + 1 : ℝ) * Real.log N := by positivity
      calc
        ((q.totient : ℝ)⁻¹) *
            ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) ≤
            1 * ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
          gcongr
        _ ≤ (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
          nlinarith
    _ = ((Finset.Icc 1 Q).card : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by simp
    _ ≤ (Q : ℝ) *
        ((Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
      gcongr
      simp
    _ = _ := by ring

/-- The higher-prime-power lane is `Q (√N+1) log₂(N) log N`. -/
theorem primePowerPhysical_le_explicit (N Q : ℕ) :
    primePowerPhysical N Q ≤
      (Q : ℝ) * primePowerCorrectionExplicitBound N := by
  exact sum_lambdaPrimePowerCorrectionPrefixMaxError_le N Q

/-- Each direct conductor-change amplitude for `Λ` is polylogarithmic. -/
theorem vonMangoldt_conductorErrorAmplitude_le
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    conductorErrorAmplitude χ vonMangoldtIntegerCoeff N ≤
      2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N := by
  have hs := vonMangoldt_conductorErrorPrefixMaxSquare_le hq χ N
  rw [← conductorErrorAmplitude_sq] at hs
  have hx := conductorErrorAmplitude_nonneg χ vonMangoldtIntegerCoeff N
  have hC : 0 ≤ 2 * (Nat.log2 q : ℝ) *
      (Nat.log2 N + 1 : ℝ) * Real.log N := by positivity
  nlinarith

/-- The full unsquared conductor correction is only `Q` times a polylogarithm
(and therefore also a polylogarithm times `Q²`). -/
theorem directConductorCorrectionMean_vonMangoldt_le (N Q : ℕ) :
    directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤
      (Q : ℝ) *
        (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N) := by
  unfold directConductorCorrectionMean
  let C : ℝ :=
    2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, C := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφ : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hchar := nonprincipalCharacters_card_le_totient hq0
      have hqlog : (Nat.log2 q : ℝ) ≤ Nat.log2 Q := by
        exact_mod_cast (by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right (Finset.mem_Icc.mp hq).2)
      have hpoly :
          2 * (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N ≤ C := by
        dsimp [C]
        gcongr
      calc
        ((q.totient : ℝ)⁻¹) *
            (∑ χ ∈ nonprincipalCharacters q,
              conductorErrorAmplitude χ vonMangoldtIntegerCoeff N) ≤
            ((q.totient : ℝ)⁻¹) *
              (∑ _χ ∈ nonprincipalCharacters q, C) := by
          gcongr with χ hχ
          exact (vonMangoldt_conductorErrorAmplitude_le hq0 χ N).trans hpoly
        _ = ((q.totient : ℝ)⁻¹) *
              (((nonprincipalCharacters q).card : ℝ) * C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((q.totient : ℝ)⁻¹) * ((q.totient : ℝ) * C) := by
          gcongr
        _ = C := by field_simp
    _ = ((Finset.Icc 1 Q).card : ℝ) * C := by simp
    _ ≤ (Q : ℝ) * C := by
      gcongr
      simp
    _ = _ := by rfl

private lemma vonMangoldt_toNat_le_log_v_succ {n : ℤ} {v : ℕ}
    (hn : 1 ≤ n) (hnv : n.toNat ≤ v) :
    ArithmeticFunction.vonMangoldt n.toNat ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
  exact vonMangoldt_le_log_v_succ hn hnv

/-- Every primitive-character small Vaughan prefix is bounded directly by its
support length `v`; no large-sieve input is needed. -/
theorem vaughanSmall_primitivePrefixAmplitude_le
    (N q v : ℕ) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q χ ≤
      (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) := by
  let C : ℝ := (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmax : primitiveCharacterPrefixMaxSquare
      (vaughanSmallCoeff vaughanUnitIntegerCoeff v) 0 N q χ ≤ C ^ 2 := by
    unfold primitiveCharacterPrefixMaxSquare
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    unfold primitiveCharacterPrefixSquare
    simp only [zero_add]
    let S := (Finset.Icc (1 : ℤ) y).filter (fun n => n.toNat ≤ v)
    have heq :
        (∑ n ∈ Finset.Icc (1 : ℤ) y,
          vaughanSmallCoeff vaughanUnitIntegerCoeff v n * χ.1 (n : ZMod q)) =
        ∑ n ∈ S,
          vaughanSmallCoeff vaughanUnitIntegerCoeff v n * χ.1 (n : ZMod q) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hnI hnS
      have hnnot : ¬ n.toNat ≤ v := by
        intro h
        exact hnS (Finset.mem_filter.mpr ⟨hnI, h⟩)
      rw [vaughanSmallCoeff_eq_zero_of_v_lt_toNat _ _ (Nat.lt_of_not_ge hnnot)]
      simp
    rw [heq]
    have hnorm :
        ‖∑ n ∈ S,
          vaughanSmallCoeff vaughanUnitIntegerCoeff v n * χ.1 (n : ZMod q)‖ ≤ C := by
      calc
        _ ≤ ∑ n ∈ S,
            ‖vaughanSmallCoeff vaughanUnitIntegerCoeff v n *
              χ.1 (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ S, Real.log ((v + 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_filter.mp hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn'.1).1
          have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
          have hΛ := vonMangoldt_toNat_le_log_v_succ hn1 hn'.2
          rw [vaughanSmallCoeff_eq_of_toNat_le vaughanUnitIntegerCoeff v hn'.2,
            norm_mul, norm_mul]
          simp only [vaughanUnitIntegerCoeff, norm_one, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hΛ0]
          exact (mul_le_of_le_one_right hΛ0 (χ.1.norm_le_one _)).trans hΛ
        _ = (S.card : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) := by simp
        _ ≤ C := by
          dsimp [C]
          apply mul_le_mul_of_nonneg_right
          · have hcardS : S.card ≤ v := by
              simpa [S, vaughanSmallSupport] using card_vaughanSmallSupport_le y v
            exact_mod_cast hcardS
          · positivity
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [← primitivePrefixAmplitude_sq] at hmax
  nlinarith [primitivePrefixAmplitude_nonneg
    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q χ]

end

end AnalyticNumberTheory.LargeSieve
