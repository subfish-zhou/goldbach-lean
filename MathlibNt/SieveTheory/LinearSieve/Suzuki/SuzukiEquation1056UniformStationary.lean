import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMinusFirstCrossingProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1056ScalarAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Uniform stationary exclusion and non-circular minus-parameter selection

The key input from source Lemma 10.27 is kept as an adjacent-value comparison,
not as the desired scalar inequality.  Division by the positive `s * R s`
and the stationary equation give `(10.46)`, namely
`ξ(s)-c-2/s = R(s-1)/(sR(s)) ≥ 1-K/s`.  Consequently the cutoff below depends
on the comparison constants (and hence on `R`) but not on `c`.
-/

namespace Section10Equation1056UniformStationary

set_option autoImplicit false
set_option maxHeartbeats 2400000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053
open Section10Equation1053NonCircular
open Section10Equation1053MinusFirstCrossing
open Section10Equation1053KernelExpansion
open Section10Equation1056ScalarAbsorption
open Section10MinusFirstCrossingProducer
open Section10CanonicalXi

/-- Source Lemma 10.27 in the precise comparison form used here.  The adjoint
argument in the source produces this estimate for `R`; no scalar kernel bound,
stationary exclusion, or conclusion of (10.56) is stored in this packet. -/
structure Lemma1027AdjointRComparison (R : ℝ → ℝ) where
  K : ℝ
  cutoff : ℝ
  K_nonneg : 0 ≤ K
  comparison : ∀ s, cutoff ≤ s →
    (1 - K / s) * (s * R s) ≤ R (s - 1)

/-- The cutoff-aware minus majorant produced after the single compact choice.
This is the same six-field contract consumed by the cutoff-corrected Section-13
ratio argument. -/
structure QhatMinusMajorant (R : ℝ → ℝ) where
  cMinus : ℝ
  cutoff : ℝ
  A : ℝ
  four_le_cutoff : 4 ≤ cutoff
  one_le_A : 1 ≤ A
  majorizes_log : ∀ s, cutoff ≤ s →
    (1 / A) * Real.log (Real.exp 1 * s) ≤ xi s - cMinus - 2 / s
  envelope_slope_nonpos : ∀ s, cutoff ≤ s →
    -(R (s - 1)) + s * (xi s - cMinus - 2 / s) * R s ≤ 0

/-- A fixed cutoff depending only on the Lemma-10.27 comparison constants. -/
noncomputable def stationaryCutoff {R : ℝ → ℝ}
    (h27 : Lemma1027AdjointRComparison R) : ℝ :=
  max h27.cutoff (max (2 * h27.K + 2) (Real.exp 2 + 21))

lemma stationaryCutoff_ge_comparison {R : ℝ → ℝ}
    (h27 : Lemma1027AdjointRComparison R) :
    h27.cutoff ≤ stationaryCutoff h27 :=
  le_max_left _ _

lemma stationaryCutoff_ge_K {R : ℝ → ℝ}
    (h27 : Lemma1027AdjointRComparison R) :
    2 * h27.K + 2 ≤ stationaryCutoff h27 :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma stationaryCutoff_ge_numeric {R : ℝ → ℝ}
    (h27 : Lemma1027AdjointRComparison R) :
    Real.exp 2 + 21 ≤ stationaryCutoff h27 :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The literal (10.46) bridge: stationary equality plus the source's
adjacent-value comparison. -/
lemma equation1046_of_stationary_and_comparison
    {R : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβ : β ≤ 3)
    (h27 : Lemma1027AdjointRComparison R)
    (hs : stationaryCutoff h27 ≤ s)
    (hstat : normalizedMinusBase R xi s = c) :
    1 - h27.K / s ≤ xi s - c - 2 / s := by
  have hsnum := stationaryCutoff_ge_numeric h27 |>.trans hs
  have hs0 : 0 < s := by linarith [Real.exp_pos 2]
  have hdom : β - 1 < s := by
    have hleft : β - 1 ≤ 2 := by linarith
    have hright : 2 < s := by nlinarith [Real.exp_pos 2]
    exact hleft.trans_lt hright
  have hRs : 0 < R s := h.positive s hdom
  have hden : 0 < s * R s := mul_pos hs0 hRs
  have hcmp := h27.comparison s ((stationaryCutoff_ge_comparison h27).trans hs)
  have hratio : 1 - h27.K / s ≤ R (s - 1) / (s * R s) :=
    (le_div_iff₀ hden).2 hcmp
  dsimp [normalizedMinusBase] at hstat
  rw [neg_div] at hstat
  have heq : xi s - c - 2 / s = R (s - 1) / (s * R s) := by
    linarith
  rwa [heq]

lemma stationary_prefactor_ge_half
    {R : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβ : β ≤ 3)
    (h27 : Lemma1027AdjointRComparison R)
    (hs : stationaryCutoff h27 ≤ s)
    (hstat : normalizedMinusBase R xi s = c) :
    (1 / 2 : ℝ) ≤ xi s - c - 2 / s := by
  have hsK := stationaryCutoff_ge_K h27 |>.trans hs
  have hsnum := stationaryCutoff_ge_numeric h27 |>.trans hs
  have hs0 : 0 < s := by linarith [Real.exp_pos 2]
  have hKdiv : h27.K / s ≤ 1 / 2 := by
    apply (div_le_iff₀ hs0).2
    linarith [h27.K_nonneg]
  linarith [equation1046_of_stationary_and_comparison h hβ h27 hs hstat]

lemma exp_parameter_dominates (c : ℝ) (hc : 1152 ≤ c) :
    20 * c + 40 < Real.exp c := by
  have hc0 : 0 < c / 2 := by linarith
  have he := Real.add_one_lt_exp (ne_of_gt hc0)
  have hb0 : 0 < 1 + c / 2 := by linarith
  have hexp0 : 0 < Real.exp (c / 2) := Real.exp_pos _
  calc
    20 * c + 40 < (1 + c / 2) ^ 2 := by nlinarith
    _ < (Real.exp (c / 2)) ^ 2 := by nlinarith
    _ = Real.exp c := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- Uniform form of the strict scalar estimate.  Its cutoff is independent of
`c`; the only source-side premise is (10.46)'s adjacent-value comparison. -/
theorem scalarRatio_lt_one_of_stationary
    {R : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβ : β ≤ 3)
    (h27 : Lemma1027AdjointRComparison R)
    (hc : 1152 ≤ c)
    (hs : stationaryCutoff h27 ≤ s)
    (hstat : normalizedMinusBase R xi s = c) :
    Equation1053EarliestScalarInequality xi c s := by
  have hsnum := stationaryCutoff_ge_numeric h27 |>.trans hs
  have hs4 : 4 ≤ s := by linarith [Real.exp_pos 2]
  have hs3 : 3 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hsexp : Real.exp 2 ≤ s - 1 := by linarith
  have hx2 : 2 ≤ xi (s - 1) := (two_lt_xi hsexp).le
  let A : ℝ := xi s - c - 2 / s
  let m : ℝ := xi (s - 1) - c - kappaOneLogSlope (s - 1)
  have hAhalf : (1 / 2 : ℝ) ≤ A := by
    exact stationary_prefactor_ge_half h hβ h27 hs hstat
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hAhalf
  have hdelta0 := proposition1020_secant_nonneg canonicalXi_proposition1020
    (t := s - 1) (s := s) (by linarith) (by linarith)
  have hdelta := xi_unit_increment_le hs4 hx2
  have hk0 := kappaOneLogSlope_nonneg (u := s - 1) (by linarith)
  have hk := kappaOneLogSlope_le_three_div (u := s - 1) (by linarith)
  have htwo' : 2 / (s - 1) ≤ 4 / s := by
    apply (div_le_div_iff₀ hsm0 hs0).2
    nlinarith
  have hthree : 3 / (s - 1) ≤ 6 / s := by
    apply (div_le_div_iff₀ hsm0 hs0).2
    nlinarith
  have hsmall : 10 / s < 1 / 2 := by
    apply (div_lt_iff₀ hs0).2
    nlinarith [Real.exp_pos 2]
  have hgapUpper : A - m ≤ 10 / s := by
    have hd := hdelta.trans htwo'
    have hkk := hk.trans hthree
    have hsum : (xi s - xi (s - 1)) + kappaOneLogSlope (s - 1) ≤ 10 / s := by
      calc
        _ ≤ 4 / s + 6 / s := add_le_add hd hkk
        _ = 10 / s := by ring
    have htwo0 : 0 ≤ 2 / s := div_nonneg (by norm_num) hs0.le
    have heq : A - m = (xi s - xi (s - 1)) - 2 / s +
        kappaOneLogSlope (s - 1) := by
      dsimp [A, m]
      ring
    rw [heq]
    linarith
  have hmpos : 0 < m := by
    linarith only [hgapUpper, hAhalf, hsmall]
  have hxprev_pos : 0 < xi (s - 1) := by linarith
  have hEqXi := xi_equation (by linarith : 1 < s - 1)
  have hnegxi : Real.exp (-(xi (s - 1))) =
      1 / (1 + (s - 1) * xi (s - 1)) := by
    have he : Real.exp (xi (s - 1)) = 1 + (s - 1) * xi (s - 1) := by
      linarith
    rw [Real.exp_neg, he, one_div]
  have hdenpos : 0 < 1 + (s - 1) * xi (s - 1) := by positivity
  have hdenle : 1 + (s - 1) * xi (s - 1) ≤ s * xi (s - 1) := by
    nlinarith
  have hbase : 1 / (s * xi (s - 1)) ≤ Real.exp (-(xi (s - 1))) := by
    rw [hnegxi]
    exact one_div_le_one_div_of_le hdenpos hdenle
  have htwoS : 2 / s ≤ 1 := by
    apply (div_le_iff₀ hs0).2
    nlinarith
  have hxprev_le : xi (s - 1) ≤ A + c + 1 := by
    dsimp [A]
    linarith
  have hfactor : xi (s - 1) ≤ (2 * c + 4) * A := by
    have hc0 : 0 ≤ c := by linarith
    nlinarith
  have hcp : 0 < 2 * c + 4 := by linarith
  have hexpc : 10 * (2 * c + 4) < Real.exp c := by
    nlinarith [exp_parameter_dominates c hc]
  have hratioConst : 10 / s < A * (Real.exp c * (1 / (s * xi (s - 1)))) := by
    have hdenall : 0 < s * xi (s - 1) := mul_pos hs0 hxprev_pos
    apply (div_lt_iff₀ hs0).2
    have hscaled : (2 * c + 4) * A / xi (s - 1) ≥ 1 := by
      apply (le_div_iff₀ hxprev_pos).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfactor
    have hAc : 10 * (2 * c + 4) * A < Real.exp c * A :=
      mul_lt_mul_of_pos_right hexpc hApos
    have hdiv : 10 < Real.exp c * A / xi (s - 1) := by
      apply (lt_div_iff₀ hxprev_pos).2
      calc
        10 * xi (s - 1) ≤ 10 * ((2 * c + 4) * A) :=
          mul_le_mul_of_nonneg_left hfactor (by norm_num)
        _ < Real.exp c * A := by
          simpa [mul_assoc] using hAc
    field_simp [ne_of_gt hxprev_pos]
    nlinarith
  have heqc : Real.exp (-m) =
      Real.exp c * Real.exp (kappaOneLogSlope (s - 1)) *
        Real.exp (-(xi (s - 1))) := by
    dsimp [m]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexpk : 1 ≤ Real.exp (kappaOneLogSlope (s - 1)) :=
    Real.one_le_exp hk0
  have hExpLower : Real.exp c * (1 / (s * xi (s - 1))) ≤ Real.exp (-m) := by
    rw [heqc]
    have h1 := mul_le_mul_of_nonneg_left hbase (Real.exp_pos c).le
    have h2 := mul_le_mul_of_nonneg_right hexpk
      (Real.exp_pos (-(xi (s - 1)))).le
    simp only [one_mul] at h2
    calc
      Real.exp c * (1 / (s * xi (s - 1))) ≤
          Real.exp c * Real.exp (-(xi (s - 1))) := h1
      _ ≤ Real.exp c * (Real.exp (kappaOneLogSlope (s - 1)) *
            Real.exp (-(xi (s - 1)))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le
      _ = _ := by ring
  have hrhs : 10 / s < A * Real.exp (-m) :=
    hratioConst.trans_le (mul_le_mul_of_nonneg_left hExpLower hApos.le)
  apply scalar_absorption_of_elementary_bounds hs3 (by simpa [m] using hmpos)
    (by simpa [A] using hApos)
  dsimp [A, m] at hgapUpper hrhs ⊢
  exact hgapUpper.trans_lt hrhs

/-- The pairing comparison gives the opposite half of (10.56) at a genuine
first crossing.  This is derived here (rather than imported from the older
assembly) with the shifted adjoint positivity rewritten explicitly. -/
lemma minusFirstCrossing_scalarRatio_ge_one_local
    {R : ℝ → ℝ} {β c s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (w : MinusFirstCrossing R xi c β s₀) :
    1 ≤ equation1056ScalarRatio xi c w.s := by
  have hs2 : 2 ≤ w.s := by linarith [h.beta_ge_one, w.beta_add_one_le_s]
  have hs0 : 0 < w.s := by linarith
  have hRs : 0 < R w.s := h.positive w.s (by linarith [w.beta_lt_s₀, w.s₀_lt_s])
  have hadjs : 0 < explicitKappaOneAdjointPlus w.s :=
    explicitKappaOneAdjointPlus_pos (by linarith)
  have hkernelCont : ContinuousOn
      (fun t => Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))
      (Icc (w.s - 1) w.s) := by
    intro t ht
    have hd := (psiMinus_kappaOne_hasDerivAt_local
      (c := c) (s := t) (by linarith [ht.1])).continuousAt.neg
    exact (Real.continuous_exp.continuousAt.comp hd).continuousWithinAt
  have hkernelInt : IntervalIntegrable
      (fun t => Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))
      volume (w.s - 1) w.s :=
    hkernelCont.intervalIntegrable_of_Icc (by linarith)
  have hprodCont : ContinuousOn
      (fun t => envelopeMinus R xi c t *
        Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))
      (Icc (w.s - 1) w.s) := by
    intro t ht
    have hRc : ContinuousAt R t := h.continuous.continuousAt
      (Ioi_mem_nhds (by linarith [ht.1, w.beta_add_one_le_s]))
    have hphase : ContinuousAt (phiMinus xi c) t :=
      ((xiPhase_hasDerivAt canonicalXi_proposition1020 t).sub
        (by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul c)).continuousAt
    have hkneg := (psiMinus_kappaOne_hasDerivAt_local
      (c := c) (s := t) (by linarith [ht.1])).continuousAt.neg
    exact ((hRc.mul (Real.continuous_exp.continuousAt.comp hphase)).mul
      (Real.continuous_exp.continuousAt.comp hkneg)).continuousWithinAt
  have hprodInt : IntervalIntegrable
      (fun t => envelopeMinus R xi c t *
        Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))
      volume (w.s - 1) w.s :=
    hprodCont.intervalIntegrable_of_Icc (by linarith)
  have hpair := Section10Equation1053MinusFirstCrossing.pairing_le_leftEndpoint_kernel
    h hadj w hs2 hprodInt hkernelInt
  have hstat := w.normalizedMinusBase_eq h canonicalXi_proposition1020
  have hAeq : xi w.s - c - 2 / w.s = R (w.s - 1) / (w.s * R w.s) := by
    dsimp [normalizedMinusBase] at hstat
    have hden : w.s * R w.s ≠ 0 := mul_ne_zero (ne_of_gt hs0) (ne_of_gt hRs)
    rw [neg_div] at hstat
    linarith
  have hleftPos : 0 < w.s * explicitKappaOneAdjointPlus w.s * R w.s :=
    mul_pos (mul_pos hs0 hadjs) hRs
  have hratio : equation1056ScalarRatio xi c w.s =
      (envelopeMinus R xi c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))) /
        (w.s * explicitKappaOneAdjointPlus w.s * R w.s) := by
    unfold equation1056ScalarRatio
    rw [hAeq]
    have hadjshift : 0 < explicitKappaOneAdjointPlus (w.s - 1 + 1) := by
      convert hadjs using 1 <;> ring
    rw [exp_neg_psiMinus hadjshift]
    dsimp [envelopeMinus]
    field_simp [ne_of_gt hs0, ne_of_gt hRs, ne_of_gt hadjs, Real.exp_ne_zero]
    rw [show w.s - 1 + 1 = w.s by ring]
    have hcancel : Real.exp (-phiMinus xi c (w.s - 1)) *
        Real.exp (phiMinus xi c (w.s - 1)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (R (w.s - 1) * (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))) *
          explicitKappaOneAdjointPlus w.s =
        (R (w.s - 1) * (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))) *
          explicitKappaOneAdjointPlus w.s * 1 := by ring
      _ = (R (w.s - 1) * (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))) *
          explicitKappaOneAdjointPlus w.s *
          (Real.exp (-phiMinus xi c (w.s - 1)) *
            Real.exp (phiMinus xi c (w.s - 1))) := by rw [hcancel]
      _ = _ := by ring
  rw [hratio]
  exact (le_div_iff₀ hleftPos).2 (by simpa only [one_mul] using hpair)

/-- No genuine stationary first-crossing candidate survives past the fixed
`R`-dependent cutoff, simultaneously for every `c ≥ 1152`. -/
theorem no_uniform_minusFirstCrossing
    {R : ℝ → ℝ} {β c s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (h27 : Lemma1027AdjointRComparison R)
    (hβ : β ≤ 3)
    (hc : 1152 ≤ c)
    (w : MinusFirstCrossing R xi c β s₀)
    (hs : stationaryCutoff h27 ≤ w.s) : False := by
  have hstat := w.normalizedMinusBase_eq h canonicalXi_proposition1020
  have hupper := scalarRatio_lt_one_of_stationary h hβ h27 hc hs hstat
  have hlower := minusFirstCrossing_scalarRatio_ge_one_local h hadj w
  exact (not_lt_of_ge hlower) hupper

lemma canonical_eventual_log_lower_local (c : ℝ) :
    ∃ T : ℝ, ∀ s, T ≤ s →
      (1 / 2 : ℝ) * Real.log (Real.exp 1 * s) ≤ xi s - c - 2 / s := by
  let L : ℝ := max 2 (2 * c + 5)
  let T : ℝ := Real.exp L
  refine ⟨T, ?_⟩
  intro s hs
  have hL2 : 2 ≤ L := le_max_left _ _
  have hLc : 2 * c + 5 ≤ L := le_max_right _ _
  have hTpos : 0 < T := Real.exp_pos L
  have hspos : 0 < s := hTpos.trans_le hs
  have hlog : L ≤ Real.log s := by
    rw [← Real.log_exp L]
    exact Real.strictMonoOn_log.monotoneOn hTpos hspos hs
  have hexp1s : Real.exp 1 ≤ s :=
    (Real.exp_le_exp.mpr (by linarith)).trans hs
  have hxi : Real.log s < xi s := log_lt_xi hexp1s
  have hsone : 1 ≤ s := by
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hexp1s
  have htwo : 2 / s ≤ 2 := (div_le_iff₀ hspos).2 (by nlinarith)
  rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hspos), Real.log_exp]
  norm_num
  nlinarith

/-- One compact choice of `c` after the uniform cutoff has been frozen.  The
compact premise is initial data only; it contains neither a scalar-ratio bound
nor a majorant. -/
noncomputable def qhatMinusMajorant_of_uniform_stationary
    {R : ℝ → ℝ} {β : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (h27 : Lemma1027AdjointRComparison R)
    (hβ : β ≤ 3)
    (hcompact : ContinuousOn (normalizedMinusBase R xi)
      (Icc β (stationaryCutoff h27))) :
    QhatMinusMajorant R := by
  let S := stationaryCutoff h27
  have hSnum : Real.exp 2 + 21 ≤ S := stationaryCutoff_ge_numeric h27
  have hβS : β < S := by linarith [Real.exp_pos 2]
  have hβoneS : β + 1 ≤ S := by linarith [Real.exp_pos 2]
  have hb := isCompact_Icc.bddAbove_image hcompact
  have hbex : ∃ B : ℝ, ∀ z ∈ normalizedMinusBase R xi '' Icc β S, z ≤ B := by
    rw [bddAbove_def] at hb
    simpa [S] using hb
  let B : ℝ := Classical.choose hbex
  have hB : ∀ z ∈ normalizedMinusBase R xi '' Icc β S, z ≤ B :=
    Classical.choose_spec hbex
  let c : ℝ := max 1152 (B + 1)
  have hc : 1152 ≤ c := le_max_left _ _
  have hinitial : ∀ u ∈ Icc β S, normalizedMinusBase R xi u < c := by
    intro u hu
    have huB : normalizedMinusBase R xi u ≤ B := hB _ ⟨u, hu, rfl⟩
    have hBc : B + 1 ≤ c := le_max_right _ _
    linarith
  have hglobal : ∀ s, 4 ≤ s → normalizedMinusBase R xi s - c ≤ 0 := by
    intro v hv4
    by_cases hvS : v ≤ S
    · have hβv : β ≤ v := hβ.trans (by linarith)
      linarith [hinitial v ⟨hβv, hvS⟩]
    · have hSv : S ≤ v := (lt_of_not_ge hvS).le
      by_contra hn
      have hvreach : c ≤ normalizedMinusBase R xi v := by linarith
      obtain ⟨w, hSw⟩ := minusFirstCrossing_of_reaches h hβS hβoneS
        hinitial hSv hvreach
      exact no_uniform_minusFirstCrossing h hadj h27 hβ hc w hSw
  let hw := canonical_eventual_log_lower_local c
  let T : ℝ := Classical.choose hw
  have hlog := Classical.choose_spec hw
  let U : ℝ := max 4 T
  refine ⟨c, U, 2, le_max_left _ _, by norm_num, ?_, ?_⟩
  · intro s hs
    exact hlog s ((le_max_right 4 T).trans hs)
  · intro s hs
    have hs4 : 4 ≤ s := (le_max_left 4 T).trans hs
    have hs0 : 0 < s := by linarith
    have hRs : 0 < R s := h.positive s (by linarith [hβ])
    have hn := hglobal s hs4
    have hscale : 0 < s * R s := mul_pos hs0 hRs
    have heq :
        -(R (s - 1)) + s * (xi s - c - 2 / s) * R s =
          (s * R s) * (normalizedMinusBase R xi s - c) := by
      dsimp [normalizedMinusBase]
      field_simp [ne_of_gt hs0, ne_of_gt hRs]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hscale.le hn


end Section10Equation1056UniformStationary
