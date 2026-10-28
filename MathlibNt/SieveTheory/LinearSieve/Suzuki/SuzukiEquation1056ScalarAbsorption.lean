import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053KernelExpansion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Equation (10.56): eventual strict scalar absorption
-/

namespace Section10Equation1056ScalarAbsorption

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Section10Lemma1028
open Section10Equation1053
open Section10Equation1053NonCircular
open Section10Equation1053KernelExpansion
open Section10CanonicalXi

lemma kappaOneLogSlope_antitoneOn :
    AntitoneOn kappaOneLogSlope (Ici 2) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    (fun x hx => (kappaOneLogSlope_hasDerivAt (by change 2 ≤ x at hx; linarith)).continuousAt.continuousWithinAt)
  · intro x hx
    rw [interior_Ici] at hx
    change 2 < x at hx
    exact (kappaOneLogSlope_hasDerivAt (by linarith [hx])).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    change 2 < x at hx
    have hnum : 0 ≤ 2 * x ^ 2 + 1 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hnum) (sq_nonneg _)

lemma psiMinus_kappaOne_hasDerivAt_local
    {c s : ℝ} (hs : 1 ≤ s) :
    HasDerivAt (psiMinus explicitKappaOneAdjointPlus xi c)
      (xi s - c - kappaOneLogSlope s) s := by
  have hpos : 0 < explicitKappaOneAdjointPlus (s + 1) :=
    explicitKappaOneAdjointPlus_pos (by linarith)
  have hadj0 : HasDerivAt explicitKappaOneAdjointPlus (2 * (s + 1) - 2) (s + 1) := by
    have hp :=
      ((hasDerivAt_pow 2 (s + 1)).sub
        ((hasDerivAt_id (s + 1)).const_mul 2) |>.add_const (1 / 2))
    exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl)) |>.congr_deriv (by norm_num)
  have hadj := hadj0.comp s ((hasDerivAt_id s).add_const 1)
  have hlog := hadj.log (ne_of_gt hpos)
  have hphase := (xiPhase_hasDerivAt canonicalXi_proposition1020 s).sub
    (by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul c)
  have hout := hphase.sub hlog
  have hden : 2 * s ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg s]
  have hadjNe : explicitKappaOneAdjointPlus (s + 1) ≠ 0 := ne_of_gt hpos
  have hslope : (2 * (s + 1) - 2) * 1 /
      (explicitKappaOneAdjointPlus ∘ fun x => id x + 1) s = kappaOneLogSlope s := by
    simp only [Function.comp_apply, id_eq]
    dsimp [explicitKappaOneAdjointPlus, kappaOneLogSlope]
    apply (div_eq_div_iff hadjNe hden).2
    dsimp [explicitKappaOneAdjointPlus]
    ring
  apply (hout.congr_deriv (by rw [hslope])).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

lemma psiMinus_secant_lower
    {c s t : ℝ} (hs : 3 ≤ s) (ht : t ∈ Icc (s - 1) s) :
    (xi (s - 1) - c - kappaOneLogSlope (s - 1)) * (t - (s - 1)) ≤
      psiMinus explicitKappaOneAdjointPlus xi c t -
        psiMinus explicitKappaOneAdjointPlus xi c (s - 1) := by
  let m := xi (s - 1) - c - kappaOneLogSlope (s - 1)
  let g : ℝ → ℝ := fun u => psiMinus explicitKappaOneAdjointPlus xi c u - m * u
  have hgcont : ContinuousOn g (Icc (s - 1) s) := by
    intro u hu
    have hd := psiMinus_kappaOne_hasDerivAt_local
      (c := c) (s := u) (by linarith [hu.1])
    exact (hd.sub ((hasDerivAt_id u).const_mul m)).continuousAt.continuousWithinAt
  have hgmono : MonotoneOn g (Icc (s - 1) s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (s - 1) s) hgcont
    · intro u hu
      have huI : u ∈ Icc (s - 1) s := by
        rw [interior_Icc] at hu
        exact ⟨hu.1.le, hu.2.le⟩
      exact (psiMinus_kappaOne_hasDerivAt_local
        (c := c) (s := u) (by linarith [huI.1])).sub
          ((hasDerivAt_id u).const_mul m) |>.hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hxi : xi (s - 1) ≤ xi u := by
        have hsec := proposition1020_secant_nonneg canonicalXi_proposition1020
          (t := s - 1) (s := u) (by linarith) hu.1.le
        linarith
      have hk : kappaOneLogSlope u ≤ kappaOneLogSlope (s - 1) :=
        kappaOneLogSlope_antitoneOn (by change 2 ≤ s - 1; linarith)
          (by change 2 ≤ u; linarith [hu.1])
          hu.1.le
      dsimp [m]
      linarith
  have hmono := hgmono (by exact ⟨le_rfl, by linarith⟩) ht ht.1
  dsimp [g, m] at hmono ⊢
  linarith

lemma normalized_kernel_le
    {c s : ℝ} (hs : 3 ≤ s)
    (hm : 0 < xi (s - 1) - c - kappaOneLogSlope (s - 1)) :
    (∫ t in s - 1..s,
      Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t)) /
        Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c (s - 1)) ≤
      (1 - Real.exp (-(xi (s - 1) - c - kappaOneLogSlope (s - 1)))) /
        (xi (s - 1) - c - kappaOneLogSlope (s - 1)) := by
  let m := xi (s - 1) - c - kappaOneLogSlope (s - 1)
  let q := psiMinus explicitKappaOneAdjointPlus xi c (s - 1)
  have hm' : 0 < m := hm
  have hcontL : ContinuousOn
      (fun t => Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t))
      (Icc (s - 1) s) := by
    intro t ht
    exact (Real.continuous_exp.continuousAt.comp_of_eq
      (psiMinus_kappaOne_hasDerivAt_local
        (c := c) (s := t) (by linarith [ht.1])).continuousAt.neg rfl).continuousWithinAt
  have hcontR : ContinuousOn
      (fun t => Real.exp (-q) * Real.exp (-m * (t - (s - 1))))
      (Icc (s - 1) s) := by fun_prop
  have hint :
      (∫ t in s - 1..s,
        Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t)) ≤
      ∫ t in s - 1..s,
        Real.exp (-q) * Real.exp (-m * (t - (s - 1))) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hcontL.intervalIntegrable_of_Icc (by linarith)
    · exact hcontR.intervalIntegrable_of_Icc (by linarith)
    · intro t ht
      have hsec := psiMinus_secant_lower (c := c) hs ht
      dsimp [m, q]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
  have hcalc :
      (∫ t in s - 1..s,
        Real.exp (-q) * Real.exp (-m * (t - (s - 1)))) =
      Real.exp (-q) * ((1 - Real.exp (-m)) / m) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hderiv : ∀ t ∈ uIcc (s - 1) s,
        HasDerivAt (fun u : ℝ => Real.exp (-m * (u - (s - 1))) / (-m))
          (Real.exp (-m * (t - (s - 1)))) t := by
      intro t _
      have h := (((hasDerivAt_id t).sub_const (s - 1)).const_mul (-m)).exp
      have hh := h.div_const (-m)
      have hc : (Real.exp (-m * (t - (s - 1))) * (-m * 1)) / (-m) =
          Real.exp (-m * (t - (s - 1))) := by
        rw [mul_one, mul_div_cancel_right₀ _ (neg_ne_zero.mpr (ne_of_gt hm'))]
      simpa only [id_eq] using hh.congr_deriv hc
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
    rw [show s - (s - 1) = 1 by ring]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    have hm0 : m ≠ 0 := ne_of_gt hm'
    field_simp [hm0]
    ring
  rw [hcalc] at hint
  have hqpos : 0 < Real.exp (-q) := Real.exp_pos _
  have hdiv :
      (∫ t in s - 1..s, Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t)) /
          Real.exp (-q) ≤ (1 - Real.exp (-m)) / m := by
    apply (div_le_iff₀ hqpos).2
    calc
      (∫ t in s - 1..s, Real.exp (-psiMinus explicitKappaOneAdjointPlus xi c t)) ≤
          Real.exp (-q) * ((1 - Real.exp (-m)) / m) := hint
      _ = ((1 - Real.exp (-m)) / m) * Real.exp (-q) := mul_comm _ _
  simpa [q, m] using hdiv

lemma scalar_absorption_of_elementary_bounds
    {c s : ℝ} (hs : 3 ≤ s)
    (hm : 0 < xi (s - 1) - c - kappaOneLogSlope (s - 1))
    (hA : 0 < xi s - c - 2 / s)
    (hgap :
      (xi s - c - 2 / s) -
          (xi (s - 1) - c - kappaOneLogSlope (s - 1)) <
        (xi s - c - 2 / s) *
          Real.exp (-(xi (s - 1) - c - kappaOneLogSlope (s - 1)))) :
    Equation1053EarliestScalarInequality xi c s := by
  let A := xi s - c - 2 / s
  let m := xi (s - 1) - c - kappaOneLogSlope (s - 1)
  have hm' : 0 < m := hm
  have hK := normalized_kernel_le (c := c) hs hm
  have hfactor : A * ((1 - Real.exp (-m)) / m) < 1 := by
    have hh : A * (1 - Real.exp (-m)) / m < 1 := by
      apply (div_lt_iff₀ hm').2
      dsimp [A, m] at hgap ⊢
      nlinarith
    convert hh using 1; ring
  unfold Equation1053EarliestScalarInequality equation1056ScalarRatio
  have hmul := mul_le_mul_of_nonneg_left hK hA.le
  apply lt_of_le_of_lt _ hfactor
  dsimp [A, m] at hmul ⊢
  convert hmul using 1; ring


lemma xi_unit_increment_le
    {s : ℝ} (hs : 4 ≤ s) (hx : 2 ≤ xi (s - 1)) :
    xi s - xi (s - 1) ≤ 2 / (s - 1) := by
  have hlt : s - 1 < s := by linarith
  obtain ⟨u, hu, hdu⟩ := exists_hasDerivAt_eq_slope
    xi (deriv xi) hlt xi_continuous.continuousOn
    (fun v hv => (xi_differentiableAt (by linarith [hv.1, hs])).hasDerivAt)
  have hmono : xi (s - 1) ≤ xi u := by
    have hsec := proposition1020_secant_nonneg canonicalXi_proposition1020
      (t := s - 1) (s := u) (by linarith) hu.1.le
    linarith
  have hxu : 2 ≤ xi u := hx.trans hmono
  have hu0 : 0 < u := by linarith [hu.1, hs]
  have hden : u / 2 ≤ u - (u - 1) / xi u := by
    have hxupos : 0 < xi u := by linarith
    have hq : (u - 1) / xi u ≤ u / 2 := by
      apply (div_le_iff₀ hxupos).2
      nlinarith
    linarith
  have hdenpos : 0 < u - (u - 1) / xi u := by linarith
  have hdle : deriv xi u ≤ 2 / u := by
    rw [(canonicalXi_proposition1020.hasDerivAt (by linarith [hu.1, hs])).deriv]
    apply (div_le_div_iff₀ hdenpos hu0).2
    nlinarith
  have hfrac : 2 / u ≤ 2 / (s - 1) := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (sub_pos.mpr (lt_of_lt_of_le (by norm_num) hs)) hu.1.le
  rw [hdu] at hdle
  have hslope := hdle.trans hfrac
  have hpos : 0 < s - (s - 1) := by linarith
  have hout := (div_le_iff₀ hpos).1 hslope
  have hone : s - (s - 1) = 1 := by ring
  rw [hone, mul_one] at hout
  exact hout

lemma kappaOneLogSlope_nonneg {u : ℝ} (hu : 2 ≤ u) :
    0 ≤ kappaOneLogSlope u := by
  have hden : 0 < 2 * u ^ 2 - 1 := by nlinarith [sq_nonneg u]
  exact div_nonneg (by positivity) hden.le

lemma kappaOneLogSlope_le_three_div {u : ℝ} (hu : 2 ≤ u) :
    kappaOneLogSlope u ≤ 3 / u := by
  have hu0 : 0 < u := by linarith
  have hden : 0 < 2 * u ^ 2 - 1 := by nlinarith [sq_nonneg u]
  dsimp [kappaOneLogSlope]
  apply (div_le_div_iff₀ hden hu0).2
  nlinarith [sq_nonneg (u - 2)]


end Section10Equation1056ScalarAbsorption
