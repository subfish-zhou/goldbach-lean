import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1055UniformStationary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1056ScalarAbsorption

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Internal source expansion for the plus case of (10.55)

The scalar expansion and its error absorption are proved here from the canonical
inverse `ξ`, the explicit rational adjoint, and stationarity.  The direct
majorant constructor at the end has no expansion, remainder, or final-strict
premise.
-/

namespace Section10Equation1055SourceExpansion

set_option autoImplicit false
set_option maxHeartbeats 2400000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053NonCircular
open Section10Equation1053KernelExpansion
open Section10CanonicalXi
open Section10Lemma1028PlusAssembly
open Section10Equation1055UniformStationary
open Section10Equation1056ScalarAbsorption

/-- Exact derivative of the plus kernel phase for the explicit adjoint. -/
lemma psiPlus_kappaOne_hasDerivAt
    {c s : ℝ} (hs : 1 ≤ s) :
    HasDerivAt (psiPlus explicitKappaOneAdjointPlus xi c)
      (xi s + c - kappaOneLogSlope s) s := by
  have hpos : 0 < explicitKappaOneAdjointPlus (s + 1) :=
    explicitKappaOneAdjointPlus_pos (by linarith)
  have hadj0 : HasDerivAt explicitKappaOneAdjointPlus
      (2 * (s + 1) - 2) (s + 1) := by
    have hp := ((hasDerivAt_pow 2 (s + 1)).sub
      ((hasDerivAt_id (s + 1)).const_mul 2) |>.add_const (1 / 2))
    exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
      |>.congr_deriv (by norm_num)
  have hadj := hadj0.comp s ((hasDerivAt_id s).add_const 1)
  have hlog := hadj.log (ne_of_gt hpos)
  have hphase := (xiPhase_hasDerivAt canonicalXi_proposition1020 s).add
    (by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul c)
  have hout := hphase.sub hlog
  have hden : 2 * s ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg s]
  have hadjNe : explicitKappaOneAdjointPlus (s + 1) ≠ 0 := ne_of_gt hpos
  have hslope : (2 * (s + 1) - 2) * 1 /
      (explicitKappaOneAdjointPlus ∘ fun x => id x + 1) s =
        kappaOneLogSlope s := by
    simp only [Function.comp_apply, id_eq]
    dsimp [explicitKappaOneAdjointPlus, kappaOneLogSlope]
    apply (div_eq_div_iff hadjNe hden).2
    dsimp [explicitKappaOneAdjointPlus]
    ring
  apply (hout.congr_deriv (by rw [hslope])).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The canonical derivative is at least the reciprocal derivative suggested by
`ξ(s) ~ log s` (the error has an exact positive rational formula). -/
lemma one_div_le_xi_deriv {u : ℝ} (hu : 1 < u) :
    1 / u ≤ deriv xi u := by
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < xi u := xi_pos hu
  have hB : 0 < u * (xi u - 1) + 1 := by
    have hD := xiSlope_pos hu
    rw [xiSlope_eq hu] at hD
    rcases div_pos_iff.mp hD with h | h
    · exact h.1
    · exfalso
      linarith [h.2, hx0]
  have hden : 0 < u * (u * (xi u - 1) + 1) := mul_pos hu0 hB
  have herr : 0 ≤ (u - 1) / (u * (u * (xi u - 1) + 1)) :=
    div_nonneg (by linarith) hden.le
  have heq := xi_deriv_sub_reciprocal_eq hu
  linarith

/-- Linear one-window lower increment for canonical `ξ`. -/
lemma xi_window_linear_lower {s t : ℝ}
    (hs : Real.exp 2 + 1 ≤ s) (ht : t ∈ Icc (s - 1) s) :
    xi t ≤ xi s - (s - t) / s := by
  let g : ℝ → ℝ := fun u => xi u - u / s
  have hs0 : 0 < s := by linarith [Real.exp_pos 2]
  have hexpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hcont : ContinuousOn g (Icc (s - 1) s) :=
    (xi_continuous.sub (continuous_id.div_const s)).continuousOn
  have hmono : MonotoneOn g (Icc (s - 1) s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (s - 1) s) hcont
    · intro u hu
      rw [interior_Icc] at hu
      have huExp : Real.exp 2 ≤ u := by linarith [hu.1]
      have hu1 : 1 < u := by linarith
      exact ((xi_hasDerivAt hu1).sub
        ((hasDerivAt_id u).div_const s)).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu1 : 1 < u := by linarith [hu.1]
      have hu0 : 0 < u := by linarith
      have hus : u ≤ s := hu.2.le
      have hrecip : 1 / s ≤ 1 / u := by
        exact one_div_le_one_div_of_le hu0 hus
      have hdx : 1 / u ≤ deriv xi u := one_div_le_xi_deriv hu1
      rw [← xi_deriv hu1]
      exact sub_nonneg.mpr (hrecip.trans hdx)
  have hm := hmono ht (by exact ⟨by linarith, le_rfl⟩) ht.2
  dsimp [g] at hm ⊢
  field_simp [ne_of_gt hs0] at hm ⊢
  linarith

/-- Explicit rational adjoint inequality needed in the plus expansion. -/
lemma two_div_lt_kappaOneLogSlope {s : ℝ} (hs : 1 ≤ s) :
    2 / s < kappaOneLogSlope s := by
  have hs0 : 0 < s := by linarith
  have hden : 0 < 2 * s ^ 2 - 1 := by nlinarith [sq_nonneg s]
  dsimp [kappaOneLogSlope]
  apply (div_lt_div_iff₀ hs0 hden).2
  nlinarith

/-- Quadratic one-window upper expansion of the plus phase. -/
lemma psiPlus_secant_upper
    {c s t : ℝ} (hs : Real.exp 2 + 1 ≤ s)
    (ht : t ∈ Icc (s - 1) s) :
    psiPlus explicitKappaOneAdjointPlus xi c t -
        psiPlus explicitKappaOneAdjointPlus xi c (s - 1) ≤
      (xi s + c - 2 / s) * (t - (s - 1)) -
        ((t - (s - 1)) - (t - (s - 1)) ^ 2 / 2) / s := by
  let A : ℝ := xi s + c - 2 / s
  let model : ℝ → ℝ := fun u =>
    A * (u - (s - 1)) -
      ((u - (s - 1)) - (u - (s - 1)) ^ 2 / 2) / s
  let g : ℝ → ℝ := fun u => model u -
    (psiPlus explicitKappaOneAdjointPlus xi c u -
      psiPlus explicitKappaOneAdjointPlus xi c (s - 1))
  have hs0 : 0 < s := by linarith [Real.exp_pos 2]
  have hexpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hexpTwo : 2 < Real.exp 2 := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)]
  have hcont : ContinuousOn g (Icc (s - 1) s) := by
    intro u hu
    have hp := (psiPlus_kappaOne_hasDerivAt
      (c := c) (s := u) (by linarith [hu.1])).continuousAt
    exact (by fun_prop : ContinuousAt model u) |>.sub
      (hp.sub continuousAt_const) |>.continuousWithinAt
  have hmono : MonotoneOn g (Icc (s - 1) s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (s - 1) s) hcont
    · intro u hu
      rw [interior_Icc] at hu
      have huI : u ∈ Icc (s - 1) s := ⟨hu.1.le, hu.2.le⟩
      have hu1 : 1 ≤ u := by linarith [hu.1]
      have hmodel : HasDerivAt model
          (A - (1 - (u - (s - 1))) / s) u := by
        dsimp [model]
        have hd := (((hasDerivAt_id u).sub_const (s - 1)).const_mul A).sub
          ((((hasDerivAt_id u).sub_const (s - 1)).sub
            (((((hasDerivAt_id u).sub_const (s - 1)).pow 2).div_const 2))).div_const s)
        apply hd.congr_deriv
        simp only [id_eq]
        field_simp [ne_of_gt hs0]
        ring
      exact (hmodel.sub ((psiPlus_kappaOne_hasDerivAt
        (c := c) (s := u) hu1).sub_const _)).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have huI : u ∈ Icc (s - 1) s := ⟨hu.1.le, hu.2.le⟩
      have hu1 : 1 ≤ u := by linarith [hu.1]
      have hxi := xi_window_linear_lower hs huI
      have hk := two_div_lt_kappaOneLogSlope hu1
      have hder := (psiPlus_kappaOne_hasDerivAt (c := c) (s := u) hu1).deriv
      change 0 ≤ (A - (1 - (u - (s - 1))) / s) -
        (xi u + c - kappaOneLogSlope u)
      dsimp [A]
      have htwo : 2 / s ≤ kappaOneLogSlope u := by
        have hks : kappaOneLogSlope s ≤ kappaOneLogSlope u :=
          kappaOneLogSlope_antitoneOn
            (show u ∈ Ici 2 by change 2 ≤ u; linarith [hu.1])
            (show s ∈ Ici 2 by change 2 ≤ s; linarith) hu.2.le
        exact (two_div_lt_kappaOneLogSlope (by linarith)).le.trans hks
      have hid : 1 - (u - (s - 1)) = s - u := by ring
      rw [hid]
      linarith
  have hout := hmono (by exact ⟨le_rfl, by linarith⟩) ht ht.1
  dsimp [g, model, A] at hout ⊢
  norm_num at hout
  linarith

/-- Closed form for the elementary first-order expansion integral. -/
lemma plus_expansion_integral
    {A s : ℝ} (hA : A ≠ 0) (hs : s ≠ 0) :
    (∫ t in s - 1..s,
      Real.exp (-A * (t - (s - 1))) *
        (1 + (t - (s - 1)) / (2 * s))) =
      (1 - Real.exp (-A)) / A +
        (1 - (A + 1) * Real.exp (-A)) / (2 * s * A ^ 2) := by
  let F : ℝ → ℝ := fun t =>
    -Real.exp (-A * (t - (s - 1))) / A -
      Real.exp (-A * (t - (s - 1))) *
        (A * (t - (s - 1)) + 1) / (2 * s * A ^ 2)
  have hder : ∀ t ∈ uIcc (s - 1) s,
      HasDerivAt F
        (Real.exp (-A * (t - (s - 1))) *
          (1 + (t - (s - 1)) / (2 * s))) t := by
    intro t _
    dsimp [F]
    have he := (((hasDerivAt_id t).sub_const (s - 1)).const_mul (-A)).exp
    have hd := (he.neg.div_const A).sub
      ((he.mul (((hasDerivAt_id t).sub_const (s - 1)).const_mul A |>.add_const 1)).div_const
        (2 * s * A ^ 2))
    apply hd.congr_deriv
    simp only [id_eq]
    field_simp [hA, hs]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder]
  · dsimp [F]
    rw [show s - (s - 1) = 1 by ring]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    field_simp [hA, hs]
    ring
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).mul
        (continuous_const.add
          ((continuous_id.sub continuous_const).div_const (2 * s)))).intervalIntegrable _ _

/-- Internalized plus (10.55): the positive first-order correction absorbs the
exponential tail uniformly for every `c ≥ 64` beyond one fixed cutoff. -/
theorem equation1055_internal_strict
    {c s : ℝ} (hc : 64 ≤ c) (hs : Real.exp 2 + 1 ≤ s) :
    1 < plusPairingScalarRatio xi c s := by
  let A : ℝ := xi s + c - 2 / s
  have hs0 : 0 < s := by linarith [Real.exp_pos 2]
  have hexpOne : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hs1 : 1 < s := by linarith
  have hx2 : 2 < xi s := two_lt_xi (by linarith)
  have htwo : 2 / s ≤ 1 := (div_le_iff₀ hs0).2 (by linarith)
  have htwo0 : 0 ≤ 2 / s := div_nonneg (by norm_num) hs0.le
  have hA64 : 64 ≤ A := by dsimp [A]; linarith
  have hA : 0 < A := by linarith
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hphaseInt : IntervalIntegrable
      (fun t => Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
      volume (s - 1) s := by
    have hcont : ContinuousOn
        (fun t => Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
        (Icc (s - 1) s) := by
      intro t ht
      exact (Real.continuous_exp.continuousAt.comp
        (psiPlus_kappaOne_hasDerivAt (c := c) (s := t)
          (by linarith [ht.1])).continuousAt.neg).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by linarith)
  have hnorm :
      (∫ t in s - 1..s,
        Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t)) /
          Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c (s - 1)) =
      ∫ t in s - 1..s,
        Real.exp (-(psiPlus explicitKappaOneAdjointPlus xi c t -
          psiPlus explicitKappaOneAdjointPlus xi c (s - 1))) := by
    rw [div_eq_iff (Real.exp_ne_zero _)]
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring
  have hpoint : ∀ t ∈ Icc (s - 1) s,
      Real.exp (-A * (t - (s - 1))) *
          (1 + (t - (s - 1)) / (2 * s)) ≤
        Real.exp (-(psiPlus explicitKappaOneAdjointPlus xi c t -
          psiPlus explicitKappaOneAdjointPlus xi c (s - 1))) := by
    intro t ht
    let u := t - (s - 1)
    have hu0 : 0 ≤ u := by dsimp [u]; linarith [ht.1]
    have hu1 : u ≤ 1 := by dsimp [u]; linarith [ht.2]
    have hquad : u / 2 ≤ u - u ^ 2 / 2 := by nlinarith
    have hcorr0 : 0 ≤ (u - u ^ 2 / 2) / s :=
      div_nonneg ((div_nonneg hu0 (by norm_num)).trans hquad) hs0.le
    have hsec := psiPlus_secant_upper (c := c) hs ht
    have hexpsec :
        Real.exp (-A * u + (u - u ^ 2 / 2) / s) ≤
          Real.exp (-(psiPlus explicitKappaOneAdjointPlus xi c t -
            psiPlus explicitKappaOneAdjointPlus xi c (s - 1))) := by
      apply Real.exp_le_exp.mpr
      dsimp [A, u] at hsec ⊢
      linarith
    have hexpcorr : 1 + u / (2 * s) ≤
        Real.exp ((u - u ^ 2 / 2) / s) := by
      have hlin := Real.add_one_le_exp ((u - u ^ 2 / 2) / s)
      have : u / (2 * s) ≤ (u - u ^ 2 / 2) / s := by
        rw [show u / (2 * s) = (u / 2) / s by ring]
        apply (div_le_div_iff_of_pos_right hs0).2
        exact hquad
      linarith
    calc
      Real.exp (-A * u) * (1 + u / (2 * s)) ≤
          Real.exp (-A * u) * Real.exp ((u - u ^ 2 / 2) / s) :=
        mul_le_mul_of_nonneg_left hexpcorr (Real.exp_pos _).le
      _ = Real.exp (-A * u + (u - u ^ 2 / 2) / s) := by rw [← Real.exp_add]
      _ ≤ _ := hexpsec
  have hleftInt : IntervalIntegrable
      (fun t => Real.exp (-A * (t - (s - 1))) *
        (1 + (t - (s - 1)) / (2 * s))) volume (s - 1) s :=
    ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).mul
        (continuous_const.add
          ((continuous_id.sub continuous_const).div_const (2 * s)))).intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (fun t => Real.exp (-(psiPlus explicitKappaOneAdjointPlus xi c t -
        psiPlus explicitKappaOneAdjointPlus xi c (s - 1)))) volume (s - 1) s := by
    convert hphaseInt.const_mul
      (Real.exp (psiPlus explicitKappaOneAdjointPlus xi c (s - 1))) using 1
    ext t
    rw [← Real.exp_add]
    ring_nf
  have hint := intervalIntegral.integral_mono_on (by linarith)
    hleftInt hrightInt hpoint
  rw [plus_expansion_integral hA0 (ne_of_gt hs0)] at hint
  have hexpc : 4 * c < Real.exp (c - 1) := by
    have hz : 0 < (c - 1) / 2 := by linarith
    have he := Real.add_one_lt_exp (ne_of_gt hz)
    have hpoly : 4 * c < (1 + (c - 1) / 2) ^ 2 := by nlinarith
    calc
      4 * c < (1 + (c - 1) / 2) ^ 2 := hpoly
      _ < (Real.exp ((c - 1) / 2)) ^ 2 := by nlinarith [Real.exp_pos ((c - 1) / 2)]
      _ = Real.exp (c - 1) := by rw [pow_two, ← Real.exp_add]; congr 1 <;> ring
  have hAupper : A ≤ c * xi s := by
    dsimp [A]
    have hsum : xi s + c ≤ c * xi s := by nlinarith
    linarith
  have hExpA : 2 * s * A + A + 1 < Real.exp A := by
    have hAs : A + 1 ≤ s * A := by nlinarith [hA64]
    have hlhs : 2 * s * A + A + 1 ≤ 3 * s * A := by linarith
    have hmid : 3 * s * A ≤ 3 * s * (c * xi s) :=
      mul_le_mul_of_nonneg_left hAupper (by positivity)
    have heqxi : Real.exp (xi s) = 1 + s * xi s := by
      linarith [xi_equation hs1]
    have hminus : -1 < -2 / s := by
      have : 2 / s < 1 := by
        apply (div_lt_iff₀ hs0).2
        linarith
      rw [show -2 / s = -(2 / s) by ring]
      exact neg_lt_neg this
    have hexpLower : Real.exp (c - 1) * Real.exp (xi s) < Real.exp A := by
      rw [← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      have hminus' : -1 < -(2 / s) := by
        calc
          -1 < -2 / s := hminus
          _ = -(2 / s) := by ring
      dsimp [A]
      linarith
    calc
      2 * s * A + A + 1 ≤ 3 * s * A := hlhs
      _ ≤ 3 * s * (c * xi s) := hmid
      _ < 4 * c * (1 + s * xi s) := by
        have hc0 : 0 < c := by linarith
        have hx0 : 0 < xi s := by linarith
        nlinarith
      _ < Real.exp (c - 1) * Real.exp (xi s) := by
        rw [heqxi]
        exact mul_lt_mul_of_pos_right hexpc (by positivity)
      _ < Real.exp A := hexpLower
  have htail :
      Real.exp (-A) <
        (1 - (A + 1) * Real.exp (-A)) / (2 * s * A) := by
    have hden : 0 < 2 * s * A := by positivity
    apply (lt_div_iff₀ hden).2
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    nlinarith
  unfold plusPairingScalarRatio
  change 1 < A * (∫ t in s - 1..s,
    Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t)) /
      Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c (s - 1))
  rw [div_eq_mul_inv]
  rw [show A * (∫ t in s - 1..s,
      Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t)) *
      (Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c (s - 1)))⁻¹ =
    A * ((∫ t in s - 1..s,
      Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t)) *
      (Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c (s - 1)))⁻¹) by ring]
  rw [← div_eq_mul_inv, hnorm]
  have hmul := mul_le_mul_of_nonneg_left hint hA.le
  have htail' : Real.exp (-A) * (2 * s * A) <
      1 - (A + 1) * Real.exp (-A) :=
    (lt_div_iff₀ (by positivity : 0 < 2 * s * A)).mp htail
  calc
    1 < A * ((1 - Real.exp (-A)) / A +
        (1 - (A + 1) * Real.exp (-A)) / (2 * s * A ^ 2)) := by
      field_simp [hA0]
      nlinarith [htail']
    _ ≤ _ := hmul

/-- Direct plus majorant.  Its only source-side input is boundedness on the
fixed initial segment; no source structure carries expansion/remainder data. -/
noncomputable def section10_plus_commonMajorant_internal
    {R : ℝ → ℝ} {β S₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (hβ : β ≤ 3)
    (hS : Real.exp 2 + 1 ≤ S₀)
    (hcompact : ∃ B : ℝ, ∀ u ∈ Icc β S₀,
      -normalizedMinusBase R xi u ≤ B) :
    Section10PlusCommonMajorant R := by
  let B : ℝ := Classical.choose hcompact
  have hB := Classical.choose_spec hcompact
  let c : ℝ := max 64 (max 1 (B + 1))
  have hc64 : 64 ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := (le_max_left 1 (B + 1)).trans
    (le_max_right 64 (max 1 (B + 1)))
  have hBc : B + 1 ≤ c := (le_max_right 1 (B + 1)).trans
    (le_max_right 64 (max 1 (B + 1)))
  have hexpThree : 3 < Real.exp 2 :=
    by
      have hh := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      norm_num at hh ⊢
      exact hh
  have hβS : β < S₀ := by linarith
  have hβoneS : β + 1 ≤ S₀ := by linarith
  have hinitial : ∀ u ∈ Icc β S₀,
      0 < normalizedMinusBase R xi u + c := by
    intro u hu
    linarith [hB u hu]
  have hproducer : ProducesPlusFirstCrossing R β c S₀ :=
    producesPlusFirstCrossing h hβS hβoneS hinitial
  have hslope : ∀ s, S₀ ≤ s → 0 ≤ normalizedMinusBase R xi s + c := by
    intro v hvS
    by_cases hv : normalizedMinusBase R xi v + c < 0
    · obtain ⟨w, hSw⟩ := hproducer v hvS (le_of_lt hv)
      have hstrict := equation1055_internal_strict hc64 (hS.trans hSw)
      have hupper := plusFirstCrossing_scalarRatio_le_one h hadj w
      exact False.elim ((not_lt_of_ge hupper) hstrict)
    · exact le_of_not_gt hv
  refine ⟨c, S₀, hc1, ?_, ?_⟩
  · linarith
  · intro s hs
    have hs0 : 0 < s := by linarith [hS, Real.exp_pos 2]
    have hRs : 0 < R s := h.positive s (by linarith [hβ, hS, Real.exp_pos 2])
    have hn := hslope s hs
    have heq :
        -(R (s - 1)) + s * (xi s + c - 2 / s) * R s =
          (s * R s) * (normalizedMinusBase R xi s + c) := by
      dsimp [normalizedMinusBase]
      field_simp [ne_of_gt hs0, ne_of_gt hRs]
      ring
    rw [heq]
    exact mul_nonneg (mul_pos hs0 hRs).le hn


end Section10Equation1055SourceExpansion
