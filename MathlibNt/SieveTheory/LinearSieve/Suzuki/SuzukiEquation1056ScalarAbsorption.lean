import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053KernelExpansion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

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
        field_simp [ne_of_gt hm']
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
    convert hh using 1 <;> ring
  unfold Equation1053EarliestScalarInequality equation1056ScalarRatio
  have hmul := mul_le_mul_of_nonneg_left hK hA.le
  apply lt_of_le_of_lt _ hfactor
  dsimp [A, m] at hmul ⊢
  convert hmul using 1 <;> ring

lemma xi_nonneg (s : ℝ) : 0 ≤ xi s := by
  exact (etaOrderIso.symm ⟨max s 1, le_max_right s 1⟩).property

lemma xi_tendsto_atTop_local : Tendsto xi atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  let B₀ : ℝ := max B 0
  let S : ℝ := max 2 (eta B₀ + 1)
  apply eventually_atTop.2
  refine ⟨S, fun s hs => ?_⟩
  have hs2 : 2 ≤ s := (le_max_left 2 (eta B₀ + 1)).trans hs
  have hs1 : 1 < s := by linarith
  have hB0 : 0 ≤ B₀ := le_max_right B 0
  have hxi0 : 0 ≤ xi s := xi_nonneg s
  have hetaXi : eta (xi s) = s := by rw [eta_xi, max_eq_left hs1.le]
  have hetaB : eta B₀ + 1 ≤ s := (le_max_right 2 (eta B₀ + 1)).trans hs
  have hxiB0 : B₀ ≤ xi s := by
    by_contra hn
    have hlt : xi s < B₀ := lt_of_not_ge hn
    have hη := eta_strictMonoOn hxi0 hB0 hlt
    rw [hetaXi] at hη
    linarith
  exact (le_max_left B 0).trans hxiB0

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
    apply (div_le_div_iff₀ hu0 (by linarith [hs])).2
    nlinarith [hu.1]
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

lemma eventual_elementary_absorption (c : ℝ) (hc : 1152 ≤ c) :
    ∃ S : ℝ, ∀ s, S ≤ s →
      3 ≤ s ∧
      0 < xi (s - 1) - c - kappaOneLogSlope (s - 1) ∧
      0 < xi s - c - 2 / s ∧
      (xi s - c - 2 / s -
          (xi (s - 1) - c - kappaOneLogSlope (s - 1)) <
        (xi s - c - 2 / s) *
          Real.exp (-(xi (s - 1) - c - kappaOneLogSlope (s - 1)))) := by
  have hev : ∀ᶠ s in atTop, 2 * c + 4 ≤ xi (s - 1) := by
    have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop :=
      by
        rw [tendsto_atTop]
        intro B
        filter_upwards [eventually_ge_atTop (B + 1)] with s hs
        linarith
    exact (xi_tendsto_atTop_local.comp hshift).eventually (eventually_ge_atTop (2 * c + 4))
  apply eventually_atTop.1
  filter_upwards [hev, eventually_ge_atTop (4 : ℝ)] with s hxi hs
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hx2 : 2 ≤ xi (s - 1) := by linarith [hc]
  have hks0 := kappaOneLogSlope_nonneg (u := s - 1) (by linarith)
  have hks := kappaOneLogSlope_le_three_div (u := s - 1) (by linarith)
  have hdelta0 := proposition1020_secant_nonneg canonicalXi_proposition1020
    (t := s - 1) (s := s) (by linarith) (by linarith)
  have hdelta := xi_unit_increment_le hs hx2
  have htwo : 2 / s ≤ 1 := by
    apply (div_le_iff₀ hs0).2
    nlinarith
  have hthree : 3 / (s - 1) ≤ 6 / s := by
    apply (div_le_div_iff₀ hsm0 hs0).2
    nlinarith
  have htwo' : 2 / (s - 1) ≤ 4 / s := by
    apply (div_le_div_iff₀ hsm0 hs0).2
    nlinarith
  have hgapUpper :
      xi s - c - 2 / s - (xi (s - 1) - c - kappaOneLogSlope (s - 1)) ≤
        10 / s := by
    have heq : xi s - c - 2 / s -
        (xi (s - 1) - c - kappaOneLogSlope (s - 1)) =
        (xi s - xi (s - 1)) + kappaOneLogSlope (s - 1) - 2 / s := by ring
    rw [heq]
    have hd4 := hdelta.trans htwo'
    have hk6 := hks.trans hthree
    calc
      xi s - xi (s - 1) + kappaOneLogSlope (s - 1) - 2 / s ≤
          4 / s + 6 / s - 2 / s := sub_le_sub_right (add_le_add hd4 hk6) _
      _ = 8 / s := by ring
      _ ≤ 10 / s := by
        apply (div_le_div_iff₀ hs0 hs0).2
        nlinarith
  have hAhalf : xi (s - 1) / 2 ≤ xi s - c - 2 / s := by
    linarith
  have hmpos : 0 < xi (s - 1) - c - kappaOneLogSlope (s - 1) := by
    have hk2 : kappaOneLogSlope (s - 1) ≤ 2 := by
      calc
        kappaOneLogSlope (s - 1) ≤ 3 / (s - 1) := hks
        _ ≤ 2 := by
          apply (div_le_iff₀ hsm0).2
          nlinarith
    linarith
  have hApos : 0 < xi s - c - 2 / s := lt_of_lt_of_le (by linarith [hx2]) hAhalf
  have heqc :
      Real.exp (-(xi (s - 1) - c - kappaOneLogSlope (s - 1))) =
        Real.exp c * Real.exp (kappaOneLogSlope (s - 1)) * Real.exp (-(xi (s - 1))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexpk : 1 ≤ Real.exp (kappaOneLogSlope (s - 1)) :=
    Real.one_le_exp hks0
  have hxipos : 0 < xi (s - 1) := by linarith
  have hs1 : 1 < s - 1 := by linarith
  have hEqXi := xi_equation hs1
  have hnegxi : Real.exp (-(xi (s - 1))) =
      1 / (1 + (s - 1) * xi (s - 1)) := by
    have he : Real.exp (xi (s - 1)) = 1 + (s - 1) * xi (s - 1) := by
      linarith
    rw [Real.exp_neg, he]
    rw [one_div]
  have hdenpos : 0 < 1 + (s - 1) * xi (s - 1) := by positivity
  have hdenle : 1 + (s - 1) * xi (s - 1) ≤ s * xi (s - 1) := by
    nlinarith
  have hbase : 1 / (s * xi (s - 1)) ≤ Real.exp (-(xi (s - 1))) := by
    rw [hnegxi]
    exact one_div_le_one_div_of_le hdenpos hdenle
  have hexpc : 20 < Real.exp c := by
    have := Real.add_one_lt_exp (ne_of_gt (by linarith [hc] : 0 < c))
    linarith [hc]
  have hrhs : 10 / s <
      (xi s - c - 2 / s) *
        Real.exp (-(xi (s - 1) - c - kappaOneLogSlope (s - 1))) := by
    rw [heqc]
    have hExpLower : Real.exp c * (1 / (s * xi (s - 1))) ≤
        Real.exp c * Real.exp (kappaOneLogSlope (s - 1)) * Real.exp (-(xi (s - 1))) := by
      have hcpos : 0 ≤ Real.exp c := (Real.exp_pos c).le
      have h1 := mul_le_mul_of_nonneg_left hbase hcpos
      have h2 := mul_le_mul_of_nonneg_right hexpk
        (Real.exp_pos (-(xi (s - 1)))).le
      simp only [one_mul] at h2
      calc
        Real.exp c * (1 / (s * xi (s - 1))) ≤
            Real.exp c * Real.exp (-(xi (s - 1))) := h1
        _ ≤ Real.exp c * (Real.exp (kappaOneLogSlope (s - 1)) *
              Real.exp (-(xi (s - 1)))) := mul_le_mul_of_nonneg_left h2 hcpos
        _ = _ := by ring
    have hprod : (Real.exp c / (2 * s)) ≤
        (xi s - c - 2 / s) *
          (Real.exp c * Real.exp (kappaOneLogSlope (s - 1)) * Real.exp (-(xi (s - 1)))) := by
      have hh := mul_le_mul hAhalf hExpLower
        (by positivity : 0 ≤ Real.exp c * (1 / (s * xi (s - 1)))) hApos.le
      calc
        Real.exp c / (2 * s) =
            (xi (s - 1) / 2) * (Real.exp c * (1 / (s * xi (s - 1)))) := by
              field_simp [ne_of_gt hs0, ne_of_gt hxipos]
        _ ≤ _ := hh
    have : 10 / s < Real.exp c / (2 * s) := by
      apply (div_lt_div_iff₀ hs0 (mul_pos (by norm_num) hs0)).2
      nlinarith
    exact this.trans_le hprod
  exact ⟨by linarith, hmpos, hApos, hgapUpper.trans_lt hrhs⟩

/-- Final source-(10.56) scalar absorption: for every fixed `c ≥ 1152`,
the canonical `ξ` makes the normalized scalar product strictly less than one
for all sufficiently large `s`. -/
theorem equation1056_eventually_strict (c : ℝ) (hc : 1152 ≤ c) :
    ∃ S : ℝ, ∀ s, S ≤ s → Equation1053EarliestScalarInequality xi c s := by
  obtain ⟨S, hS⟩ := eventual_elementary_absorption c hc
  refine ⟨S, fun s hs => ?_⟩
  rcases hS s hs with ⟨hs3, hm, hA, hgap⟩
  exact scalar_absorption_of_elementary_bounds hs3 hm hA hgap

/-- The literal final contradiction in (10.56): the source-side lower bound
`1 ≤ ratio` is incompatible with the eventual strict absorption. -/
theorem equation1056_eventually_contradiction (c : ℝ) (hc : 1152 ≤ c) :
    ∃ S : ℝ, ∀ s, S ≤ s →
      1 ≤ equation1056ScalarRatio xi c s → False := by
  obtain ⟨S, hS⟩ := equation1056_eventually_strict c hc
  exact ⟨S, fun s hs hsource => (not_lt_of_ge hsource) (hS s hs)⟩


end Section10Equation1056ScalarAbsorption
