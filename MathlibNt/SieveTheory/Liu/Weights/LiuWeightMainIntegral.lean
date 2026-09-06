import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Liu's reciprocal-log main integral

This file defines the exact source integral and the uniform prime-sum transfer
predicate behind Liu's printed `0.49254` estimate. The downstream logarithmic
grid development proves the transfer predicate.
-/

open Filter MeasureTheory Set
open scoped Interval

namespace MathlibNt.SieveTheory.LiuWeight

noncomputable section

/-- The integrand in the inner integral printed in Liu's `lm-mt`. -/
def liuSourceInnerIntegrand (α β : ℝ) : ℝ :=
  1 / (β * (1 - α - β))

/-- The inner integral in Liu's `lm-mt`. -/
noncomputable def liuSourceInnerIntegral (α : ℝ) : ℝ :=
  ∫ β in (1 / 3 : ℝ)..(1 - α) / 2, liuSourceInnerIntegrand α β

/-- The source double integral in Liu's `lm-mt`. -/
noncomputable def liuSourceMainIntegral : ℝ :=
  ∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ),
    (1 / α) * liuSourceInnerIntegral α

/-- The one-dimensional integrand obtained after evaluating Liu's inner
integral. -/
def liuSourceReducedIntegrand (α : ℝ) : ℝ :=
  Real.log (2 - 3 * α) / (α * (1 - α))

lemma liuSource_inner_domain_pos {α β : ℝ}
    (hα : α ∈ Icc (1 / 10 : ℝ) (1 / 3 : ℝ))
    (hβ : β ∈ Icc (1 / 3 : ℝ) ((1 - α) / 2)) :
    0 < β ∧ 0 < 1 - α - β := by
  constructor
  · linarith [hβ.1]
  · linarith [hα.2, hβ.2]

lemma liuSource_inner_intervalIntegrable {α : ℝ}
    (hα : α ∈ Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) :
    IntervalIntegrable (liuSourceInnerIntegrand α) volume
      (1 / 3 : ℝ) ((1 - α) / 2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [hα.2])]
  apply ContinuousOn.div continuousOn_const
    (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro β hβ
  exact mul_ne_zero (liuSource_inner_domain_pos hα hβ).1.ne'
    (liuSource_inner_domain_pos hα hβ).2.ne'

/-- Exact evaluation of the inner integral in Liu's `lm-mt`. -/
theorem liuSourceInnerIntegral_eq {α : ℝ}
    (hα : α ∈ Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) :
    liuSourceInnerIntegral α = Real.log (2 - 3 * α) / (1 - α) := by
  have hle : (1 / 3 : ℝ) ≤ (1 - α) / 2 := by linarith [hα.2]
  have hαone : 0 < 1 - α := by linarith [hα.2]
  have hleft : IntervalIntegrable (fun β : ℝ => β⁻¹) volume
      (1 / 3 : ℝ) ((1 - α) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro β hβ
      rw [uIcc_of_le hle] at hβ
      exact (liuSource_inner_domain_pos hα hβ).1.ne'
    · exact continuousOn_id
  have hright : IntervalIntegrable (fun β : ℝ => (1 - α - β)⁻¹) volume
      (1 / 3 : ℝ) ((1 - α) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro β hβ
      rw [uIcc_of_le hle] at hβ
      exact (liuSource_inner_domain_pos hα hβ).2.ne'
    · exact continuousOn_const.sub continuousOn_id
  have hreflect :
      (∫ β in (1 / 3 : ℝ)..(1 - α) / 2, (1 - α - β)⁻¹) =
        ∫ β in (1 - α) - (1 - α) / 2..(1 - α) - 1 / 3, β⁻¹ := by
    simpa only using
      (intervalIntegral.integral_comp_sub_left
        (f := fun β : ℝ => β⁻¹) (a := (1 / 3 : ℝ))
        (b := (1 - α) / 2) (1 - α))
  have hthird : (0 : ℝ) < 1 / 3 := by norm_num
  have hhalf : 0 < (1 - α) / 2 := by positivity
  have htail : 0 < (1 - α) - 1 / 3 := by linarith [hα.2]
  have harg : 0 < 2 - 3 * α := by linarith [hα.2]
  unfold liuSourceInnerIntegral
  calc
    (∫ β in (1 / 3 : ℝ)..(1 - α) / 2, liuSourceInnerIntegrand α β) =
        ∫ β in (1 / 3 : ℝ)..(1 - α) / 2,
          (1 / (1 - α)) * (β⁻¹ + (1 - α - β)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro β hβ
            rw [uIcc_of_le hle] at hβ
            have hpos := liuSource_inner_domain_pos hα hβ
            dsimp [liuSourceInnerIntegrand]
            field_simp [hαone.ne', hpos.1.ne', hpos.2.ne']
            ring
    _ = (1 / (1 - α)) *
        (∫ β in (1 / 3 : ℝ)..(1 - α) / 2,
          (β⁻¹ + (1 - α - β)⁻¹)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (1 / (1 - α)) *
        ((∫ β in (1 / 3 : ℝ)..(1 - α) / 2, β⁻¹) +
          ∫ β in (1 / 3 : ℝ)..(1 - α) / 2, (1 - α - β)⁻¹) := by
            rw [intervalIntegral.integral_add hleft hright]
    _ = (1 / (1 - α)) *
        (Real.log (((1 - α) / 2) / (1 / 3)) +
          Real.log (((1 - α) - 1 / 3) /
            ((1 - α) - (1 - α) / 2))) := by
            rw [integral_inv_of_pos hthird hhalf]
            rw [hreflect]
            rw [integral_inv_of_pos
              (by linarith [hαone]) htail]
    _ = Real.log (2 - 3 * α) / (1 - α) := by
      rw [Real.log_div hhalf.ne' hthird.ne']
      rw [Real.log_div htail.ne' (by linarith [hαone] :
        (1 - α) - (1 - α) / 2 ≠ 0)]
      rw [show (1 - α) - (1 - α) / 2 = (1 - α) / 2 by ring]
      rw [show (1 - α) - (1 / 3 : ℝ) = (2 - 3 * α) / 3 by ring]
      rw [Real.log_div harg.ne' (by norm_num : (3 : ℝ) ≠ 0)]
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0)]
      rw [Real.log_one]
      ring

lemma liuSource_reduced_intervalIntegrable :
    IntervalIntegrable liuSourceReducedIntegrand volume
      (1 / 10 : ℝ) (1 / 3 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
  apply ContinuousOn.div
  · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
      (fun α hα => by
        simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
        linarith [hα.2])
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro α hα
    exact mul_ne_zero (by linarith [hα.1]) (by linarith [hα.2])

/-- Liu's double integral is exactly the reduced one-dimensional integral. -/
theorem liuSourceMainIntegral_eq_reduced :
    liuSourceMainIntegral =
      ∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ), liuSourceReducedIntegrand α := by
  unfold liuSourceMainIntegral
  apply intervalIntegral.integral_congr
  intro α hα
  rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] at hα
  change (1 / α) * liuSourceInnerIntegral α = liuSourceReducedIntegrand α
  rw [liuSourceInnerIntegral_eq hα]
  dsimp [liuSourceReducedIntegrand]
  have hαne : α ≠ 0 := by linarith [hα.1]
  have h1αne : 1 - α ≠ 0 := by linarith [hα.2]
  field_simp [hαne, h1αne]

private def liuSourceLogMajorant (y : ℝ) : ℝ :=
  2 * y + (2 / 3) * y ^ 3 + (2 / 5) * y ^ 5 + (2 / 7) * y ^ 7 +
    (2 / 9) * y ^ 9 + (2 / 11) * y ^ 11 + (729 / 340) * y ^ 13

private def liuSourceLogMajorantAntideriv (y : ℝ) : ℝ :=
  (-729 / 4420) * y ^ 13 + (-81 / 1360) * y ^ 12 +
    (-1571 / 41140) * y ^ 11 + (-1571 / 112200) * y ^ 10 +
    (-3017 / 100980) * y ^ 9 + (-3017 / 269280) * y ^ 8 +
    (-223079 / 4948020) * y ^ 7 + (-223079 / 12723480) * y ^ 6 +
    (-110711 / 1272348) * y ^ 5 + (-553555 / 15268176) * y ^ 4 +
    (-8187643 / 34353396) * y ^ 3 + (-8187643 / 68706792) * y ^ 2 +
    (-214308019 / 103060188) * y

private def liuSourceLogMajorantIntegralAntideriv (y : ℝ) : ℝ :=
  (-214308019 / 309180564) * Real.log (1 - 3 * y) +
    liuSourceLogMajorantAntideriv y

private lemma liuSource_reduced_integral_change :
    (∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ), liuSourceReducedIntegrand α) =
      3 * ∫ y in (0 : ℝ)..7 / 27,
        Real.log ((1 + y) / (1 - y)) / (1 - 3 * y) := by
  let g : ℝ → ℝ := fun x => Real.log (1 + x) / ((1 - x) * (2 + x))
  have hlinear := intervalIntegral.integral_comp_add_mul
    (f := g) (a := (1 / 10 : ℝ)) (b := (1 / 3 : ℝ))
    (c := (-3 : ℝ)) (by norm_num) 1
  rw [show (1 + -3 * (1 / 10 : ℝ)) = 7 / 10 by norm_num,
    show (1 + -3 * (1 / 3 : ℝ)) = 0 by norm_num] at hlinear
  have hfirst :
      (∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ), liuSourceReducedIntegrand α) =
        3 * ∫ x in (0 : ℝ)..7 / 10, g x := by
    calc
      (∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ), liuSourceReducedIntegrand α) =
          9 * ∫ α in (1 / 10 : ℝ)..(1 / 3 : ℝ), g (1 + -3 * α) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro α hα
            rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] at hα
            have hα0 : α ≠ 0 := by linarith [hα.1]
            have hα1 : 1 - α ≠ 0 := by linarith [hα.2]
            dsimp [liuSourceReducedIntegrand, g]
            rw [show 2 - 3 * α = 1 + (1 + -3 * α) by ring]
            rw [show 1 - (1 + -3 * α) = 3 * α by ring,
              show 2 + (1 + -3 * α) = 3 * (1 - α) by ring]
            field_simp [hα0, hα1]
            ; ring
      _ = 3 * ∫ x in (0 : ℝ)..7 / 10, g x := by
        rw [hlinear, intervalIntegral.integral_symm]
        norm_num [smul_eq_mul]
        ; ring
  let f : ℝ → ℝ := fun y => 2 * y / (1 - y)
  let f' : ℝ → ℝ := fun y => 2 / (1 - y) ^ 2
  have hf : ContinuousOn f (uIcc (0 : ℝ) (7 / 27)) := by
    apply ContinuousOn.div (continuousOn_const.mul continuousOn_id)
      (continuousOn_const.sub continuousOn_id)
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
    dsimp
    linarith [hy.2]
  have hderiv : ∀ y ∈ Ioo (min (0 : ℝ) (7 / 27)) (max (0 : ℝ) (7 / 27)),
      HasDerivWithinAt f (f' y) (Ioi y) y := by
    intro y hy
    apply HasDerivAt.hasDerivWithinAt
    have hden : 1 - y ≠ 0 := by
      norm_num at hy
      linarith [hy.2]
    have hn : HasDerivAt (fun z : ℝ => 2 * z) 2 y := by
      simpa using (hasDerivAt_id y).const_mul 2
    have hd : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    exact (hn.div hd hden).congr_deriv (by dsimp [f']; ring)
  have hf' : ContinuousOn f' (uIcc (0 : ℝ) (7 / 27)) := by
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.sub continuousOn_id).pow 2)
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
    exact pow_ne_zero 2 (by dsimp; linarith [hy.2])
  have hg : ContinuousOn g (f '' uIcc (0 : ℝ) (7 / 27)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
      have h1y : 1 - y ≠ 0 := by linarith [hy.2]
      dsimp [f]
      rw [show 1 + 2 * y / (1 - y) = (1 + y) / (1 - y) by
        field_simp [h1y] ; ring]
      exact div_ne_zero (by linarith [hy.1]) h1y
    · exact (continuousOn_const.sub continuousOn_id).mul
        (continuousOn_const.add continuousOn_id)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
      have h1y : 1 - y ≠ 0 := by linarith [hy.2]
      dsimp [f]
      rw [show 1 - 2 * y / (1 - y) = (1 - 3 * y) / (1 - y) by
          field_simp [h1y] ; ring,
        show 2 + 2 * y / (1 - y) = 2 / (1 - y) by
          field_simp [h1y] ; ring]
      exact mul_ne_zero (div_ne_zero (by linarith [hy.2]) h1y)
        (div_ne_zero (by norm_num) h1y)
  have hchange := intervalIntegral.integral_comp_mul_deriv'' hf hderiv hf' hg
  dsimp [f] at hchange
  rw [show 2 * (0 : ℝ) / (1 - 0) = 0 by norm_num,
    show 2 * (7 / 27 : ℝ) / (1 - 7 / 27) = 7 / 10 by norm_num] at hchange
  rw [hfirst, ← hchange]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
  have h1y : 1 - y ≠ 0 := by linarith [hy.2]
  have h13y : 1 - 3 * y ≠ 0 := by linarith [hy.2]
  dsimp [Function.comp_def, f, f', g]
  rw [show 1 + 2 * y / (1 - y) = (1 + y) / (1 - y) by
    field_simp [h1y] ; ring]
  field_simp [h1y, h13y]
  ; ring

private lemma liuSource_log_le_majorant {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) (7 / 27)) :
    Real.log ((1 + y) / (1 - y)) ≤ liuSourceLogMajorant y := by
  have hylt : y < 1 := by linarith [hy.2]
  have hsquare : y ^ 2 ≤ (7 / 27 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.2)
      (by linarith [hy.1] : 0 ≤ 7 / 27 + y)]
  have hden : 0 < 1 - y ^ 2 := by nlinarith
  have hrecip : 1 / (1 - y ^ 2) ≤ (729 / 680 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have htail := mul_le_mul_of_nonneg_left hrecip (pow_nonneg hy.1 13)
  have hlog := Real.log_div_le_sum_range_add hy.1 hylt 6
  norm_num [Finset.sum_range_succ] at hlog
  dsimp [liuSourceLogMajorant]
  ring_nf at hlog htail ⊢
  linarith

private lemma liuSource_transformed_intervalIntegrable :
    IntervalIntegrable
      (fun y : ℝ => Real.log ((1 + y) / (1 - y)) / (1 - 3 * y))
      volume 0 (7 / 27) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)]
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · apply ContinuousOn.div
        (continuousOn_const.add continuousOn_id)
        (continuousOn_const.sub continuousOn_id)
      intro y hy
      change 1 - y ≠ 0
      linarith [hy.2]
    · intro y hy
      exact div_ne_zero (by linarith [hy.1]) (by linarith [hy.2])
  · exact continuousOn_const.sub (continuousOn_const.mul continuousOn_id)
  · intro y hy
    linarith [hy.2]

private lemma liuSource_majorant_intervalIntegrable :
    IntervalIntegrable
      (fun y : ℝ => liuSourceLogMajorant y / (1 - 3 * y))
      volume 0 (7 / 27) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)]
  apply ContinuousOn.div
  · change ContinuousOn
      (fun y : ℝ =>
        2 * y + (2 / 3) * y ^ 3 + (2 / 5) * y ^ 5 + (2 / 7) * y ^ 7 +
          (2 / 9) * y ^ 9 + (2 / 11) * y ^ 11 + (729 / 340) * y ^ 13) _
    fun_prop
  · exact continuousOn_const.sub (continuousOn_const.mul continuousOn_id)
  · intro y hy
    linarith [hy.2]

/-- Derivative certificate for the logarithmic term and polynomial majorant primitive. -/
private lemma liuSource_majorant_hasDerivAt {y : ℝ}
    (hy : y ∈ uIcc (0 : ℝ) (7 / 27)) :
    HasDerivAt liuSourceLogMajorantIntegralAntideriv
      (3 * (liuSourceLogMajorant y / (1 - 3 * y))) y := by
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7 / 27)] at hy
  have hden : 1 - 3 * y ≠ 0 := by linarith [hy.2]
  have hthree : HasDerivAt (fun z : ℝ => 3 * z) 3 y := by
    simpa using (hasDerivAt_id y).const_mul 3
  have hlog : HasDerivAt (fun z : ℝ => Real.log (1 - 3 * z))
      (-3 / (1 - 3 * y)) y := (hthree.const_sub 1).log hden
  have hpoly : HasDerivAt liuSourceLogMajorantAntideriv
      (3 * liuSourceLogMajorant y / (1 - 3 * y) -
        3 * (214308019 / 309180564) / (1 - 3 * y)) y := by
    have h13 := ((hasDerivAt_id y).pow 13).const_mul (-729 / 4420 : ℝ)
    have h12 := ((hasDerivAt_id y).pow 12).const_mul (-81 / 1360 : ℝ)
    have h11 := ((hasDerivAt_id y).pow 11).const_mul (-1571 / 41140 : ℝ)
    have h10 := ((hasDerivAt_id y).pow 10).const_mul (-1571 / 112200 : ℝ)
    have h9 := ((hasDerivAt_id y).pow 9).const_mul (-3017 / 100980 : ℝ)
    have h8 := ((hasDerivAt_id y).pow 8).const_mul (-3017 / 269280 : ℝ)
    have h7 := ((hasDerivAt_id y).pow 7).const_mul (-223079 / 4948020 : ℝ)
    have h6 := ((hasDerivAt_id y).pow 6).const_mul (-223079 / 12723480 : ℝ)
    have h5 := ((hasDerivAt_id y).pow 5).const_mul (-110711 / 1272348 : ℝ)
    have h4 := ((hasDerivAt_id y).pow 4).const_mul (-553555 / 15268176 : ℝ)
    have h3 := ((hasDerivAt_id y).pow 3).const_mul (-8187643 / 34353396 : ℝ)
    have h2 := ((hasDerivAt_id y).pow 2).const_mul (-8187643 / 68706792 : ℝ)
    have h1 := (hasDerivAt_id y).const_mul (-214308019 / 103060188 : ℝ)
    have hsum2 := h13.add h12
    have hsum3 := hsum2.add h11
    have hsum4 := hsum3.add h10
    have hsum5 := hsum4.add h9
    have hsum6 := hsum5.add h8
    have hsum7 := hsum6.add h7
    have hsum8 := hsum7.add h6
    have hsum9 := hsum8.add h5
    have hsum10 := hsum9.add h4
    have hsum11 := hsum10.add h3
    have hsum12 := hsum11.add h2
    have hsum := hsum12.add h1
    convert hsum using 1
    all_goals try rfl
    norm_num [id_eq, liuSourceLogMajorant]
    field_simp [hden]
    ring
  have htotal : HasDerivAt
      ((fun z : ℝ => (-214308019 / 309180564) * Real.log (1 - 3 * z)) +
        liuSourceLogMajorantAntideriv)
      (3 * (liuSourceLogMajorant y / (1 - 3 * y))) y :=
    ((hlog.const_mul (-214308019 / 309180564 : ℝ)).add hpoly).congr_deriv
      (by field_simp [hden]; ring)
  convert htotal using 1
  all_goals try rfl

private lemma liuSource_majorant_integral_eq :
    3 * ∫ y in (0 : ℝ)..7 / 27,
        liuSourceLogMajorant y / (1 - 3 * y) =
      (214308019 / 309180564) * Real.log (9 / 2) -
        21864298677554399495239 / 39641290296069664144800 := by
  have hint : IntervalIntegrable
      (fun y : ℝ => 3 * (liuSourceLogMajorant y / (1 - 3 * y)))
      volume 0 (7 / 27) := by
    exact liuSource_majorant_intervalIntegrable.const_mul (3 : ℝ)
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hy => liuSource_majorant_hasDerivAt hy) hint
  rw [← intervalIntegral.integral_const_mul]
  rw [heval]
  have hloginv : -Real.log (2 / 9 : ℝ) = Real.log (9 / 2 : ℝ) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  dsimp [liuSourceLogMajorantIntegralAntideriv,
    liuSourceLogMajorantAntideriv]
  rw [show (1 - 3 * (7 / 27 : ℝ)) = 2 / 9 by norm_num,
    show (1 - 3 * (0 : ℝ)) = 1 by norm_num, Real.log_one]
  norm_num
  linarith [hloginv]

private lemma liuSource_log_nine_halves_le :
    Real.log (9 / 2 : ℝ) ≤
      2330397792547147 / 1549384193150640 := by
  have h₂ := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 6
  have h₉ := Real.log_div_le_sum_range_add
    (x := (1 / 17 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h₂ h₉
  rw [show (9 / 2 : ℝ) = (2 * 2) * (9 / 8) by norm_num,
    Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0)
      (by norm_num : (9 / 8 : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- Liu's source main integral is strictly below the printed constant. -/
theorem liuSourceMainIntegral_lt : liuSourceMainIntegral < 0.49254 := by
  rw [liuSourceMainIntegral_eq_reduced, liuSource_reduced_integral_change]
  have hmono :
      (∫ y in (0 : ℝ)..7 / 27,
          Real.log ((1 + y) / (1 - y)) / (1 - 3 * y)) ≤
        ∫ y in (0 : ℝ)..7 / 27,
          liuSourceLogMajorant y / (1 - 3 * y) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      liuSource_transformed_intervalIntegrable
      liuSource_majorant_intervalIntegrable
    intro y hy
    exact div_le_div_of_nonneg_right (liuSource_log_le_majorant hy)
      (by linarith [hy.2])
  have hscaled := mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 3)
  rw [liuSource_majorant_integral_eq] at hscaled
  have hlogscaled := mul_le_mul_of_nonneg_left liuSource_log_nine_halves_le
    (by norm_num : (0 : ℝ) ≤ 214308019 / 309180564)
  calc
    3 * (∫ y in (0 : ℝ)..7 / 27,
        Real.log ((1 + y) / (1 - y)) / (1 - 3 * y))
        ≤ (214308019 / 309180564) * Real.log (9 / 2) -
          21864298677554399495239 / 39641290296069664144800 := hscaled
    _ ≤ 2708303448755077502730999486461 /
          5515926424558845342117042772800 := by
      norm_num at hlogscaled ⊢
      linarith
    _ < 0.49254 := by norm_num

/-- The purely symbolic constant inequality used in Liu's transfer argument. -/
def LiuSourceMainIntegralConstantBound : Prop :=
  liuSourceMainIntegral < 0.49254

/-- The source main integral satisfies its named constant-bound predicate. -/
theorem liuSourceMainIntegralConstantBound :
    LiuSourceMainIntegralConstantBound :=
  liuSourceMainIntegral_lt

/-- A source-faithful, uniform eventual transfer from Liu's finite prime-pair
sum to the source integral. Its quantifier order fixes the grid before choosing
the finite-`N` threshold. -/
def LiuSourcePrimeSumToIntegralTransfer : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Real.log N * liuSourceReciprocalLogSum N ≤
      liuSourceMainIntegral + η

/-- An explicit positive margin below Liu's printed decimal. -/
def LiuSourceMainIntegralMargin (δ : ℝ) : Prop :=
  0 < δ ∧ liuSourceMainIntegral ≤ 0.49254 - δ

theorem eventually_liuSourceReciprocalLogBound_of_transfer_of_margin
    (htransfer : LiuSourcePrimeSumToIntegralTransfer)
    {δ : ℝ} (hmargin : LiuSourceMainIntegralMargin δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → LiuSourceReciprocalLogBound N := by
  obtain ⟨N₀, hN₀⟩ := htransfer (δ / 2) (half_pos hmargin.1)
  refine ⟨max 3 N₀, fun N hN => ?_⟩
  have hlog : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold LiuSourceReciprocalLogBound
  rw [le_div_iff₀ hlog]
  calc
    liuSourceReciprocalLogSum N * Real.log N
        ≤ liuSourceMainIntegral + δ / 2 := by
          simpa only [mul_comm] using hN₀ N (le_trans (le_max_right _ _) hN)
    _ ≤ 0.49254 - δ + δ / 2 := by linarith [hmargin.2]
    _ ≤ 0.49254 := by linarith [hmargin.1]

theorem eventually_liuSourceReciprocalLogBound_of_transfer_of_constantBound
    (htransfer : LiuSourcePrimeSumToIntegralTransfer)
    (hconstant : LiuSourceMainIntegralConstantBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → LiuSourceReciprocalLogBound N := by
  let δ := 0.49254 - liuSourceMainIntegral
  apply eventually_liuSourceReciprocalLogBound_of_transfer_of_margin htransfer
  constructor
  · exact sub_pos.mpr hconstant
  · linarith

end
end MathlibNt.SieveTheory.LiuWeight
