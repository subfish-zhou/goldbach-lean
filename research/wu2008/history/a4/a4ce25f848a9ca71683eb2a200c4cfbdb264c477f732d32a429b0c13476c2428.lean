import MathlibNt.Wu2004MeanValue.SieveSupport
import MathlibNt.SieveTheory.Switching.SourceSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The literal half-level Rosser ratio at the logarithmically reduced square-root
modulus cutoff. No natural rounding enters the analytic cutoff or its ratio. -/

namespace Wu2004MeanValue

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

def sieveAsymptoticQ (B x : ℝ) : ℝ := Real.sqrt x / Real.log x ^ B

def sieveAsymptoticZ (B x : ℝ) : ℝ := Real.sqrt (sieveAsymptoticQ B x)

def sieveAsymptoticRatio (B x : ℝ) : ℝ :=
  Real.log (sieveAsymptoticQ B x / 2) / Real.log (sieveAsymptoticZ B x)

theorem sieveAsymptoticQ_pos (B : ℝ) {x : ℝ} (hx : 1 < x) :
    0 < sieveAsymptoticQ B x :=
  div_pos (Real.sqrt_pos.2 (by linarith))
    (Real.rpow_pos_of_pos (Real.log_pos hx) B)

theorem log_sieveAsymptoticQ (B : ℝ) {x : ℝ} (hx : 1 < x) :
    Real.log (sieveAsymptoticQ B x) =
      Real.log x / 2 - B * Real.log (Real.log x) := by
  rw [sieveAsymptoticQ, Real.log_div
    (Real.sqrt_pos.2 (by linarith : 0 < x)).ne'
    (Real.rpow_pos_of_pos (Real.log_pos hx) B).ne',
    Real.log_sqrt (by linarith), Real.log_rpow (Real.log_pos hx)]

theorem tendsto_log_sieveAsymptoticQ_div_log (B : ℝ) :
    Tendsto (fun x => Real.log (sieveAsymptoticQ B x) / Real.log x)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop
  have h' : Tendsto (fun x : ℝ =>
      1 / 2 - B * (Real.log (Real.log x) / Real.log x))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (hsmall.const_mul B)
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [log_sieveAsymptoticQ B hx]
  field_simp [(Real.log_pos hx).ne']

theorem tendsto_log_sieveAsymptoticQ_atTop (B : ℝ) :
    Tendsto (fun x => Real.log (sieveAsymptoticQ B x)) atTop atTop := by
  have h := (tendsto_log_sieveAsymptoticQ_div_log B).pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2) Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact div_mul_cancel₀ _ (Real.log_pos hx).ne'

theorem tendsto_sieveAsymptoticQ_atTop (B : ℝ) :
    Tendsto (sieveAsymptoticQ B) atTop atTop := by
  apply (Real.tendsto_exp_atTop.comp (tendsto_log_sieveAsymptoticQ_atTop B)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact Real.exp_log (sieveAsymptoticQ_pos B hx)

theorem tendsto_sieveAsymptoticZ_atTop (B : ℝ) :
    Tendsto (sieveAsymptoticZ B) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_sieveAsymptoticQ_atTop B)

theorem tendsto_log_sieveAsymptoticZ_div_log (B : ℝ) :
    Tendsto (fun x => Real.log (sieveAsymptoticZ B x) / Real.log x)
      atTop (nhds (1 / 4 : ℝ)) := by
  have h := (tendsto_log_sieveAsymptoticQ_div_log B).div_const 2
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [sieveAsymptoticZ, Real.log_sqrt (sieveAsymptoticQ_pos B hx).le]
  ring

theorem sieveAsymptoticRatio_eq (B : ℝ) {x : ℝ}
    (hx : 1 < x) (hQ : 1 < sieveAsymptoticQ B x) :
    sieveAsymptoticRatio B x =
      2 - 2 * Real.log 2 / Real.log (sieveAsymptoticQ B x) := by
  rw [sieveAsymptoticRatio, sieveAsymptoticZ,
    Real.log_sqrt (sieveAsymptoticQ_pos B hx).le,
    Real.log_div (sieveAsymptoticQ_pos B hx).ne' (by norm_num)]
  field_simp [(Real.log_pos hQ).ne']

theorem tendsto_sieveAsymptoticRatio (B : ℝ) :
    Tendsto (sieveAsymptoticRatio B) atTop (nhds 2) := by
  have hsmall := (tendsto_log_sieveAsymptoticQ_atTop B).const_div_atTop
    (2 * Real.log 2)
  have h : Tendsto (fun x => 2 - 2 * Real.log 2 /
      Real.log (sieveAsymptoticQ B x)) atTop (nhds 2) := by
    simpa using tendsto_const_nhds.sub hsmall
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sieveAsymptoticQ_atTop B).eventually (eventually_gt_atTop 1)]
    with x hx hQ
  exact (sieveAsymptoticRatio_eq B hx hQ).symm

theorem eventually_sieveAsymptoticRatio_mem (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, sieveAsymptoticRatio B x ∈ Set.Icc (3 / 2) 3 := by
  exact (tendsto_sieveAsymptoticRatio B).eventually
    (Icc_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3))

theorem tendsto_sieveAsymptoticUpperFactor (B : ℝ) :
    Tendsto (fun x => jurkatRichertUpperLinearSieveFactor (sieveAsymptoticRatio B x))
      atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h := (tendsto_const_nhds (x := 2 * Real.exp Real.eulerMascheroniConstant)).div
    (tendsto_sieveAsymptoticRatio B)
    (by norm_num : (2 : ℝ) ≠ 0)
  have h' : Tendsto (fun x => 2 * Real.exp Real.eulerMascheroniConstant /
      sieveAsymptoticRatio B x) atTop
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
    convert h using 1
    · ext x
      rfl
    · congr 1
      ring
  apply h'.congr'
  filter_upwards [eventually_sieveAsymptoticRatio_mem B] with x hx
  simp [jurkatRichertUpperLinearSieveFactor, hx.2]

end
end Wu2004MeanValue
