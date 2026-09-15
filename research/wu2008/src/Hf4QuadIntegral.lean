import Hf4QuadKernel
import SigmaActualNineCellFTC

noncomputable section
namespace Hf4Quad
open Real Set MeasureTheory SigmaVariableOuterPayment SigmaActualBlockSeparable
open scoped Interval

theorem Model.neg {f : ℝ → ℝ} {p : Cubic} {e : ℝ} (hf : Model f p e) :
    Model (fun x => -f x) ⟨-p.a,-p.b,-p.c,-p.d⟩ e := by
  intro x hx
  have he : -f x-Cubic.eval ⟨-p.a,-p.b,-p.c,-p.d⟩ x = -(f x-p.eval x) := by
    simp only [Cubic.eval]
    ring
  rw [he,abs_neg]
  exact hf x hx

theorem Model.constant (a : ℝ) : Model (fun _ => a) ⟨a,0,0,0⟩ 0 := by
  intro x _
  simp [Cubic.eval]

theorem Model.variable (m h : ℝ) : Model (fun x => m+h*x) ⟨m,h,0,0⟩ 0 := by
  intro x _
  simp [Cubic.eval]

theorem Model.radical : Model (fun _ => TerminalE.radical)
    ⟨(7745966692415/2000000000000),0,0,0⟩ (1/2000000000000) := by
  intro x _
  simp only [Cubic.eval,zero_mul,add_zero]
  apply abs_le.mpr
  constructor <;> linarith only [Hf4Target.radical_bounds.1,Hf4Target.radical_bounds.2]

def Cubic.primitive (p : Cubic) (m h t : ℝ) : ℝ :=
  h*(p.a*((t-m)/h)+p.b*((t-m)/h)^2/2+p.c*((t-m)/h)^3/3+p.d*((t-m)/h)^4/4)

theorem Cubic.primitive_deriv (p : Cubic) (m h t : ℝ) (hh : h ≠ 0) :
    HasDerivAt (p.primitive m h) (p.eval ((t-m)/h)) t := by
  have hy := ((hasDerivAt_id t).sub_const m).div_const h
  convert ((((hy.const_mul p.a).add ((hy.pow 2).const_mul p.b |>.div_const 2)).add
    ((hy.pow 3).const_mul p.c |>.div_const 3)).add
    ((hy.pow 4).const_mul p.d |>.div_const 4)).const_mul h using 1 <;>
    first | rfl | (simp only [Cubic.eval,id_eq]; norm_num; field_simp [hh])

theorem Cubic.integral (p : Cubic) (m h : ℝ) (hh : 0 < h) :
    (∫ t in (m-h)..(m+h), p.eval ((t-m)/h)) = 2*h*(p.a+p.c/3) := by
  have hc : Continuous (fun t => p.eval ((t-m)/h)) := by unfold Cubic.eval; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => p.primitive_deriv m h t hh.ne') (hc.intervalIntegrable _ _)]
  unfold Cubic.primitive
  field_simp
  ring

/-- Quantitative integral enclosure, applied later to the literal paidWeight endpoint mass. -/
theorem endpoint_model {m h : ℝ} {p : Cubic} {e : ℝ}
    (hh : 0 < h) (ha : 1 ≤ m-h) (hb : m+h ≤ 3)
    (hm : Model (fun x => kernel (m+h*x)) p e) :
    2*h*(p.a+p.c/3-e) ≤ endpointCellMass (m-h) (m+h) ∧
    endpointCellMass (m-h) (m+h) ≤ 2*h*(p.a+p.c/3+e) := by
  have hab : m-h ≤ m+h := by linarith
  have hi : IntervalIntegrable paidWeight volume (m-h) (m+h) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (paidWeight_continuousAt ⟨ha.trans ht.1,ht.2.trans hb⟩).continuousWithinAt
  have hc : Continuous (fun t => p.eval ((t-m)/h)) := by unfold Cubic.eval; fun_prop
  have hbound (t : ℝ) (ht : t ∈ Icc (m-h) (m+h)) :
      p.eval ((t-m)/h)-e ≤ paidWeight t ∧ paidWeight t ≤ p.eval ((t-m)/h)+e := by
    have hx : |(t-m)/h| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · apply (le_div_iff₀ hh).mpr
        linarith only [ht.1]
      · apply (div_le_iff₀ hh).mpr
        linarith only [ht.2]
    have he : m+h*((t-m)/h) = t := by field_simp; ring
    have ht' : t ∈ Icc 1 3 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    have hp := hm ((t-m)/h) hx
    dsimp only at hp
    rw [he,kernel_eq ht'] at hp
    obtain ⟨hl,hu⟩ := abs_le.mp hp
    constructor <;> linarith only [hl,hu]
  have hlo := intervalIntegral.integral_mono_on hab
    ((hc.sub continuous_const).intervalIntegrable _ _) hi (fun t ht => (hbound t ht).1)
  have hup := intervalIntegral.integral_mono_on hab hi
    ((hc.add continuous_const).intervalIntegrable _ _) (fun t ht => (hbound t ht).2)
  simp only [Pi.sub_apply,Pi.add_apply] at hlo hup
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    p.integral m h hh,intervalIntegral.integral_const,paidWeight_integral ha hab hb] at hlo
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const,
    p.integral m h hh,intervalIntegral.integral_const,paidWeight_integral ha hab hb] at hup
  simp only [smul_eq_mul] at hlo hup
  constructor <;> linarith only [hlo,hup]

end Hf4Quad
