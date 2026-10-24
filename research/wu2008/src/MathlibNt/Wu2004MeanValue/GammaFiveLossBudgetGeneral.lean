import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
/-!
# Parameterized scalar budgets for Gamma₅ loss

For the four original pairs (S, κ₂), the explicit one-fifth loss kernel has
strict weighted integral bounds 1/750, 1/500, 9/4000 and 1/1000. The proof
uses rational bounds on log x and the exact support, with no quadrature.

These are scalar certificates. The hypotheses on H are retained explicitly;
identities with each research row's actual gain must be established before
using these debits in the second-functional count inequalities.
-/

open Real Set MeasureTheory
open scoped Interval
namespace Wu2004MeanValue.GammaFiveLossBudget
noncomputable def generalKernel (S B v : ℝ) : ℝ :=
  if S*(1-2*B) ≤ v ∧ v ≤ S*(1-B)/2 then
    (1/(v*(1-v/S))) * log (B/(1-v/S-B)) / 5
  else if S*(1-B)/2 < v ∧ v < S/3 then
    (1/(v*(1-v/S))) * log ((S-2*v)/v) / 5
  else 0

/-- Uniform prefactor bound on the loss support. -/
theorem kernel_prefactor_bounds {S v : ℝ} (hS : 0 < S)
    (hv : (5/4 : ℝ) ≤ v) (he : v ≤ S/3) :
    0 ≤ 1/(v*(1-v/S)) ∧ 1/(v*(1-v/S)) ≤ 6/5 := by
  have hv0 : 0 < v := by linarith
  have hw : 2/3 ≤ 1-v/S := by
    have hh : v/S ≤ 1/3 := (div_le_iff₀ hS).mpr (by linarith)
    linarith
  have hd : 5/6 ≤ v*(1-v/S) := by
    nlinarith [mul_le_mul_of_nonneg_left hw hv0.le]
  exact ⟨by positivity, (div_le_iff₀ (by linarith)).mpr (by nlinarith)⟩

theorem generalKernel_upper {S B : ℝ} (hS : 0 < S) (hB : 1/3 ≤ B)
    (hBhi : B < 1/2) (hA : 5/4 ≤ S*(1-2*B)) (v : ℝ) :
    generalKernel S B v ≤ (6/25)*((3*B-1)/(1-B)) := by
  have hB0 : 0 < B := by linarith
  have hB1 : 0 < 1-B := by linarith
  have hL : 0 ≤ (3*B-1)/(1-B) := div_nonneg (by linarith) hB1.le
  have hmid : S*(1-2*B) ≤ S*(1-B)/2 := by nlinarith
  have hmidhi : S*(1-B)/2 ≤ S/3 := by nlinarith
  have logcap {x : ℝ} (hx : 0 < x) (hxu : x ≤ 2*B/(1-B)) :
      log x ≤ (3*B-1)/(1-B) := by
    have hlog := Real.log_le_sub_one_of_pos hx
    have heq : 2*B/(1-B)-1 = (3*B-1)/(1-B) := by field_simp; ring
    linarith
  unfold generalKernel
  split_ifs with h h
  · obtain ⟨hp0,hp⟩ := kernel_prefactor_bounds hS (hA.trans h.1) (h.2.trans hmidhi)
    have hvS : v/S ≤ (1-B)/2 := (div_le_iff₀ hS).mpr (by nlinarith [h.2])
    have hd : 0 < 1-v/S-B := by linarith
    have hr : B/(1-v/S-B) ≤ 2*B/(1-B) := by
      apply (div_le_div_iff₀ hd hB1).mpr
      nlinarith [mul_le_mul_of_nonneg_left hvS hB0.le]
    have hl := logcap (div_pos hB0 hd) hr
    have hm := mul_le_mul_of_nonneg_left hl hp0
    have hh := mul_le_mul_of_nonneg_right hp hL
    nlinarith
  · obtain ⟨hp0,hp⟩ := kernel_prefactor_bounds hS (hA.trans (hmid.trans h.1.le)) h.2.le
    have hv0 : 0 < v := by linarith [h.1]
    have hn : 0 < S-2*v := by linarith [h.2]
    have hr : (S-2*v)/v ≤ 2*B/(1-B) := by
      apply (div_le_div_iff₀ hv0 hB1).mpr
      nlinarith [h.1]
    have hl := logcap (div_pos hn hv0) hr
    have hm := mul_le_mul_of_nonneg_left hl hp0
    have hh := mul_le_mul_of_nonneg_right hp hL
    nlinarith
  · positivity
theorem generalKernel_support {S B : ℝ} (hS : 0 < S)
    (hB : 1/3 ≤ B) (hBhi : B < 1/2) :
    Function.support (generalKernel S B) ⊆ Ioc (S*(1-2*B)) (S/3) := by
  have hB0 : 0 < B := by linarith
  have hmid : S*(1-2*B) ≤ S*(1-B)/2 := by nlinarith
  have hmidhi : S*(1-B)/2 ≤ S/3 := by nlinarith
  intro v hv
  by_contra h
  apply hv
  by_cases he : v = S*(1-2*B)
  · subst v
    rw [generalKernel, if_pos ⟨le_rfl,hmid⟩]
    have heq : 1-S*(1-2*B)/S-B = B := by field_simp; ring
    rw [heq, div_self hB0.ne', log_one, mul_zero, zero_div]
  · have hn : ¬(S*(1-2*B) ≤ v ∧ v ≤ S*(1-B)/2) := by
      intro hh
      exact h ⟨lt_of_le_of_ne hh.1 (Ne.symm he), hh.2.trans hmidhi⟩
    have hn' : ¬(S*(1-B)/2 < v ∧ v < S/3) := by
      intro hh
      exact h ⟨hmid.trans_lt hh.1, hh.2.le⟩
    simp only [generalKernel, if_neg hn, if_neg hn']

/-- One-fifth loss budget as an explicit rational function of the row parameters. -/
theorem general_weighted_integral_bound {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (hE : S/3 ≤ 3)
    (H : ℝ → ℝ) (hH : ∀ v ∈ Icc (S*(1-2*B)) (S/3), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * generalKernel S B v)
      volume (S*(1-2*B)) (S/3)) :
    (∫ v in (1 : ℝ)..3, H v * generalKernel S B v) ≤
      (6/25)*((3*B-1)/(1-B))*(S/3-S*(1-2*B)) := by
  have hab : S*(1-2*B) ≤ S/3 := by nlinarith
  have hcap : 0 ≤ (6/25 : ℝ)*((3*B-1)/(1-B)) :=
    mul_nonneg (by norm_num) (div_nonneg (by linarith) (by linarith))
  have hs : Function.support (fun v => H v * generalKernel S B v) ⊆
      Ioc (S*(1-2*B)) (S/3) := by
    intro v hv
    apply generalKernel_support hS hB hBhi
    intro he
    exact hv (by simp [he])
  have hs' : Function.support (fun v => H v * generalKernel S B v) ⊆ Ioc (1 : ℝ) 3 := by
    intro v hv
    obtain ⟨hl,hu⟩ := hs hv
    exact ⟨by linarith,hu.trans hE⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs',
    ← intervalIntegral.integral_eq_integral_of_support_subset hs]
  have hb : (∫ v in (S*(1-2*B))..(S/3), H v * generalKernel S B v) ≤
      ∫ _v in (S*(1-2*B))..(S/3), (6/25 : ℝ)*((3*B-1)/(1-B)) := by
    apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    intro v hv
    exact (mul_le_mul_of_nonneg_left (generalKernel_upper hS hB hBhi hA v)
      (hH v hv).1).trans
      (by nlinarith [(hH v hv).2])
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hb

/-- Original four rows, recording S and the reciprocal of κ₂. -/
noncomputable def rowParameters : Fin 4 → ℝ × ℝ :=
  ![(227/50,10/29),(9/2,25/72),(223/50,100/287),(103/25,100/291)]

/-- Strict one-fifth debits, chosen above their exact rational upper bounds. -/
noncomputable def rowDebit : Fin 4 → ℝ := ![1/750,1/500,9/4000,1/1000]

theorem original_row_budget (i : Fin 4) (H : ℝ → ℝ)
    (hH : ∀ v ∈ Icc ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * generalKernel (rowParameters i).1
      (rowParameters i).2 v) volume ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3)) :
    (∫ v in (1 : ℝ)..3, H v * generalKernel (rowParameters i).1
      (rowParameters i).2 v) < rowDebit i := by
  have hp : 0 < (rowParameters i).1 ∧ 1/3 ≤ (rowParameters i).2 ∧
      (rowParameters i).2 < 1/2 ∧ 5/4 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) ∧
      (rowParameters i).1/3 ≤ 3 := by
    fin_cases i <;> norm_num [rowParameters]
  have h := general_weighted_integral_bound hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2 H hH hi
  apply h.trans_lt
  fin_cases i <;> norm_num [rowParameters,rowDebit]

end Wu2004MeanValue.GammaFiveLossBudget
