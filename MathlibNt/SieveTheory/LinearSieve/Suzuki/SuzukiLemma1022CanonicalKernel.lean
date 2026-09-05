import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition1023Phase
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1022DownwardCrossingCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1022

set_option autoImplicit false
set_option maxHeartbeats 800000

open Section10CanonicalXi

/-- The conjugated one-step kernel in (10.37). -/
noncomputable def lowerKernel (b E c s : ℝ) : ℝ :=
  b / (s + E) *
    ∫ t in s - 1..s, Real.exp (lowerPhase b c s - lowerPhase b c t)

/-- The canonical analytic input required by the downward-crossing core. -/
def CanonicalKernelGrowth (b E : ℝ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ s in atTop,
    0 < s + E ∧ 1 < lowerKernel b E c s

/-- Concavity of `log`, in the endpoint form used in (10.34)--(10.36). -/
lemma log_sub_log_ge_endpoint_slope {t s : ℝ}
    (ht : 0 < t + Real.exp 1) (hts : t ≤ s) :
    (s - t) / (s + Real.exp 1) ≤
      Real.log (s + Real.exp 1) - Real.log (t + Real.exp 1) := by
  have hs : 0 < s + Real.exp 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs)] at h
  have hratio :
      (t + Real.exp 1) / (s + Real.exp 1) - 1 =
        -((s - t) / (s + Real.exp 1)) := by
    field_simp [ne_of_gt hs]
    ring
  rw [hratio] at h
  linarith

/-- Exact elementary integral underlying the passage from (10.36) to (10.37). -/
lemma integral_exp_endpoint (A s : ℝ) (hA : A ≠ 0) :
    (∫ t in s - 1..s, Real.exp (A * (s - t))) =
      (Real.exp A - 1) / A := by
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => Real.exp (A * u)) s]
  have hderiv : ∀ u ∈ uIcc (s - s) (s - (s - 1)),
      HasDerivAt (fun v : ℝ => Real.exp (A * v) / A)
        (Real.exp (A * u)) u := by
    intro u _
    apply (((hasDerivAt_const u A).mul (hasDerivAt_id u)).exp.div_const A).congr_deriv
    simp only [Pi.mul_apply, id_eq, zero_mul, zero_add]
    field_simp [hA]
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (A * u)) volume
      (s - s) (s - (s - 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num
  field_simp [hA]

/-- Pointwise canonical phase increment.  This is the rigorous endpoint-slope
version of (10.34)--(10.36), with no phase-expansion premise. -/
lemma lowerPhase_increment_ge {c s t : ℝ}
    (hc : 0 ≤ c) (hs : Real.exp 1 + 2 ≤ s)
    (ht : t ∈ Icc (s - 1) s) :
    xi (s - 1) * (s - t) + c / (s + Real.exp 1) * (s - t) ≤
      lowerPhase 1 c s - lowerPhase 1 c t := by
  have htpos : 0 < t + Real.exp 1 := by
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    linarith [ht.1]
  have hlog := log_sub_log_ge_endpoint_slope htpos ht.2
  have hxiInt_t : IntervalIntegrable xi volume 1 t :=
    xi_continuous.intervalIntegrable 1 t
  have hxiInt_ts : IntervalIntegrable xi volume t s :=
    xi_continuous.intervalIntegrable t s
  have hadd := intervalIntegral.integral_add_adjacent_intervals hxiInt_t hxiInt_ts
  have hsplit :
      (∫ u in (1 : ℝ)..s, xi u) - (∫ u in (1 : ℝ)..t, xi u) =
        ∫ u in t..s, xi u := by linarith
  have hconstInt : IntervalIntegrable (fun _ : ℝ => xi (s - 1)) volume t s :=
    continuous_const.intervalIntegrable t s
  have hmono : (s - t) * xi (s - 1) ≤ ∫ u in t..s, xi u := by
    have hi := intervalIntegral.integral_mono_on ht.2 hconstInt hxiInt_ts (by
      intro u hu
      exact xi_monotone (le_trans ht.1 hu.1))
    simpa [intervalIntegral.integral_const, mul_comm] using hi
  simp only [lowerPhase, div_one]
  have hclog := mul_le_mul_of_nonneg_left hlog hc
  calc
    xi (s - 1) * (s - t) + c / (s + Real.exp 1) * (s - t)
        ≤ (∫ u in t..s, xi u) +
            c * (Real.log (s + Real.exp 1) - Real.log (t + Real.exp 1)) := by
              have hcoeff : c / (s + Real.exp 1) * (s - t) =
                  c * ((s - t) / (s + Real.exp 1)) := by ring
              rw [hcoeff]
              exact add_le_add (by simpa [mul_comm] using hmono) hclog
    _ = (∫ u in (1 : ℝ)..s, xi u) + c * Real.log (s + Real.exp 1) -
          ((∫ u in (1 : ℝ)..t, xi u) + c * Real.log (t + Real.exp 1)) := by
            rw [← hsplit]
            ring

/-- Direct formalization of the canonical-kernel growth in (10.34)--(10.38)
for `κ = b = 1`.  The constant is explicit and depends only on `E`; no kernel
growth or phase expansion is assumed. -/
theorem canonicalKernelGrowth_one {E : ℝ} (hE : 1 ≤ E) :
    CanonicalKernelGrowth 1 E := by
  let c : ℝ := 4 * (E + 2)
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    linarith
  filter_upwards [eventually_ge_atTop
      (max E (Real.exp 9 + Real.exp 1 + 2))] with s hs
  have hsE : E ≤ s := le_trans (le_max_left _ _) hs
  have hsbig : Real.exp 9 + Real.exp 1 + 2 ≤ s :=
    le_trans (le_max_right _ _) hs
  have hsbase : Real.exp 1 + 2 ≤ s := by
    have he9 : 0 < Real.exp 9 := Real.exp_pos 9
    linarith
  have hspos : 0 < s := by
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have hdenE : 0 < s + E := by linarith
  have hdene : 0 < s + Real.exp 1 := add_pos hspos (Real.exp_pos 1)
  have hcpos : 0 < c := by dsimp [c]; linarith
  let x : ℝ := xi (s - 1)
  let d : ℝ := c / (s + Real.exp 1)
  let A : ℝ := x + d
  have hsxm1 : Real.exp 9 ≤ s - 1 := by
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have hsxm1one : 1 < s - 1 := by
    have he9one : 1 < Real.exp 9 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hx9 : 9 < x := by
    dsimp [x]
    have hlog := log_lt_xi
      ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 9)).trans hsxm1)
    have hlog9 : 9 ≤ Real.log (s - 1) := by
      have hp : 0 < s - 1 := lt_of_lt_of_le (Real.exp_pos 9) hsxm1
      rw [← Real.exp_log hp] at hsxm1
      exact Real.exp_le_exp.mp hsxm1
    linarith
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hApos : 0 < A := by dsimp [A]; linarith
  have hratioLower : (1 / 2 : ℝ) ≤ (s - 1) / (s + Real.exp 1) := by
    apply (le_div_iff₀ hdene).2
    linarith [hsbase]
  have hdsm1 : 2 * (E + 2) ≤ d * (s - 1) := by
    have hm := mul_le_mul_of_nonneg_left hratioLower hcpos.le
    have heq : c * ((s - 1) / (s + Real.exp 1)) = d * (s - 1) := by
      dsimp [d]
      field_simp [ne_of_gt hdene]
    rw [heq] at hm
    dsimp [c] at hm
    linarith
  have hratioUpper : (s + E - 1) / (s + Real.exp 1) ≤ 2 := by
    apply (div_le_iff₀ hdene).2
    linarith [hsE, Real.exp_pos 1]
  have hdterm : d * (s + E - 1) ≤ 2 * c := by
    have hm := mul_le_mul_of_nonneg_left hratioUpper hcpos.le
    have heq : c * ((s + E - 1) / (s + Real.exp 1)) = d * (s + E - 1) := by
      dsimp [d]
      field_simp [ne_of_gt hdene]
    rw [heq] at hm
    simpa [mul_comm] using hm
  let q : ℝ := d * (s - 1) - (E + 1)
  have hq : E + 3 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := by linarith
  have hxq : 9 * (E + 3) < x * q := by
    have h1 := mul_lt_mul_of_pos_right hx9 hqpos
    have h2 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 9)
    nlinarith
  have hmain : (s + E) * A < (1 + d) * (1 + (s - 1) * x) - 1 := by
    have hgap : d * (s + E - 1) < x * q := by
      have hcval : 2 * c = 8 * (E + 2) := by dsimp [c]; ring
      rw [hcval] at hdterm
      nlinarith
    dsimp [A, q] at hgap ⊢
    nlinarith
  have hxEq : Real.exp x - 1 = (s - 1) * x := by
    dsimp [x]
    exact xi_equation hsxm1one
  have hexpLower : (1 + d) * Real.exp x ≤ Real.exp A := by
    have h := Real.add_one_le_exp d
    have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
    rw [mul_comm (Real.exp x), ← Real.exp_add] at hm
    simpa [A, add_comm] using hm
  have hnumerator : (s + E) * A < Real.exp A - 1 := by
    calc
      (s + E) * A < (1 + d) * (1 + (s - 1) * x) - 1 := hmain
      _ = (1 + d) * Real.exp x - 1 := by rw [← hxEq]; ring
      _ ≤ Real.exp A - 1 := by linarith
  have hquotient : s + E < (Real.exp A - 1) / A :=
    (lt_div_iff₀ hApos).2 (by simpa [mul_comm] using hnumerator)
  have hphaseInt :
      (Real.exp A - 1) / A ≤
        ∫ t in s - 1..s, Real.exp (lowerPhase 1 c s - lowerPhase 1 c t) := by
    rw [← integral_exp_endpoint A s (ne_of_gt hApos)]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
    · have hpcont : ContinuousOn (lowerPhase 1 c) (Icc (s - 1) s) :=
        (lowerPhase_continuousOn (show 0 ≤ s - 1 by linarith)).mono
          (by intro t ht; exact ht.1)
      have hpcontU : ContinuousOn (lowerPhase 1 c) (uIcc (s - 1) s) := by
        simpa [uIcc_of_le (by linarith : s - 1 ≤ s)] using hpcont
      have hdiff : ContinuousOn
          (fun u : ℝ => lowerPhase 1 c s - lowerPhase 1 c u)
          (uIcc (s - 1) s) :=
        continuousOn_const.sub hpcontU
      have hccomp : ContinuousOn
          (fun u : ℝ => Real.exp (lowerPhase 1 c s - lowerPhase 1 c u))
          (uIcc (s - 1) s) := by
        change ContinuousOn
          (Real.exp ∘ fun u : ℝ => lowerPhase 1 c s - lowerPhase 1 c u)
          (uIcc (s - 1) s)
        exact Real.continuous_exp.comp_continuousOn hdiff
      exact hccomp.intervalIntegrable
    · intro t ht
      apply Real.exp_le_exp.mpr
      have hinc := lowerPhase_increment_ge hcpos.le hsbase ht
      simpa [A, x, d, add_mul] using hinc
  have hintgt : s + E <
      ∫ t in s - 1..s, Real.exp (lowerPhase 1 c s - lowerPhase 1 c t) :=
    lt_of_lt_of_le hquotient hphaseInt
  refine ⟨hdenE, ?_⟩
  rw [lowerKernel]
  norm_num only [one_div]
  simpa [div_eq_inv_mul] using (one_lt_div hdenE).2 hintgt

end Section10Lemma1022
