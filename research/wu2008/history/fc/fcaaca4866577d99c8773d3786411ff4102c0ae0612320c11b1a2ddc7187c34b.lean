import CoupledJGainOrder
import Wu04BypassActual

noncomputable section
namespace WuTarget.W05
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment
open scoped Interval BigOperators

def jCoefficient (s S : ℝ) (k : Fin 9) : ℝ :=
  log (right (S - 2) 3 k / left (S - 2) 3 k) * log ((S - 1) / (s - 1)) +
    (CoupledJLogRecovery.fullPrimitive S (jStart s S)
      (right (jStart s S - 1) (S - 2) k) -
    CoupledJLogRecovery.fullPrimitive S (jStart s S)
      (left (jStart s S - 1) (S - 2) k))

theorem jCoefficient_basis (s S : ℝ) (k : Fin 9) :
    CoupledJLogRecovery.jRest (nodeBasis k) s S = jCoefficient s S k := by
  classical
  simp [CoupledJLogRecovery.jRest, tail, nodeBasis, jCoefficient]

theorem jRest_expansion (z : Fin 9 → ℝ) (s S : ℝ) :
    CoupledJLogRecovery.jRest z s S = ∑ k : Fin 9, jCoefficient s S k * z k := by
  unfold CoupledJLogRecovery.jRest tail jCoefficient
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem jCoefficient_paid {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) (k : Fin 9) :
    aProfile (nineProfile (nodeBasis k)) * log ((S - 1) / (s - 1)) +
      jCoefficient s S k ≤ profileJ (nodeBasis k) s S := by
  have h := CoupledJLogRecovery.jTerm_le (nodeBasis k) (nodeBasis_nonneg k)
    hs hS hS5 hsS hr
  simpa only [CoupledJLogRecovery.jTerm, jCoefficient_basis] using h

theorem jCoefficients_paid {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    aProfile (nineProfile z) * log ((S - 1) / (s - 1)) +
      ∑ k : Fin 9, jCoefficient s S k * z k ≤ profileJ z s S := by
  simpa only [CoupledJLogRecovery.jTerm, jRest_expansion] using
    CoupledJLogRecovery.jTerm_le z hz hs hS hS5 hsS hr

theorem jStart_bounds {s S : ℝ} (hs : 2 ≤ s) (hsS : s ≤ S)
    (hr : 2 ≤ S - S / s) : 2 ≤ jStart s S ∧ jStart s S ≤ S - 1 := by
  have h := (one_le_div (by linarith : 0 < s)).mpr hsS
  exact ⟨hr, by unfold jStart; linarith⟩

theorem j_domain_denominators {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S)
    (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    (∀ u ∈ Icc (1 - 1 / s) (1 - 1 / S),
      0 < u * (1 - u) ∧ 1 ≤ S * u - 1 ∧ S * u - 1 ≤ S - 2) ∧
    (∀ t ∈ Icc (jStart s S - 1) (S - 2),
      0 < t ∧ 0 < S - 1 - t ∧ 0 < S - jStart s S) := by
  have hA := jStart_bounds hs hsS hr
  constructor
  · intro u hu
    have h := (J_geometry hs hS hS5 hsS hr).2 u hu
    have he : S * (1 - 1 / S) = S - 1 := by
      have hS0 : S ≠ 0 := by linarith
      field_simp
    have hb := mul_le_mul_of_nonneg_left hu.2 (by linarith : 0 ≤ S)
    rw [he] at hb
    exact ⟨mul_pos h.1 (by linarith [h.2.1]), by linarith [h.2.2.1],
      by linarith⟩
  · intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2], by linarith [hA.2]⟩

theorem lowerLog_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ SharpLogRecurrence.lowerLog x := by
  have h := FirstFeedbackIntegrals.low_nonneg hx
  simpa only [SharpLogRecurrence.low, if_pos hx, Wu04FactorEnvelopes.lower] using h

theorem recoveryKernel_nonneg {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S - 1)
    (hu : u ∈ Icc (A - 1) (S - 2)) :
    0 ≤ CoupledJLogRecovery.kernel S A u := by
  have h1 : 1 ≤ (u + 1) / A :=
    (one_le_div (by linarith : 0 < A)).mpr (by linarith [hu.1])
  have h2 : 1 ≤ (S - A) / (S - 1 - u) :=
    (one_le_div (by linarith [hu.2] : 0 < S - 1 - u)).mpr (by linarith [hu.1])
  have hj : 0 ≤ jKernel S A u := by
    rw [jKernel_eq hA hAS hu]
    exact div_nonneg (add_nonneg (lowerLog_nonneg h1) (lowerLog_nonneg h2))
      (by linarith [hu.1])
  exact add_nonneg
    (add_nonneg hj (CoupledJLogRecovery.firstError_nonneg hA hu.1))
    (CoupledJLogRecovery.secondError_nonneg hA hAS hu)

theorem jCoefficient_nonneg {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S)
    (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S - S / s) (k : Fin 9) :
    0 ≤ jCoefficient s S k := by
  have hA := jStart_bounds hs hsS hr
  have hab : jStart s S - 1 ≤ S - 2 := by linarith [hA.2]
  have ht : S - 2 ≤ (3 : ℝ) := by linarith
  have hl : 0 < left (S - 2) 3 k := by
    have h := (clip_bounds (x := upperLeft k) ht).1
    change S - 2 ≤ left (S - 2) 3 k at h
    linarith
  have hlog := log_nonneg ((one_le_div hl).mpr (cell_order (S - 2) 3 k))
  have hw := log_nonneg ((one_le_div (by linarith : 0 < s - 1)).mpr
    (by linarith : s - 1 ≤ S - 1))
  unfold jCoefficient
  apply add_nonneg (mul_nonneg hlog hw)
  rw [← CoupledJLogRecovery.kernel_integral hA.1 hA.2
    (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2]
  apply intervalIntegral.integral_nonneg (cell_order _ _ k)
  intro u hu
  exact recoveryKernel_nonneg hA.1 hA.2
    ⟨(clip_bounds hab).1.trans hu.1, hu.2.trans (clip_bounds hab).2⟩

theorem first_coefficients_paid (i : Fin 5) (k : Fin 9) :
    aProfile (nineProfile (nodeBasis k)) * log ((firstS i - 1) / (firstNode i - 1)) +
      jCoefficient (firstNode i) (firstS i) k ≤
        profileJ (nodeBasis k) (firstNode i) (firstS i) := by
  have hg := first_geometry i
  exact jCoefficient_paid hg.1 hg.2.2.1 hg.2.2.2.1
    (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 k

theorem coupled_coefficients_paid (i : Fin 4) (k : Fin 9) :
    (aProfile (nineProfile (nodeBasis k)) *
        log (((coupledRow i).S - 1) / ((coupledRow i).s - 1)) +
      jCoefficient (coupledRow i).s (coupledRow i).S k ≤
        profileJ (nodeBasis k) (coupledRow i).s (coupledRow i).S) ∧
    (aProfile (nineProfile (nodeBasis k)) *
        log (((coupledRow i).S - 1) / ((coupledRow i).kappa2 - 1)) +
      jCoefficient (coupledRow i).kappa2 (coupledRow i).S k ≤
        profileJ (nodeBasis k) (coupledRow i).kappa2 (coupledRow i).S) ∧
    (aProfile (nineProfile (nodeBasis k)) *
        log (((coupledRow i).S - 1) / ((coupledRow i).kappa3 - 1)) +
      jCoefficient (coupledRow i).kappa3 (coupledRow i).S k ≤
        profileJ (nodeBasis k) (coupledRow i).kappa3 (coupledRow i).S) := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  exact ⟨jCoefficient_paid hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1 k,
    jCoefficient_paid hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.1 hp.2.2.2.1 k,
    jCoefficient_paid hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.2.2.1 hp.2.2.2.2 k⟩

theorem terminal_coefficient_zero (k : Fin 9) : jCoefficient 3 3 k = 0 := by
  simp [jCoefficient, jStart, left, right, clip]

end WuTarget.W05
