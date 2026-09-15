import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13QhatMajorantClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1056UniformStationary

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Section10Lemma1028FirstCrossing
open Section13QhatMajorantClosure
open Section10Equation1056UniformStationary

noncomputable def explicitLemma1027AdjointPlus (s : ℝ) : ℝ :=
  s ^ 2 - 2 * s + 1 / 2

lemma explicitLemma1027AdjointPlus_pos {s : ℝ} (hs : 2 ≤ s) :
    0 < explicitLemma1027AdjointPlus s := by
  dsimp [explicitLemma1027AdjointPlus]
  nlinarith [sq_nonneg (s - 1)]

/-- Lemma 10.27, internalized from the positive DDE solution, the explicit
quadratic adjoint, and pairing zero. -/
noncomputable def lemma1027AdjointRComparison_of_firstCrossingDDEApparatus
    {R : ℝ → ℝ} (h : FirstCrossingDDEApparatus R 3)
    (hadj : h.adjoint = explicitLemma1027AdjointPlus) :
    Lemma1027AdjointRComparison R := by
  refine
    { K := 2
      cutoff := 5
      K_nonneg := by norm_num
      comparison := ?_ }
  intro s hs
  have hs0 : 0 < s := by linarith
  have hsm1 : 3 < s - 1 := by linarith
  have hab : s - 1 ≤ s := by linarith
  have hRanti : AntitoneOn R (Icc (s - 1) s) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (s - 1) s)
    · exact h.continuous.mono (by
        intro u hu
        norm_num at hu ⊢
        linarith [hu.1])
    · intro u hu
      rw [interior_Icc] at hu
      exact (h.original_dde u (by linarith [hu.1])).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hRu : 0 < R u := h.positive u (by linarith [hu.1])
      have hRum : 0 < R (u - 1) := h.positive (u - 1) (by linarith [hu.1])
      have hnum : 0 < 2 * R u + R (u - 1) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum.le) hu0.le
  have hqcont : Continuous explicitLemma1027AdjointPlus := by
    unfold explicitLemma1027AdjointPlus
    fun_prop
  have hRcont : ContinuousOn R (Icc (s - 1) s) :=
    h.continuous.mono (by
      intro u hu
      norm_num at hu ⊢
      linarith [hu.1])
  have hint : IntervalIntegrable
      (fun t => explicitLemma1027AdjointPlus (t + 1) * R t)
      volume (s - 1) s := by
    apply ContinuousOn.intervalIntegrable_of_Icc (hab)
    exact (hqcont.comp (continuous_id.add continuous_const)).continuousOn.mul hRcont
  have hconstInt : IntervalIntegrable
      (fun _t : ℝ => explicitLemma1027AdjointPlus (s + 1) * R (s - 1))
      volume (s - 1) s := intervalIntegrable_const
  have hpairBound :
      s * explicitLemma1027AdjointPlus s * R s ≤
        explicitLemma1027AdjointPlus (s + 1) * R (s - 1) := by
    have hp := h.pairing_zero s (by linarith)
    rw [hadj] at hp
    rw [hp]
    calc
      (∫ t in s - 1..s, explicitLemma1027AdjointPlus (t + 1) * R t) ≤
          ∫ _t in s - 1..s,
            explicitLemma1027AdjointPlus (s + 1) * R (s - 1) := by
        apply intervalIntegral.integral_mono_on hab hint hconstInt
        intro t ht
        have htI : t ∈ Icc (s - 1) s := ht
        have hRt : R t ≤ R (s - 1) :=
          hRanti ⟨le_rfl, hab⟩ htI htI.1
        have hqt : explicitLemma1027AdjointPlus (t + 1) ≤
            explicitLemma1027AdjointPlus (s + 1) := by
          dsimp [explicitLemma1027AdjointPlus]
          nlinarith [htI.1, htI.2]
        have hqt0 : 0 ≤ explicitLemma1027AdjointPlus (t + 1) :=
          (explicitLemma1027AdjointPlus_pos (by linarith [htI.1])).le
        have hqnext0 : 0 ≤ explicitLemma1027AdjointPlus (s + 1) :=
          (explicitLemma1027AdjointPlus_pos (by linarith)).le
        exact mul_le_mul hqt hRt (h.positive t (by linarith [htI.1])).le hqnext0
      _ = explicitLemma1027AdjointPlus (s + 1) * R (s - 1) := by
        simp
  have hqnext : 0 < explicitLemma1027AdjointPlus (s + 1) :=
    explicitLemma1027AdjointPlus_pos (by linarith)
  have hRs : 0 < R s := h.positive s (by linarith)
  have hfactor :
      (1 - 2 / s) * explicitLemma1027AdjointPlus (s + 1) ≤
        explicitLemma1027AdjointPlus s := by
    dsimp [explicitLemma1027AdjointPlus]
    field_simp [ne_of_gt hs0]
    nlinarith
  apply le_of_mul_le_mul_left ?_ hqnext
  calc
    explicitLemma1027AdjointPlus (s + 1) * ((1 - 2 / s) * (s * R s)) =
        ((1 - 2 / s) * explicitLemma1027AdjointPlus (s + 1)) * (s * R s) := by ring
    _ ≤ explicitLemma1027AdjointPlus s * (s * R s) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hs0.le hRs.le)
    _ = s * explicitLemma1027AdjointPlus s * R s := by ring
    _ ≤ explicitLemma1027AdjointPlus (s + 1) * R (s - 1) := hpairBound

/-- Section 13 specialization: `Qhat` satisfies the adjacent comparison without
assuming that comparison in its source contract or first-crossing apparatus. -/
noncomputable def section13Qhat_lemma1027AdjointRComparison
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Lemma1027AdjointRComparison (section13Qhat H) := by
  apply lemma1027AdjointRComparison_of_firstCrossingDDEApparatus
    (section13QhatFirstCrossingData hH)
  rfl


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
