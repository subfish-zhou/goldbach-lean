import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition1023Phase

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- On the window `[s-1,s]`, the explicit positive adjoint has weight at least
its current weight.  This is the order input that turns pairing-zero into the
local premise of Suzuki's Lemma 10.22. -/
lemma section13AdjointPlus_window_lower
    {s t : ℝ} (hs : 4 ≤ s) (ht : t ∈ Icc (s - 1) s) :
    section13AdjointPlus s ≤ section13AdjointPlus (t + 1) := by
  dsimp [section13AdjointPlus]
  have hprod : 0 ≤ (t - (s - 1)) * (t + (s - 1)) :=
    mul_nonneg (by linarith [ht.1]) (by linarith [ht.1, hs])
  nlinarith

/-- The Lemma-10.22 local lower inequality is a theorem of `Qhat`, not an
extra premise.  Pairing-zero says that the adjoint-weighted window integral is
`s q(s) Qhat(s)`; positivity of `Qhat` and monotonicity of the explicit
quadratic adjoint remove the weight. -/
theorem section13Qhat_lemma1022_local_premise
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∀ᶠ s : ℝ in atTop,
      (s + 1) * section13Qhat H s ≥
        ∫ t in s - 1..s, section13Qhat H t := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with s hs
  have hab : s - 1 ≤ s := by linarith
  have hqpos : 0 < section13AdjointPlus s := by
    dsimp [section13AdjointPlus]
    nlinarith [sq_nonneg (s - 1)]
  have hQcont : ContinuousOn (section13Qhat H) (Icc (s - 1) s) :=
    (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
      intro t ht
      exact (by linarith [ht.1] : 0 < t))
  have hleftInt : IntervalIntegrable
      (fun t => section13AdjointPlus s * section13Qhat H t) volume (s - 1) s :=
    by
      have hc : ContinuousOn
          (fun t : ℝ => section13AdjointPlus s * section13Qhat H t)
          (Icc (s - 1) s) :=
        (continuousOn_const : ContinuousOn
          (fun _t : ℝ => section13AdjointPlus s) (Icc (s - 1) s)).mul hQcont
      rw [← uIcc_of_le hab] at hc
      exact hc.intervalIntegrable
  have hrightInt : IntervalIntegrable
      (fun t => section13AdjointPlus (t + 1) * section13Qhat H t) volume (s - 1) s := by
    have hqcont : ContinuousOn (fun t : ℝ => section13AdjointPlus (t + 1))
        (Icc (s - 1) s) :=
      ((continuous_id.add continuous_const).pow 2 |>.sub
        (continuous_const.mul (continuous_id.add continuous_const)) |>.add
        continuous_const).continuousOn
    have hc := hqcont.mul hQcont
    rw [← uIcc_of_le hab] at hc
    exact hc.intervalIntegrable
  have hweighted :
      section13AdjointPlus s *
          (∫ t in s - 1..s, section13Qhat H t) ≤
        ∫ t in s - 1..s,
          section13AdjointPlus (t + 1) * section13Qhat H t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hleftInt hrightInt
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (section13AdjointPlus_window_lower hs ht)
      (section13Qhat_pos hH.toSection13HatContract (by linarith [ht.1])).le
  have hpair := section13Qhat_pairing_zero hH (by linarith : 3 < s)
  simp only [section10SignedPairing, one_mul, sub_eq_zero] at hpair
  have hsQ :
      (∫ t in s - 1..s, section13Qhat H t) ≤ s * section13Qhat H s := by
    apply (mul_le_mul_iff_of_pos_left hqpos).mp
    calc
      section13AdjointPlus s *
          (∫ t in s - 1..s, section13Qhat H t) ≤
          ∫ t in s - 1..s,
            section13AdjointPlus (t + 1) * section13Qhat H t := hweighted
      _ = section13AdjointPlus s * (s * section13Qhat H s) := by
        rw [← hpair]
        ring
  have hQpos := section13Qhat_pos hH.toSection13HatContract (by linarith : 0 < s)
  nlinarith


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
