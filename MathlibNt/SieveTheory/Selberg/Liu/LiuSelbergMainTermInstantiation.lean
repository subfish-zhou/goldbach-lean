import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairTransfer
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorAsymptotic

/-!
# Liu's genuine-li Selberg main-term instantiation

This module combines the proved reciprocal-log transfer and optimized Selberg
coefficient with the finite component-bound theorem.  The source-facing result
retains the evenness and nonempty-cutoff implications required by the optimized
weight construction.
-/

open Filter

namespace MathlibNt.SieveTheory.LiuWeight

/-- Unconditional eventual form of Liu's genuine logarithmic-integral
weight-sum estimate. -/
theorem eventually_liuGenuineLiWeightMainSumBound
    (kappa : ℝ) (hκ : 0 ≤ kappa) (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuGenuineLiWeightMainSumBound kappa (0.49254 + eta) N := by
  obtain ⟨N₁, hN₁⟩ := eventually_liuSourceReciprocalLogBound
  obtain ⟨N₂, hN₂⟩ :=
    eventually_liuGenuineLiWeightMainSumBound_of_source kappa hκ eta heta
  refine ⟨max N₁ N₂, fun N hN => hN₂ N ?_ (hN₁ N ?_)⟩
  · exact (le_max_right N₁ N₂).trans hN
  · exact (le_max_left N₁ N₂).trans hN

/-- Exact coefficient error used in the assembled `M₁` estimate. -/
noncomputable def liuM1Delta : ℝ := 1 / 10000000

/-- Exact genuine-logarithmic-integral error used in the assembled `M₁`
estimate. -/
noncomputable def liuM1Eta : ℝ := 1 / 10000000

lemma liuM1Delta_pos : 0 < liuM1Delta := by
  norm_num [liuM1Delta]

lemma liuM1Eta_pos : 0 < liuM1Eta := by
  norm_num [liuM1Eta]

lemma liuM1DeltaEta_margin :
    8 * liuM1Eta + 0.49254 * liuM1Delta + liuM1Delta * liuM1Eta ≤ 0.00001 := by
  norm_num [liuM1Delta, liuM1Eta]


end MathlibNt.SieveTheory.LiuWeight
