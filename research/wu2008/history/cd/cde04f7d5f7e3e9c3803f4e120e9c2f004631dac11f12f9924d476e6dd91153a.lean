import MathlibNt.Wu2008DoubleSieve.OmegaTerms
import MathlibNt.Wu2008DoubleSieve.ImprovementThresholdIntegrals

/-!
# The actual Omega1 upper estimate, Wu04 (5.1)

The literal count aggregate is twice Phi(t). The upper improvement is
the attained supremum for this same N0, not an assumed sieve estimate.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem wuOmega1Sum_eq_twice_Phi {i : ℕ} (N : ℕ) (δ t : ℝ)
    (W : Fin i → Finset ℕ) :
    wuOmega1Sum N δ t W = 2 * wuBoxPhi N δ W t := by
  unfold wuOmega1Sum wuOmega1 wuBoxPhi convolutionSieveCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem wu04_51 (k : ℕ) (hk : 1 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ t : ℝ, 1 ≤ t → t ≤ 10 →
        wuOmega1Sum N δ t (convolutionWuWindows N Δ V) ≤
          2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (wuImprovementAt_uniform_eventually_attained true k hk hδ hδhi)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N0 hN0 N hN he i Δ V hb t ht ht10
  have hcmp := (hT N0 ((le_max_right _ _).trans hN0) t ht ht10).2.1
    N hN ((le_max_left _ _).trans (hN0.trans hN)) he i Δ V hb
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) t ≤
    (wuUpperCoefficient t - wuImprovementAt true k δ t N0) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) at hcmp
  rw [wuOmega1Sum_eq_twice_Phi, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcmp (by norm_num)

end Wu2008DoubleSieve
