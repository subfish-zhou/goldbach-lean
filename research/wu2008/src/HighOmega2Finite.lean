import HighOmega2Theta

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

theorem cell_as_window (N j : ℕ) (q Δ t : ℝ) (hΔ : 0 < Δ) :
    cell N q Δ t j = primeWindow N (reboxingAlpha q Δ t (j+1)/Δ) (reboxingAlpha q Δ t (j+1)) := by
  simp only [cell,reboxingAlpha_step hΔ,mul_div_cancel_right₀ _ hΔ.ne']



/-- Actual AP errors are additive over the original disjoint source cells;
this is a single large prime convolution error, not r fixed error budgets. -/
theorem ap_grid_exact {N Q r : ℕ} {q Δ t : ℝ} {i : ℕ}
    (W : Fin i → Finset ℕ) (hq : 0 < q) (hΔ : 1 < Δ) :
    (∑ j ∈ range r, convolutionAPError N Q (Fin.cons (cell N q Δ t j) W)) =
      convolutionAPError N Q (Fin.cons (primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)) W) := by
  let F : ℕ → ℝ := fun d =>
    ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
      |AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.primeAPError N (d * q) N|
  have expand (P : Finset ℕ) : convolutionAPError N Q (Fin.cons P W) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ P, F (d * p) := by
    rw [convolutionAPError_eq_support_sum]
    exact boxConvolution_sum_cons P W F
  simp_rw [expand]
  exact (reboxingAlpha_convolution_sum_partition hq hΔ N r W (fun d p => F (d*p))).symm


end
end HighOmega2
