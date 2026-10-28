import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaSW
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanFirstGCD

/-!
# High-omega preprocessing at the original C.2 entry

The high-omega part of the original beta is cleaned before its progression
estimate; its divisor part, including `m*n=a`, is paid separately. Only then
is dispersion reapplied to the low-omega SW family. The resulting signed W
has an explicit restriction on both beta indices, with the same original
modulus coefficients and the same constructed frequency cutoff.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem betaClean_lowOmega_comm (β : ℕ → ℝ) (a : ℤ) (ξ : ℝ) :
    betaClean (betaLowOmega β ξ) a = betaLowOmega (betaClean β a) ξ := by
  funext n
  simp only [betaClean, betaLowOmega]
  split_ifs <;> rfl

theorem betaClean_highOmega_comm (β : ℕ → ℝ) (a : ℤ) (ξ : ℝ) :
    betaClean (betaHighOmega β ξ) a = betaHighOmega (betaClean β a) ξ := by
  funext n
  simp only [betaClean, betaHighOmega]
  split_ifs <;> rfl


/-- A genuine restriction of the tuple domain, retaining all compatibility
and Fourier factors. This identity does not assert any WF closure. -/
theorem wMaskedTruncated_betaLowOmega
    (M ξ : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    wMaskedTruncated M H N Q (betaLowOmega β ξ) c a P =
      wMaskedTruncated M H N Q β c a (fun t =>
        P t ∧ (t.2.1.primeFactors.card : ℝ) ≤ ξ ∧
          (t.2.2.primeFactors.card : ℝ) ≤ ξ) := by
  simp only [wMaskedTruncated, wMaskedTuples, sum_filter]
  apply sum_congr rfl
  intro t _
  by_cases hP : P t <;>
    by_cases h₁ : (t.2.1.primeFactors.card : ℝ) ≤ ξ <;>
    by_cases h₂ : (t.2.2.primeFactors.card : ℝ) ≤ ξ <;>
    simp [hP, h₁, h₂, wOriginalTerm, betaLowOmega]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
