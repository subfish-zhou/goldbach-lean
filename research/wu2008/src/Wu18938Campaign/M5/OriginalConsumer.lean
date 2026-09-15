import Wu18938Campaign.M5.OriginalAnalytic
import Wu18938Campaign.M5.LiteralIdentity
import Wu18938Campaign.M5.LeafConsumer

noncomputable section

namespace Wu18938Campaign.M5.OriginalConsumer

open Real Set MeasureTheory Filter Wu2008DoubleSieve
open WuPaper.R2SixthCount
open Wu18938Campaign.M5.StrictCorner Wu18938Campaign.M5.KernelCorner
open Wu18938Campaign.M5.OriginalAnalytic
open scoped Topology

theorem original_trimmed_count {N : ℕ} {η : ℝ} (hN : 1 ≤ N) (hη : 0 ≤ η) :
    rectangleCount N alpha beta beta (aCeiling - η) +
      rectangleCount N alpha bCut aCeiling (sigma - η) ≤ upsilon6 N := by
  have h := LiteralCount.original_trimmed_le hN hη
  rw [LiteralIdentity.upsilon6_eq] at h
  change rectangleCount N alpha beta beta (aCeiling - η) +
    rectangleCount N alpha bCut aCeiling (sigma - η) ≤ upsilon6 N at h
  exact h

theorem original_ah_count_truncation {ε : ℝ} (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      0 < LiteralCount.width n ∧ LiteralCount.width n ≤ 1 / 100 ∧
      (∀ N : ℕ, 1 ≤ N →
        rectangleCount N alpha beta beta (aCeiling - LiteralCount.width n) +
          rectangleCount N alpha bCut aCeiling (sigma - LiteralCount.width n) ≤ upsilon6 N) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ min (LiteralCount.width n) (1 / 100) →
        2 * beta + (aCeiling - LiteralCount.width n) < (1 / 2 : ℝ) ∧
        2 * bCut + (sigma - LiteralCount.width n) < (1 / 2 : ℝ) ∧
        2 * beta + (aCeiling - LiteralCount.width n) ≤ (1 / 2 : ℝ) - δ ∧
        2 * bCut + (sigma - LiteralCount.width n) ≤ (1 / 2 : ℝ) - δ ∧
        ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ min (LiteralCount.width n) (1 / 100) →
          |originalMass (kernel ρ (fun s => wuLowerCoefficient s +
              wuImprovementLimit false δ s)) 0 -
            originalMass (kernel ρ (fun s => wuLowerCoefficient s +
              wuImprovementLimit false δ s)) (LiteralCount.width n)| < ε := by
  exact LeafConsumer.actual_ah_count_truncation hε

end Wu18938Campaign.M5.OriginalConsumer
