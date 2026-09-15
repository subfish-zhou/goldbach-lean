import Wu18938Campaign.M5.OriginalAnalytic
import Wu18938Campaign.M5.LeafIdentity
import Wu18938Campaign.M5.TruncationConsumer

noncomputable section

namespace Wu18938Campaign.M5.LeafConsumer

open Real Set MeasureTheory Wu2008DoubleSieve
open Wu18938Campaign.M5.StrictCorner Wu18938Campaign.M5.KernelCorner
open Wu18938Campaign.M5.OriginalAnalytic
open scoped Classical

theorem actual_ah_count_truncation {ε : ℝ} (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      0 < LiteralCount.width n ∧ LiteralCount.width n ≤ 1 / 100 ∧
      (∀ N : ℕ, 1 ≤ N →
        (∑ q ∈ primeWindow N ((N : ℝ) ^ (25 / 206 : ℝ))
            ((N : ℝ) ^ (1 / 2 - 2 * (25 / 206) - LiteralCount.width n)),
          ∑ p ∈ primeWindow N ((N : ℝ) ^ (100 / 1327 : ℝ))
              ((N : ℝ) ^ (25 / 206 : ℝ)),
            sourceSieveCountLE N (p * q) N ((N : ℝ) ^ (100 / 1327 : ℝ))) +
        (∑ q ∈ primeWindow N ((N : ℝ) ^ (1 / 2 - 2 * (25 / 206) : ℝ))
            ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327) - LiteralCount.width n)),
          ∑ p ∈ primeWindow N ((N : ℝ) ^ (100 / 1327 : ℝ))
              ((N : ℝ) ^ (3 * (100 / 1327) / 2 : ℝ)),
            sourceSieveCountLE N (p * q) N ((N : ℝ) ^ (100 / 1327 : ℝ))) ≤
        ∑ q ∈ primeWindow N ((N : ℝ) ^ (25 / 206 : ℝ))
            ((N : ℝ) ^ (1 / 2 - 3 * (100 / 1327) : ℝ)),
          ∑ p ∈ primeWindow N ((N : ℝ) ^ (100 / 1327 : ℝ))
              ((N : ℝ) ^ (25 / 206 : ℝ)),
            sourceSieveCountLE N (p * q) N ((N : ℝ) ^ (100 / 1327 : ℝ))) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ min (LiteralCount.width n) (1 / 100) →
        2 * (25 / 206 : ℝ) + (1 / 2 - 2 * (25 / 206) - LiteralCount.width n) < 1 / 2 ∧
        2 * (3 * (100 / 1327 : ℝ) / 2) +
          (1 / 2 - 3 * (100 / 1327) - LiteralCount.width n) < 1 / 2 ∧
        2 * (25 / 206 : ℝ) +
          (1 / 2 - 2 * (25 / 206) - LiteralCount.width n) ≤ 1 / 2 - δ ∧
        2 * (3 * (100 / 1327 : ℝ) / 2) +
          (1 / 2 - 3 * (100 / 1327) - LiteralCount.width n) ≤ 1 / 2 - δ ∧
        ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ min (LiteralCount.width n) (1 / 100) →
          |originalMass (kernel ρ (fun s => wuLowerCoefficient s +
              wuImprovementLimit false δ s)) 0 -
            originalMass (kernel ρ (fun s => wuLowerCoefficient s +
              wuImprovementLimit false δ s)) (LiteralCount.width n)| < ε := by
  obtain ⟨n0, hn0⟩ := TruncationConsumer.original_uniform_count_truncation hε
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨hp, hphi, hc, ht⟩ := hn0 n hn
  refine ⟨hp, hphi, ?_, ?_⟩
  · intro N hN
    simpa only [LiteralCount.countA, LiteralCount.countB, LiteralCount.upsilon6,
      LeafIdentity.pairCount_eq] using hc N hN
  · intro δ hδ hδhi
    have hδ100 := (le_min_iff.mp hδhi).2
    obtain ⟨ha, hb, hda, hdb, _⟩ := ht δ hδ.le hδhi
    refine ⟨ha, hb, hda, hdb, ?_⟩
    intro ρ hρ hρhi
    have hρ100 := (le_min_iff.mp hρhi).2
    have h := (ht ρ hρ hρhi).2.2.2.2 (coefficient δ)
      (coefficient_measurable hδ (by linarith))
      (coefficient_bound hδ (by linarith))
    rwa [mass_actual_coefficient hρ hρ100 (le_refl 0),
      mass_actual_coefficient hρ hρ100 hp.le] at h

end Wu18938Campaign.M5.LeafConsumer
