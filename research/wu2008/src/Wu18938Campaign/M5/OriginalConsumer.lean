import Wu18938Campaign.M5.OriginalAnalytic
import Wu18938Campaign.M5.LiteralIdentity
import Wu18938Campaign.M5.TruncationConsumer

noncomputable section

namespace Wu18938Campaign.M5.OriginalConsumer

open Real Set MeasureTheory Filter Wu2008DoubleSieve
open WuPaper.R2SixthCount
open Wu18938Campaign.M5.StrictCorner Wu18938Campaign.M5.KernelCorner
open Wu18938Campaign.M5.OriginalAnalytic
open scoped Topology

theorem mass_congr_on_envelope {f g : ℝ × ℝ → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hfg : EqOn f g originalEnvelope) :
    originalMass f η = originalMass g η := by
  have ha : mass f (100 / 1327) (25 / 206) (25 / 206)
      (1 / 2 - 2 * (25 / 206) - η) =
      mass g (100 / 1327) (25 / 206) (25 / 206)
        (1 / 2 - 2 * (25 / 206) - η) := by
    apply setIntegral_congr_fun (rectangle_measurable _ _ _ _)
    intro z hz
    exact hfg ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hb : mass f (100 / 1327) (3 * (100 / 1327) / 2)
      (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η) =
      mass g (100 / 1327) (3 * (100 / 1327) / 2)
        (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η) := by
    apply setIntegral_congr_fun (rectangle_measurable _ _ _ _)
    intro z hz
    exact hfg ⟨⟨hz.1.1, by linarith [hz.1.2]⟩,
      (by norm_num : (25 / 206 : ℝ) ≤ 1 / 2 - 2 * (25 / 206)).trans hz.2.1,
      by linarith [hz.2.2]⟩
  simp only [originalMass, ha, hb]

theorem mass_actual_coefficient {δ ρ η : ℝ}
    (hρ : 0 ≤ ρ) (hρhi : ρ ≤ 1 / 100) (hη : 0 ≤ η) :
    originalMass (kernel ρ (coefficient δ)) η =
      originalMass (kernel ρ (fun s => wuLowerCoefficient s +
        wuImprovementLimit false δ s)) η := by
  apply mass_congr_on_envelope hη
  intro z hz
  unfold kernel
  rw [coefficient_eq (envelope_parameter hρ hρhi hz)]

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
  obtain ⟨n0, hn0⟩ := TruncationConsumer.original_uniform_count_truncation hε
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨hp, hphi, _, ht⟩ := hn0 n hn
  refine ⟨hp, hphi, fun N hN => original_trimmed_count hN hp.le, ?_⟩
  intro δ hδ hδhi
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

end Wu18938Campaign.M5.OriginalConsumer
