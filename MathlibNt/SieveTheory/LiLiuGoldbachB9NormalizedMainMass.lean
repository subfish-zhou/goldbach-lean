import MathlibNt.SieveTheory.LiLiuGoldbachB9CommonRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachB8NormalizedMainMass
import MathlibNt.SieveTheory.LiLiuGoldbachS5CountTransport


open Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Reuse the public scalar geometry, without imposing the B8 carrier window on B9. -/
theorem goldbachB9Plus_normalized_cutoff_geometry
    (B K τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Real.sqrt Δ
      max 2 K ≤ Z ∧ Z ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
        Z ≤ Real.sqrt (N : ℝ) ∧ Real.log Δ / Real.log Z = 2 ∧
        0 < Real.log Z ∧ Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
  obtain ⟨N₀, hN₀, hg⟩ := goldbachB8Plus_normalized_cutoff_geometry B K τ hB hτ hτ1
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨hlarge, hquarter, _hB8, hsqrt, hs, hlog, hratio⟩ := hg N hN
  exact ⟨hlarge, hquarter, hsqrt, hs, hlog, hratio⟩


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig