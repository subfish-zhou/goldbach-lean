import MathlibNt.SieveTheory.LiLiuGoldbachB10PanGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachB10PanTwoEndpoints

open scoped BigOperators
open Finset MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableB10PanDistribution (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Actual B10 divisor remainder at half level with a logarithmic loss.
All analytic and geometric inputs are supplied. The threshold is uniform in beta,
while epsilon and gamma are fixed before the threshold. The main term retains
its coprimality gate and the literal floor endpoint. -/
theorem goldbachB10PanPrefixRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ ε γ : ℝ,
      0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
        (1 : ℝ) / 18 < β →
        ∑ d ∈ (Icc 1 (panModulusCutoff N (B + 1))).filter (fun d => Nat.Coprime d N),
          |goldbachB10PanPrefixRemainder N d (liuPanSourceIntervalLower N B)
            (B10PanGeometryUpperWindow N γ) ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, K, htwo⟩ :=
    goldbachB10PanPrefixRemainder_floor_twoEndpoints_log_saving U hU
  refine ⟨C * (1 + (2 : ℝ) ^ U), by positivity, B, hB, ?_⟩
  intro ε γ hε hεlt hγ
  obtain ⟨N₀, hN₀, hgeo⟩ :=
    B10PanGeometry_consumer_threshold ε γ B U K hε hεlt hγ hB hU.le
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN β hβ
  rcases hgeo N hN with ⟨hKN, hKY, _hY2, hA1N, hA1Y, hA2Y, hA2N,
    hDY, hDN, hscale, hsupp⟩
  have hbound := htwo (N := N) (D := panModulusCutoff N (B + 1))
    (A₁ := liuPanSourceIntervalLower N B) (A₂ := B10PanGeometryUpperWindow N γ)
    (ε := ε) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ)
    hKN hKY hε hεlt (fun _ hm => hsupp β hβ _ hm) hA2N hA2Y hA1N hA1Y hDN hDY
  calc
    _ ≤ C * ((N : ℝ) / Real.log (N : ℝ) ^ U +
        (⌊ε * (N : ℝ)⌋₊ : ℝ) / Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ U) := hbound
    _ ≤ C * ((N : ℝ) / Real.log (N : ℝ) ^ U +
        (2 : ℝ) ^ U * N / Real.log (N : ℝ) ^ U) := by gcongr
    _ = (C * (1 + (2 : ℝ) ^ U)) * N / Real.log (N : ℝ) ^ U := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig