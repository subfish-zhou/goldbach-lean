import MathlibNt.SieveTheory.LiLiuGoldbachB10UpperError
import MathlibNt.SieveTheory.LiLiuGoldbachB10CommonRemainder

open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual B10 upper linear sieve with the common main mass and the complete
remainder paid. The genuine factor is used only on its proved ratio window.
The main mass still uses the literal floor endpoint. -/
theorem goldbachB10SiftedCount_upper_paid (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ →
      ∃ z₀ : ℝ, ∀ ε γ : ℝ, 0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        ∀ β : ℝ, (1 : ℝ) / 18 < β → ∀ Z s : ℝ,
        z₀ ≤ Z → 2 ≤ Z →
        s = Real.log ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)) /
          Real.log Z → 3 / 2 ≤ s → s ≤ 4 →
        let X := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        let S := goldbachB10BoundingSieve N hEven ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z X
        (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
          X * (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, hcommon⟩ := goldbachB10CommonRemainder_log_saving U hU
  refine ⟨C, hC, B, hB, ?_⟩
  intro ρ hρ
  obtain ⟨z₀, hfactor⟩ := goldbachB10SiftedCount_le_rosserFactor_add_upperErrSum ρ hρ
  refine ⟨z₀, ?_⟩
  intro ε γ hε hεlt hγ
  obtain ⟨Nc, hNc, hc⟩ := hcommon ε γ hε hεlt hγ
  obtain ⟨Nx, _hNx, hx⟩ := goldbachB10MainMass_nonneg_eventually ε γ hε hεlt hγ
  refine ⟨max Nc Nx, hNc.trans (le_max_left _ _), ?_⟩
  intro N hN hEven β hβ Z s hz hZ hs hslo hshi
  have hNc' : Nc ≤ N := (le_max_left _ _).trans hN
  have hNx' : Nx ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNc.trans hNc'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let X := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let S := goldbachB10BoundingSieve N hEven ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z X
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hX : 0 ≤ X := hx N hNx' β hβ
  have herr : LinearSieve.upperErrSum S (Nat.floor Δ + 1)
      (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
      C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
    calc
      _ ≤ ∑ d ∈ (Finset.Icc 1 (panModulusCutoff N (B + 1))).filter (fun d => Nat.Coprime d N),
          |((goldbachB10DivisorAtoms N d ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℝ) - X / d.totient| := by
        exact goldbachB10_upperErrSum_le_commonModulusSum N hEven ε ((N : ℝ) ^ β)
          ((N : ℝ) ^ γ) Z X (panModulusCutoff N (B + 1))
      _ ≤ _ := by simpa only [goldbachB10CommonRemainder] using hc N hNc' β hβ
  have hf := hfactor N hEven ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z Δ s X
    hz hZ hΔ hs hslo hshi hX
  exact hf.trans (add_le_add le_rfl herr)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig