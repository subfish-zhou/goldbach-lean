import MathlibNt.SieveTheory.LiLiuGoldbachB10RosserFactor
import MathlibNt.SieveTheory.LiLiuGoldbachB9CommonRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachB8PaidUpper

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The full Rosser error is dominated on its actual strict-level support, including one. -/
theorem goldbachB9Plus_upperErrSum_le_levelRemainder
    (N : ℕ) (hEven : Even N) (Z Δ : ℝ) :
    let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)
    LinearSieve.upperErrSum S (Nat.floor Δ + 1)
      (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
        ∑ d ∈ S.prodPrimes.divisors.filter (fun d => d < Nat.floor Δ + 1), |S.rem d| := by
  dsimp only
  unfold LinearSieve.upperErrSum
  apply sum_le_sum
  intro d _
  exact (mul_le_mul_of_nonneg_right
    (LinearSieve.abs_upperRosserWeight_le_one _ _ d)
    (abs_nonneg _)).trans_eq (one_mul _)

/-- No comparison of Z with either factor of the closed C10 support is needed. -/
theorem goldbachB9Plus_upperErrSum_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z : ℝ,
        let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
        let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)
        LinearSieve.upperErrSum S (Nat.floor Δ + 1)
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Nr, hNr, hrem⟩ :=
    goldbachB9PlusBoundingSieve_levelRemainder_log_saving U hU
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp hlogs
  refine ⟨C, hC, B, hB, max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z
  have hNr' : Nr ≤ N := (le_max_left _ _).trans hN
  have hNl' : Nl ≤ N := (le_max_right _ _).trans hN
  exact (goldbachB9Plus_upperErrSum_le_levelRemainder N hEven Z _).trans
    (hrem N hNr' hEven Z _
      (goldbachB8Plus_floor_paidLevel_le_panModulusCutoff N B (hl N hNl')))

/-- The genuine zero-prefix sieve with its fixed full Li mass and all errors paid.
The constants and N threshold precede the Rosser tolerance and cutoff. -/
theorem goldbachB9PlusSiftedCount_upper_paid (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ z₀ : ℝ,
        ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z s : ℝ,
          z₀ ≤ Z → 2 ≤ Z →
          s = Real.log ((N : ℝ) ^ (1 / 2 : ℝ) /
            Real.log (N : ℝ) ^ (B + 1)) / Real.log Z →
          3 / 2 ≤ s → s ≤ 4 →
          let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)
          (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (4 / 53 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) ≤
              goldbachB9PlusMainMass N * (jurkatRichertUpperLinearSieveFactor s + ρ) *
                sieveProductPrimeFactors S +
              C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Nr, hNr, herr⟩ := goldbachB9Plus_upperErrSum_log_saving U hU
  obtain ⟨Nx, _hNx, hx⟩ := goldbachB9PlusMainMass_nonneg_eventually
  refine ⟨C, hC, B, hB, max Nr Nx, hNr.trans (le_max_left _ _), ?_⟩
  intro ρ hρ
  obtain ⟨z₀, hfactor⟩ := goldbachB10SiftedCount_le_rosserFactor_add_upperErrSum ρ hρ
  refine ⟨z₀, ?_⟩
  intro N hN hEven Z s hz hZ hs hslo hshi
  have hNr' : Nr ≤ N := (le_max_left _ _).trans hN
  have hNx' : Nx ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := hNr.trans hNr'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  exact (hfactor N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ)) Z Δ s (goldbachB9PlusMainMass N)
    hz hZ hΔ hs hslo hshi (hx N hNx')).trans
      (add_le_add le_rfl (herr N hNr' hEven Z))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig