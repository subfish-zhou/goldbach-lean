import MathlibNt.SieveTheory.LiLiuGoldbachB8RosserFactor
import MathlibNt.SieveTheory.LiLiuGoldbachB8PanDistribution

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Only actual sieve divisors occur; the interval includes modulus one. -/
theorem goldbachB8Plus_upperErrSum_le_sieveDivisorSum
    (N : ℕ) (hEven : Even N) (Z Δ : ℝ) (Q : ℕ) (hQ : Nat.floor Δ ≤ Q) :
    let S := goldbachB8PlusBoundingSieve N hEven Z
    LinearSieve.upperErrSum S (Nat.floor Δ + 1)
      (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
        ∑ d ∈ (Icc 1 Q).filter (fun d => d ∣ goldbachB10ProdPrimes N Z), |S.rem d| := by
  let S := goldbachB8PlusBoundingSieve N hEven Z
  let D := Nat.floor Δ + 1
  let I := S.prodPrimes.divisors.filter (fun d => d < D)
  have hsub : I ⊆ (Icc 1 Q).filter (fun d => d ∣ goldbachB10ProdPrimes N Z) := by
    intro d hd
    obtain ⟨hddiv, hdD⟩ := mem_filter.mp hd
    have hdpos := Nat.pos_of_mem_divisors hddiv
    have hdP : d ∣ goldbachB10ProdPrimes N Z := (Nat.mem_divisors.mp hddiv).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hdpos, by dsimp [D] at hdD; omega⟩, hdP⟩
  change (∑ d ∈ I, |LinearSieve.upperRosserWeight S.prodPrimes D d| * |S.rem d|) ≤ _
  calc
    _ ≤ ∑ d ∈ I, |S.rem d| := by
      apply sum_le_sum
      intro d _
      exact (mul_le_mul_of_nonneg_right
        (LinearSieve.abs_upperRosserWeight_le_one S.prodPrimes D d)
        (abs_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- The paid level has exponent B+1, whereas the supplied Pan window has exponent B. -/
theorem goldbachB8Plus_floor_paidLevel_le_panModulusCutoff
    (N : ℕ) (B : ℝ) (hlog : 1 ≤ Real.log (N : ℝ)) :
    Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)) ≤
      panModulusCutoff N B := by
  have hlogpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hpow : Real.log (N : ℝ) ^ B ≤ Real.log (N : ℝ) ^ (B + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_left
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.rpow_pos_of_pos hlogpos B) hpow

theorem goldbachB8Plus_upperErrSum_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z : ℝ,
        Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11) →
        let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
        let S := goldbachB8PlusBoundingSieve N hEven Z
        LinearSieve.upperErrSum S (Nat.floor Δ + 1)
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Nr, hNr, hrem⟩ :=
    goldbachB8PlusBoundingSieve_remainder_log_saving U hU
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp hlogs
  refine ⟨C, hC, B, hB, max Nr Nl, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven Z hZ
  have hNr' : Nr ≤ N := (le_max_left _ _).trans hN
  have hNl' : Nl ≤ N := (le_max_right _ _).trans hN
  exact (goldbachB8Plus_upperErrSum_le_sieveDivisorSum N hEven Z _
    (panModulusCutoff N B)
    (goldbachB8Plus_floor_paidLevel_le_panModulusCutoff N B (hl N hNl'))).trans
      (hrem N hNr' hEven Z hZ)

/-- The actual labelled upper sieve, with the entire finite remainder paid.
The threshold for N is independent of the factor tolerance and the sieve cutoff. -/
theorem goldbachB8PlusSiftedCount_upper_paid (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ z₀ : ℝ,
        ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z s : ℝ,
          z₀ ≤ Z → 2 ≤ Z → Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11) →
          s = Real.log ((N : ℝ) ^ ((1 : ℝ) / 2) /
            Real.log (N : ℝ) ^ (B + 1)) / Real.log Z →
          3 / 2 ≤ s → s ≤ 4 →
          let S := goldbachB8PlusBoundingSieve N hEven Z
          ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) ≤
            goldbachB8PlusMainMass N * (jurkatRichertUpperLinearSieveFactor s + ρ) *
              sieveProductPrimeFactors S +
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, hN₀, herr⟩ := goldbachB8Plus_upperErrSum_log_saving U hU
  refine ⟨C, hC, B, hB, N₀, hN₀, ?_⟩
  intro ρ hρ
  obtain ⟨z₀, hfactor⟩ := goldbachB8PlusSiftedCount_le_rosserFactor_add_upperErrSum ρ hρ
  refine ⟨z₀, ?_⟩
  intro N hN hEven Z s hz hZ hZupper hs hslo hshi
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  exact (hfactor N hEven Z Δ s hz hZ hΔ hs hslo hshi).trans
    (add_le_add le_rfl (herr N hN hEven Z hZupper))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig