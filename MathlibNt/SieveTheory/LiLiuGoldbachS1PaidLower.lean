import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
import MathlibNt.SieveTheory.LiLiuGoldbachS1LevelSix
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional

open scoped BigOperators
open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual S1 at the original alpha endpoint, with the standard BV error paid.
The remaining main sum is the genuine lower Rosser density, not an assumed f-bound. -/
theorem goldbachS1_levelSix_lower_paid (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
          (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).divisors,
            LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)))
              (S1LevelSixD N) d / Nat.totient d) -
          C * (N : ℝ) / Real.log (N : ℝ) ^ U ≤
        (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) : ℝ) := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov U hU
  obtain ⟨Nb, hb⟩ := eventually_atTop.mp hBV
  obtain ⟨Nd, _hNd, hd⟩ := S1LevelSix_panModulusCutoff_eventually B hB
  have hz : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (4 / 53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  obtain ⟨Nz, hz'⟩ := eventually_atTop.mp hz
  refine ⟨C, hC, ?_⟩
  intro ε hε hεu
  obtain ⟨Nm, _hNm, hm⟩ := goldbachS1_strictEndpoint_mainMass_lower ε 1 hε hεu (by norm_num)
  refine ⟨max 2 (max Nb (max Nd (max Nz Nm))), le_max_left _ _, ?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hrest : max Nb (max Nd (max Nz Nm)) ≤ N := (le_max_right _ _).trans hN
  have hNb : Nb ≤ N := (le_max_left _ _).trans hrest
  have hrest' : max Nd (max Nz Nm) ≤ N := (le_max_right _ _).trans hrest
  have hNd : Nd ≤ N := (le_max_left _ _).trans hrest'
  have hrest'' : max Nz Nm ≤ N := (le_max_right _ _).trans hrest'
  have hNz : Nz ≤ N := (le_max_left _ _).trans hrest''
  have hNm : Nm ≤ N := (le_max_right _ _).trans hrest''
  have hm2 : 2 ≤ goldbachS1Endpoint N ε := by
    simpa only [goldbachS1Endpoint] using (hm N hNm).1
  have hprime : ∀ p ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).primeFactors,
      p < S1LevelSixD N := by
    intro p hp
    have hpdata := Nat.mem_primeFactors.mp hp
    have hplt := ((prime_dvd_goldbachS1ProdPrimes_iff hpdata.1).mp hpdata.2.1).1
    exact S1LevelSix_lt_D_of_lt_Z (S1LevelSix_two_le_Z hN2) (S1LevelSix_lt_Z_of_lt_rpow hplt)
  have hfinite := goldbachS1_lowerRosser_mainTerm_sub_prefix_le hε hεu hEven hm2
    (hz' N hNz) hprime (hd N hNd).2.2
  have herr := hb N hNb hN2
  exact (sub_le_sub_left herr _).trans hfinite

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig