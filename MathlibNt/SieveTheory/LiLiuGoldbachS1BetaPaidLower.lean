import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional

open scoped BigOperators
open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Increasing the strict prime cutoff can only decrease the literal S1 count. -/
theorem goldbachS1_antitone_cutoff (A : Finset ℕ) (N : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    goldbachS1 A N y ≤ goldbachS1 A N x := by
  classical
  unfold goldbachS1 literalH
  exact_mod_cast (Finset.card_le_card (show A.filter (literalHPoint N 1 y) ⊆
      A.filter (literalHPoint N 1 x) from by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hdiv, hsurvives⟩
    exact Finset.mem_filter.mpr ⟨hnA, hdiv, survivesSieve_mono hxy hsurvives⟩))

/-- The original beta endpoint is bounded below using the slightly larger
real root cutoff. The BV constant is chosen before both s and epsilon. -/
theorem goldbachS1_beta_lower_paid (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 4 ≤ s → s < (33 / 8 : ℝ) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
          (∑ d ∈ (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)).divisors,
            LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s))
              (S1BetaGeometryD N s) d / Nat.totient d) -
          C * (N : ℝ) / Real.log (N : ℝ) ^ U ≤
        (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov U hU
  obtain ⟨Nb, hb⟩ := eventually_atTop.mp hBV
  have hz : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (4 / 33 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 33)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  obtain ⟨Nz, hz'⟩ := eventually_atTop.mp hz
  refine ⟨C, hC, ?_⟩
  intro s hs4 hslt ε hε hεu
  have hs : 0 < s := by linarith
  obtain ⟨Nd, _hNd, hd⟩ := S1BetaGeometry_panModulusCutoff_eventually s B hs4 hslt hB
  obtain ⟨Nm, _hNm, hm⟩ := goldbachS1_strictEndpoint_mainMass_lower ε 1 hε hεu (by norm_num)
  refine ⟨max 4 (max Nb (max Nd (max Nz Nm))), le_max_left _ _, ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hrest : max Nb (max Nd (max Nz Nm)) ≤ N := (le_max_right _ _).trans hN
  have hNb : Nb ≤ N := (le_max_left _ _).trans hrest
  have hrest' : max Nd (max Nz Nm) ≤ N := (le_max_right _ _).trans hrest
  have hNd : Nd ≤ N := (le_max_left _ _).trans hrest'
  have hrest'' : max Nz Nm ≤ N := (le_max_right _ _).trans hrest'
  have hNz : Nz ≤ N := (le_max_left _ _).trans hrest''
  have hNm : Nm ≤ N := (le_max_right _ _).trans hrest''
  have hm2 : 2 ≤ goldbachS1Endpoint N ε := by
    simpa only [goldbachS1Endpoint] using (hm N hNm).1
  have hprime : ∀ p ∈ (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)).primeFactors,
      p < S1BetaGeometryD N s := by
    intro p hp
    have hpdata := Nat.mem_primeFactors.mp hp
    exact S1BetaGeometry_primeFactor_lt_D hN2 hs4 hpdata.1 hpdata.2.1
  have hzeta : (N : ℝ) ^ (4 / 33 : ℝ) ≤ S1BetaGeometryZeta N s :=
    S1BetaGeometry_rpow_le_zeta hs
  have hfinite := goldbachS1_lowerRosser_mainTerm_sub_prefix_le hε hεu hEven hm2
    ((hz' N hNz).trans hzeta) hprime (hd N hNd).2.2.2
  have herr := hb N hNb hN2
  have hpaid := (sub_le_sub_left herr _).trans hfinite
  have hmono : (goldbachS1 (goldbachDifferenceCarrier N ε) N (S1BetaGeometryZeta N s) : ℝ) ≤
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) := by
    exact_mod_cast goldbachS1_antitone_cutoff (goldbachDifferenceCarrier N ε) N hzeta
  exact hpaid.trans hmono

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig