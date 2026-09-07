import MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensity
import MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinateConsumers
import MathlibNt.SieveTheory.LiLiuGoldbachCompositeDimension

open scoped BigOperators Topology
open Filter Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open JurkatRichert1965ChenGammaOneQOne

private theorem movingDensity_scalar_eventually (A K ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop,
      A * Real.exp (Real.sqrt K) * (Real.log D)^(-(1/3 : ℝ)) < ρ ∧
      (6 : ℝ)^13 ≤ Real.log D ∧ Real.exp 1 ≤ Real.log D := by
  have ht : Tendsto (fun D : ℝ =>
      A * Real.exp (Real.sqrt K) * (Real.log D)^(-(1/3 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).comp Real.tendsto_log_atTop)
  exact (ht.eventually (gt_mem_nhds hρ)).and
    ((Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((6 : ℝ)^13))).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))))

/-- The genuine moving natural layer on every composite modulus in the pair
range. The single threshold precedes all N, epsilon and outer moduli. Only the
active coordinate branch t >= 2 is asserted for the signed Rosser density. -/
theorem goldbachComposite_moving_lowerDensity (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ (ε : ℝ) (m : ℕ), 0 < m →
        (N : ℝ)^(8/53 : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) →
        let S := goldbachS3BoundingSieve N hEven ε ((N : ℝ)^(4/53 : ℝ)) m
        let D := LiuWeight.panModulusCutoff N B / m + 1
        let t := Real.log (D : ℝ) / Real.log ((N : ℝ)^(4/53 : ℝ))
        2 ≤ t →
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S * (jr1965f t - ρ) ≤
          S.mainSum (LinearSieve.lowerRosserWeight S.prodPrimes D) := by
  obtain ⟨A, _, hsource⟩ := exists_actual_lowerRosser_jr_powerBudget
  obtain ⟨K, hK, hlocal⟩ := exists_goldbachComposite_dimensionOne_constant
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (movingDensity_scalar_eventually A K ρ hρ)
  have hgrowth : ∀ᶠ N : ℕ in atTop, max 2 R₀ ≤ (N : ℝ)^(7/132 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/132)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨Ng, hg⟩ := eventually_atTop.mp hgrowth
  obtain ⟨Nc, hNc, hc⟩ := exists_pairLayer_coordinate_lt_six B hB
  refine ⟨max Nc Ng, by omega, ?_⟩
  intro N hN hEven ε m hm hml hmu S D t ht
  have hN4 : 4 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNg := hg N (by omega)
  have hgeom := hc N (by omega) m hm hml hmu
  have hR : R₀ ≤ (D : ℝ) := ((le_max_right _ _).trans hNg).trans hgeom.1
  have hD2 : 2 ≤ D := by exact_mod_cast ((le_max_left _ _).trans hNg).trans hgeom.1
  have hdata := hR₀ (D : ℝ) hR
  have hz : 1 < (N : ℝ)^(4/53 : ℝ) :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have ht6 : t < 6 := by
    dsimp [t]
    rw [Real.log_rpow hNp]
    exact hgeom.2
  have hpower : t^13 ≤ Real.log (D : ℝ) := by
    calc
      t^13 ≤ (6 : ℝ)^13 := by gcongr
      _ ≤ Real.log (D : ℝ) := hdata.2.1
  have hprime : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) < (N : ℝ)^(4/53 : ℝ) := by
    intro p hp
    have hd := Nat.mem_primeFactors.mp hp
    exact ((prime_dvd_goldbachS1ProdPrimes_iff hd.1).mp hd.2.1).1
  have hdensity := hsource S K hK (hlocal N hEven ε ((N : ℝ)^(4/53 : ℝ)) m)
    D ((N : ℝ)^(4/53 : ℝ)) hD2 hz hprime ht hpower hdata.2.2
  have hV : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    have hd := Nat.mem_primeFactors.mp hp
    exact (sub_pos.mpr (S.nu_lt_one_of_prime p hd.1 hd.2.1)).le
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hdata.1.le (jr1965f t)) hV).trans hdensity

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
