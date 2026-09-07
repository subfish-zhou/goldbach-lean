import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
import MathlibNt.SieveTheory.LiLiuGoldbachS1LevelSix
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.SuzukiChenAdaptiveDepthAbsorption
import MathlibNt.SieveTheory.SuzukiDensityBoundingSieveBridge
import MathlibNt.SieveTheory.SuzukiMovingSigmaElementaryHead

open scoped BigOperators
open Finset Filter
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

private theorem S1LowerDensitySix_exists_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ),
      HasDimensionOneLocalProductBound (goldbachS1BoundingSieve N hEven ε z) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven ε z z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (goldbachS1ProdPrimes N z).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (goldbachS1ProdPrimes N z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ goldbachS1ProdPrimes N z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N z)).mp hp'.1 |>.2
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachS1ProdPrimes_iff hprime).mp hpdiv |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hprime.two_le (by simpa using hpne.symm)
    exact ⟨hprime, hp2⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (goldbachS1ProdPrimes N z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound

private theorem S1LowerDensitySix_exists_Z_large (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → L ≤ S1LevelSixZ N := by
  have hpow :
      ∀ᶠ N : ℕ in atTop, (L : ℝ) ≤ (N : ℝ) ^ (4 / 53 : ℝ) := by
    exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (L : ℝ))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hpow
  refine ⟨N₀, ?_⟩
  intro N hN
  unfold S1LevelSixZ
  have hreal : (L : ℝ) ≤ (N : ℝ) ^ (4 / 53 : ℝ) := hN₀ N hN
  exact_mod_cast hreal.trans (Nat.le_ceil _)

private theorem S1LowerDensitySix_Z_le_D (N : ℕ) :
    S1LevelSixZ N ≤ S1LevelSixD N := by
  by_cases hZ : S1LevelSixZ N = 0
  · simp [S1LevelSixD, hZ]
  · have hZpos : 0 < S1LevelSixZ N := Nat.pos_iff_ne_zero.mpr hZ
    simpa [S1LevelSixD] using
      (Nat.pow_le_pow_right hZpos (show (1 : ℕ) ≤ 6 by omega) :
        S1LevelSixZ N ^ 1 ≤ S1LevelSixZ N ^ 6)

private theorem S1LowerDensitySix_exists_D_large (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → R ≤ (S1LevelSixD N : ℝ) := by
  let L : ℕ := max 2 (Nat.ceil R)
  obtain ⟨N₀, hN₀⟩ := S1LowerDensitySix_exists_Z_large L
  refine ⟨N₀, ?_⟩
  intro N hN
  have hLZ : L ≤ S1LevelSixZ N := hN₀ N hN
  have hZD : S1LevelSixZ N ≤ S1LevelSixD N := S1LowerDensitySix_Z_le_D N
  calc
    R ≤ L := by
      exact (Nat.le_ceil R).trans (by exact_mod_cast le_max_right 2 (Nat.ceil R))
    _ ≤ (S1LevelSixZ N : ℝ) := by exact_mod_cast hLZ
    _ ≤ (S1LevelSixD N : ℝ) := by exact_mod_cast hZD

/-- Fixed `s = 6` lower-density producer for the actual `S1` sieve at the
original `α = 4 / 53` cutoff.  The source-relative Suzuki theorem supplies the
main term, the exact bridge identifies it with the genuine lower Rosser main
sum, and the adaptive-depth error is absorbed uniformly in the finite carrier. -/
theorem goldbachS1_levelSix_lowerDensitySix
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (dimensionOneLowerLinearSieveFactor 6 - ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
              (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ))) ≤
          (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ))).mainSum
            (LinearSieve.lowerRosserWeight
              (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))) (S1LevelSixD N)) := by
  have hsrc : MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
      (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, hC1min, huniform⟩ :=
    exists_lowerRosserDensity_dimensionOneLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨C145, Clow, C, _hC145, _hClow, hC3, hall⟩ := huniform C1min le_rfl
  have hC : 0 ≤ C := by linarith
  obtain ⟨K₀, hK₀, hlocal₀⟩ :=
    S1LowerDensitySix_exists_dimensionOneLocalProductBound
  let K : ℝ := max 2 K₀
  have hK : 2 ≤ K := le_max_left _ _
  have hlocal : ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ),
      HasDimensionOneLocalProductBound (goldbachS1BoundingSieve N hEven ε z) K := by
    intro N hEven ε z
    exact MathlibNt.SieveTheory.hasDimensionOneLocalProductBound_mono_K
      (hlocal₀ N hEven ε z) (le_max_right 2 K₀)
  obtain ⟨Dσ, _hDσ, hσgate⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 6 (by norm_num)
  obtain ⟨Nσ, hNσlarge⟩ := S1LowerDensitySix_exists_D_large Dσ
  have hEevent :=
    eventually_all_depth_suzuki_error_half
      (H := jr1965Section13HatLayers) (C := C) (K := K) (s := 6)
      jr1965Section13HatSourceContract.toSection13HatContract
      hC (by norm_num : 0 < (6 : ℝ)) ρ hρ
  obtain ⟨DE, hDE⟩ := eventually_atTop.1 hEevent
  obtain ⟨NE, hNElarge⟩ := S1LowerDensitySix_exists_D_large DE
  refine ⟨max 2 (max Nσ NE), le_max_left _ _, ?_⟩
  intro N hN hEven ε hε0 hε1
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hrest : max Nσ NE ≤ N := (le_max_right _ _).trans hN
  have hNσle : Nσ ≤ N := (le_max_left _ _).trans hrest
  have hNEle : NE ≤ N := (le_max_right _ _).trans hrest
  let S : BoundingSieve := goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ))
  let D : ℕ := S1LevelSixD N
  let z : ℕ := S1LevelSixZ N
  let depth : ℕ := 2 * ((suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊).card + 1)
  have hD2 : 2 ≤ D := by
    simpa [D] using S1LevelSix_two_le_D hN2
  have hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ := by
    dsimp [D]
    rw [S1LevelSix_ceil_rootD_eq_Z N]
    exact S1LevelSix_two_le_Z hN2
  have hzEq : ⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ = z := by
    dsimp [D, z]
    exact S1LevelSix_ceil_rootD_eq_Z N
  have hσ : (6 : ℝ) ≤ sourceSigma (D : ℝ) 16 := by
    simpa [D] using hσgate (D : ℝ) (hNσlarge N hNσle)
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < z := by
    intro p hp
    have hp' : p ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).primeFactors := by
      simpa [S, goldbachS1BoundingSieve] using hp
    have hpdata := Nat.mem_primeFactors.mp hp'
    have hplt :=
      ((prime_dvd_goldbachS1ProdPrimes_iff hpdata.1).mp hpdata.2.1).1
    simpa [z] using S1LevelSix_lt_Z_of_lt_rpow hplt
  have hcutD : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact S1LevelSix_lt_D_of_lt_Z (S1LevelSix_two_le_Z hN2) (hcutZ p hp)
  have hdensityRaw := hall S K hK (hlocal N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ)))
    D hD2 6 (by norm_num) (by norm_num) hσ hz2
  have hdensity :
      suzukiVProduct S ((⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor 6 -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope jr1965Section13HatLayers depth (D : ℝ) 16 6 *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
        LinearSieve.lowerRosserSetDensitySum S.nu D
          (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊) := by
    simpa [depth] using hdensityRaw
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D z hcutZ hcutD
  have hV :
      0 ≤ suzukiVProduct S ((⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ : ℕ) : ℝ) := by
    exact (suzukiVProduct_pos S (((⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ : ℕ) : ℝ))).le
  have hErrorDepth :
      C * Real.exp (Real.sqrt K) *
          errorEnvelope jr1965Section13HatLayers depth (D : ℝ) 16 6 *
            (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ := by
    simpa [D, depth] using (hDE (D : ℝ) (hNElarge N hNEle) depth).2
  have htransport :
      suzukiVProduct S ((⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor 6 - ρ) ≤
        suzukiVProduct S ((⌈(D : ℝ) ^ (1 / (6 : ℝ))⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor 6 -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope jr1965Section13HatLayers depth (D : ℝ) 16 6 *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hV
    linarith
  have hfinal := htransport.trans hdensity
  rw [hzEq] at hfinal
  rw [← hbridge.1, hbridge.2.1] at hfinal
  simpa [S, D, goldbachS1BoundingSieve, mul_comm, mul_left_comm, mul_assoc] using hfinal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig