import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser
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

private theorem S1BetaLowerDensity_exists_dimensionOneLocalProductBound :
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

/-- Fixed-`s` lower-density producer for the genuine `beta = 4 / 33` root cutoff
`ζ(N,s) = D(N,s)^(1/s)` with `D(N,s) = ceil(N^((4/33)s))`.  The source-relative
Suzuki theorem provides the lower factor, the exact bridge identifies the
finite Suzuki objects with the honest `BoundingSieve` main sum and sieve
product, and the adaptive-depth error is absorbed uniformly at this fixed `s`.
-/
theorem goldbachS1_beta_lowerDensity
    (s ρ : ℝ) (hs4 : 4 ≤ s) (hslt : s < (33 / 8 : ℝ)) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        let S : BoundingSieve := goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)
        (dimensionOneLowerLinearSieveFactor s - ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤
          S.mainSum
            (LinearSieve.lowerRosserWeight
              (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s))
              (S1BetaGeometryD N s)) := by
  have hs : 0 < s := by linarith
  have hs6 : s ≤ 6 := by linarith
  have hsrc : MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
      (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, hC1min, huniform⟩ :=
    exists_lowerRosserDensity_dimensionOneLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC3, hall⟩ := huniform C1min le_rfl
  have hC : 0 ≤ C := by linarith
  obtain ⟨K₀, hK₀, hlocal₀⟩ :=
    S1BetaLowerDensity_exists_dimensionOneLocalProductBound
  let K : ℝ := max 2 K₀
  have hK : 2 ≤ K := le_max_left _ _
  have hlocal : ∀ (N : ℕ) (hEven : Even N) (ε z : ℝ),
      HasDimensionOneLocalProductBound (goldbachS1BoundingSieve N hEven ε z) K := by
    intro N hEven ε z
    exact MathlibNt.SieveTheory.hasDimensionOneLocalProductBound_mono_K
      (hlocal₀ N hEven ε z) (le_max_right 2 K₀)
  obtain ⟨Dσ, _hDσ, hσgate⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) s (by norm_num)
  obtain ⟨Nσ, hNσ, hNσlarge⟩ :=
    S1BetaGeometry_eventually_ge_constant s Dσ hs
  have hEevent :=
    eventually_all_depth_suzuki_error_half
      (H := jr1965Section13HatLayers) (C := C) (K := K) (s := s)
      jr1965Section13HatSourceContract.toSection13HatContract
      hC hs ρ hρ
  obtain ⟨DE, hDE⟩ := eventually_atTop.1 hEevent
  obtain ⟨NE, hNE, hNElarge⟩ :=
    S1BetaGeometry_eventually_ge_constant s DE hs
  refine ⟨max Nσ NE, le_trans hNσ (le_max_left _ _), ?_⟩
  intro N hN hEven ε hε0 hε1
  let S : BoundingSieve := goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)
  let D : ℕ := S1BetaGeometryD N s
  let z : ℕ := S1BetaGeometryZ N s
  let level : ℕ := 2 * ((suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / s)⌉₊).card + 1)
  have hNσle : Nσ ≤ N := (le_max_left _ _).trans hN
  have hNEle : NE ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNσ.trans hNσle
  have hD2 : 2 ≤ D := by
    simpa [D] using S1BetaGeometry_two_le_D hN2 hs
  have hzEq : ⌈(D : ℝ) ^ (1 / s)⌉₊ = z := by
    dsimp [D, z]
    exact S1BetaGeometry_ceil_zeta_eq_Z N s
  have hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
    rw [hzEq]
    simpa [z] using S1BetaGeometry_two_le_Z hD2 hs
  have hσ : s ≤ sourceSigma (D : ℝ) 16 := by
    simpa [D] using hσgate (D : ℝ) (hNσlarge N hNσle)
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < z := by
    intro p hp
    have hp' : p ∈ (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)).primeFactors := by
      simpa [S, goldbachS1BoundingSieve] using hp
    have hpdata := Nat.mem_primeFactors.mp hp'
    have hplt :
        (p : ℝ) < S1BetaGeometryZeta N s :=
      (prime_dvd_goldbachS1ProdPrimes_iff hpdata.1).mp hpdata.2.1 |>.1
    simpa [z] using (Nat.lt_ceil.mpr hplt)
  have hcutD : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    have hp' : p ∈ (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)).primeFactors := by
      simpa [S, goldbachS1BoundingSieve] using hp
    have hpdata := Nat.mem_primeFactors.mp hp'
    simpa [D] using
      S1BetaGeometry_primeFactor_lt_D hN2 hs4 hpdata.1 hpdata.2.1
  have hdensityRaw := hall S K hK (hlocal N hEven ε (S1BetaGeometryZeta N s))
    D hD2 s hs4 hs6 hσ hz2
  have hdensity :
      suzukiVProduct S ((⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor s -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope jr1965Section13HatLayers level (D : ℝ) 16 s *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
        LinearSieve.lowerRosserSetDensitySum S.nu D
          (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / s)⌉₊) := by
    simpa [level] using hdensityRaw
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D z hcutZ hcutD
  have hV :
      0 ≤ suzukiVProduct S ((⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) : ℝ) := by
    exact (suzukiVProduct_pos S (((⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) : ℝ))).le
  have hErrorLevel :
      C * Real.exp (Real.sqrt K) *
          errorEnvelope jr1965Section13HatLayers level (D : ℝ) 16 s *
            (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ := by
    simpa [D, level] using (hDE (D : ℝ) (hNElarge N hNEle) level).2
  have htransport :
      suzukiVProduct S ((⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor s - ρ) ≤
        suzukiVProduct S ((⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) : ℝ) *
          (dimensionOneLowerLinearSieveFactor s -
            C * Real.exp (Real.sqrt K) *
              errorEnvelope jr1965Section13HatLayers level (D : ℝ) 16 s *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hV
    linarith
  have hfinal := htransport.trans hdensity
  rw [hzEq] at hfinal
  rw [← hbridge.1, hbridge.2.1] at hfinal
  simpa [S, D, goldbachS1BoundingSieve, mul_comm, mul_left_comm, mul_assoc] using hfinal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig