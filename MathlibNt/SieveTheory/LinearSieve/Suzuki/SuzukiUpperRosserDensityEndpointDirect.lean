import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAllDepth

open Set Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable section

/-- The dimension-one local-product estimate is monotone in its scalar constant. -/
theorem HasDimensionOneLocalProductBound.mono
    {S : BoundingSieve} {K K' : ℝ}
    (h : HasDimensionOneLocalProductBound S K) (hKK' : K ≤ K') :
    HasDimensionOneLocalProductBound S K' := by
  intro z₁ z₂ hz₁ hz₁₂
  have hbase := h z₁ z₂ hz₁ hz₁₂
  have hlog₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hlog₂ : 0 ≤ Real.log z₂ :=
    (Real.log_pos ((show (1 : ℝ) < 2 by norm_num).trans_le (hz₁.trans hz₁₂))).le
  calc
    (∏ p ∈ S.prodPrimes.primeFactors.filter
        (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂),
        (1 - S.nu p)⁻¹) ≤
        Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbase
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K' / Real.log z₁) := by
      gcongr

/-- Real endpoint geometry for the natural ceiling used by the all-depth Suzuki
producer.  In particular, every prime at most the requested real cutoff is
strictly below the rounded Suzuki cutoff. -/
theorem real_level_to_natCeil_geometry
    {z Δ s : ℝ} (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s) :
    let D := Nat.floor Δ + 1
    2 ≤ D ∧
      Δ < (D : ℝ) ∧
      z < (D : ℝ) ^ (1 / s) ∧
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
  have hzpos : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogzne : Real.log z ≠ 0 := ne_of_gt hlogz
  have hspos : 0 < s := by linarith
  have hsone : 1 ≤ s := by linarith
  have hΔeq : Δ = z ^ s := by
    rw [Real.rpow_def_of_pos hzpos, hs]
    have hcancel : Real.log z * (Real.log Δ / Real.log z) = Real.log Δ := by
      field_simp
    rw [hcancel, Real.exp_log hΔ]
  have hzΔ : z ≤ Δ := by
    rw [hΔeq]
    calc
      z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
      _ ≤ z ^ s := Real.rpow_le_rpow_of_exponent_le hz1 hsone
  let D := Nat.floor Δ + 1
  have hD2 : 2 ≤ D := by
    dsimp [D]
    have : 2 ≤ Nat.floor Δ := Nat.le_floor (hz.trans hzΔ)
    omega
  have hΔD : Δ < (D : ℝ) := by
    dsimp [D]
    simpa using Nat.lt_floor_add_one Δ
  have hroot : Δ ^ (1 / s) = z := by
    rw [hΔeq, ← Real.rpow_mul hzpos.le]
    have hmul : s * (1 / s) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  have hrootlt : z < (D : ℝ) ^ (1 / s) := by
    rw [← hroot]
    exact Real.rpow_lt_rpow hΔ.le hΔD (by positivity)
  have hzceil : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
    have : (2 : ℕ) < ⌈(D : ℝ) ^ (1 / s)⌉₊ :=
      Nat.lt_ceil.mpr (hz.trans_lt hrootlt)
    omega
  exact ⟨hD2, hΔD, hrootlt, hzceil⟩

/-- Direct all-depth closure of the production upper Rosser density endpoint.
The constants in the all-depth estimate are selected before `S`; the adaptive
odd depth is chosen only inside the natural-ceiling consumer.  The production
exact finite Rosser/Suzuki bridge is consumed unconditionally, with no residual
bridge or ordered-tail premise. -/
theorem dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
    (H : Section13HatLayers) {d δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d δ Θ) :
    DimensionOneUpperRosserDensityFundamentalLemma := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth H hH hsrc
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hnat⟩ := hall C1min le_rfl
  intro K ρ hK hρ
  let K' : ℝ := max 2 K
  have hK' : 2 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Dσ, hDσ1, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold d 4 hsrc.d_pos.le
  have herrEv := eventually_all_odd_depth_suzuki_error_upper_window
    H hH.toSection13HatContract (C := C) (K := K') (d := d) (Δ := δ) (ρ := ρ)
      hC0 hsrc.d_pos.le hsrc.hDelta_pos hρ
  obtain ⟨DE, hDE⟩ := eventually_atTop.1 herrEv
  let z₀ : ℝ := max 2 (max Dσ DE)
  refine ⟨z₀, ?_⟩
  intro S z Δ s hz₀ hz2 hΔ hlocal hcut hs hslo hshi
  have hzσ : Dσ ≤ z :=
    (le_max_left Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz₀)
  have hzE : DE ≤ z :=
    (le_max_right Dσ DE).trans ((le_max_right 2 (max Dσ DE)).trans hz₀)
  let D : ℕ := Nat.floor Δ + 1
  have hgeom := real_level_to_natCeil_geometry hz2 hΔ hs hslo
  dsimp only at hgeom
  have hD2 : 2 ≤ D := by simpa [D] using hgeom.1
  have hΔD : Δ < (D : ℝ) := by simpa [D] using hgeom.2.1
  have hzroot : z < (D : ℝ) ^ (1 / s) := by simpa [D] using hgeom.2.2.1
  have hzceil : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ := by simpa [D] using hgeom.2.2.2
  have hzD : z < (D : ℝ) := by
    have hΔeq : Δ = z ^ s := by
      have hzpos : 0 < z := by linarith
      have hlogz : Real.log z ≠ 0 :=
        ne_of_gt (Real.log_pos (by linarith))
      rw [Real.rpow_def_of_pos hzpos, hs]
      have hcancel : Real.log z * (Real.log Δ / Real.log z) = Real.log Δ := by
        field_simp
      rw [hcancel, Real.exp_log hΔ]
    have hzΔ : z ≤ Δ := by
      rw [hΔeq]
      calc
        z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
        _ ≤ z ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    exact hzΔ.trans_lt hΔD
  have hσ : 4 ≤ sourceSigma (D : ℝ) d := hDσ _ (hzσ.trans hzD.le)
  have hsσ : s ≤ sourceSigma (D : ℝ) d := hshi.trans hσ
  have hcutCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
    intro p hp
    exact Nat.lt_ceil.mpr ((hcut p hp).trans_lt hzroot)
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono hlocal hKK'
  have hmain := hnat S K' hK' hlocal' D hD2 s hslo hshi hsσ hzceil hcutCeil
  let N : ℕ := 2 * S.prodPrimes.primeFactors.card + 1
  have hNodd : Odd N := ⟨S.prodPrimes.primeFactors.card, by rfl⟩
  have herr := hDE (D : ℝ) (hzE.trans hzD.le) N hNodd s hslo hshi
  have hfactor :=
    suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
      H hH hslo hshi
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact sub_nonneg.mpr
      (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpDvd).le
  dsimp only [D] at hmain ⊢
  dsimp only [N] at herr
  rw [hfactor] at hmain
  nlinarith


end
end MathlibNt.SieveTheory
