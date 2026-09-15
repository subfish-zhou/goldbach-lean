import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryScalar

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform payment of the actual joined secondary term. The constant is selected
before x, all scales, the family, the signed shift, keys and dyadic data. -/
theorem directJoinedSecondary_uniform
    {κ δ ρ η Cnonzero Csecondary Ccoeff Couter : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : 0 ≤ Cnonzero) (hCsec : 0 ≤ Csecondary) (hCo : 0 ≤ Couter) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M T R S : ℝ),
      4 ≤ x → 1 ≤ M → 1 ≤ T → x = 4 * M * T →
      1 ≤ R → 1 ≤ S → R * S ≤ x →
      ∀ (N : Finset ℕ), (∀ n ∈ N, 0 < n) → (∀ n ∈ N, (n : ℝ) ≤ 2 * T) →
      ∀ (a : ℤ), |(a : ℝ)| ≤ x → ∀ (F : ℕ), (F : ℝ) ≤ 2 * T →
      ∀ (K : WExtractedKey), K ∈ wExtractedKeyBox (x ^ η) →
      ∀ (j cap : Fin 5 → ℕ) (positive : Bool) (b : ℕ) (t : WExtractedTuple × ℤ),
      t ∈ wAnalyticDyadicBlock
        (wExtractedKeyFiber (wFloorCutoff M (x ^ η)) N (Ioc 0 ⌊R * S⌋₊)
          a (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive →
      wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
        Real.sqrt (directJoinedSecondary κ δ ρ Cnonzero Csecondary Ccoeff x a R S K F j cap) /
          T ^ 2 ≤
      C * x ^ (100 * (κ + δ + ρ + η)) *
        (T * R ^ (3 / 4 : ℝ) * S ^ (3 / 2 : ℝ) / Real.sqrt x) := by
  obtain ⟨Cw, hCw, hweight⟩ := directPaySecondary_weight_paid
    (ρ := ρ) (Ccoeff := Ccoeff) hκ hδ hC hCsec
  let B : ℝ := 2048 * (256 * Real.sqrt 8) * Cw * Couter
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := Real.sqrt B + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt hB, Real.sqrt_nonneg B]
  refine ⟨C, hCpos, ?_⟩
  intro x M T R S hx hM hT hxMT hR hS hRS N hN hNT a ha F hF K hK j cap positive b t ht
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hT0 : 0 < T := by linarith
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hZ : 1 ≤ x ^ η := Real.one_le_rpow hx1 hη
  have hZ0 : 0 ≤ x ^ η := by positivity
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hD : (1 : ℝ) ≤ K.D := by
    exact_mod_cast (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hdZ := (directLocalScale_key_bounds hZ0 hK).2
  obtain ⟨hk, hr, hs⟩ := directLocalScale_fullLevel_coordinates hN (by positivity)
    hR0.le hS0.le ht
  have hn := directPaySecondary_n_bound hN hQ hNT ht
  have hH := directLocalScale_floor_frequency_le hM0 hZ0 hN hQ ht
  rw [directLocalScale_frequency_change_variables hM0.ne' hT0.ne' hxMT] at hH
  obtain ⟨hHg, hAg, hqg⟩ := directPaySecondary_growth_data hx hη hη1 hM hT hxMT
    hR hS hRS hN hNT ha hF hK ht
  have hw := hweight x hx1 a K F j ha hHg hAg hqg
  have hw0 := directPaySecondary_weight_nonneg (κ := κ) (δ := δ) (ρ := ρ)
    (Csec := Csecondary) (Ccoeff := Ccoeff) (x := x) hC a K F j
  have he := directPaySecondary_energy_local (δ := δ) (ρ := ρ) (Ccoeff := Ccoeff)
    (x := x) hκ hC hCsec hT0.le a R S K F j cap hF
  have hscalar := directPaySecondary_scalar hD (Nat.cast_nonneg K.D') hdZ
    (by positivity : 0 < (2 : ℝ) ^ j 1) (by positivity : 0 < (2 : ℝ) ^ j 2)
    (by positivity : 0 < (2 : ℝ) ^ j 3) (by positivity : 0 < (2 : ℝ) ^ j 4)
    hZ hx0 hT hR hS (show 0 ≤ Couter * x ^ ρ by positivity)
    (show 0 ≤ (256 * Real.sqrt 8) *
      directPaySecondaryWeight κ δ ρ Cnonzero Csecondary Ccoeff x a K F j by positivity)
    hk hn hr hs (by convert hH using 1; ring)
  apply directPaySecondary_root_of_sq
    (show 0 ≤ wBlockAmplitude K j by unfold wBlockAmplitude; positivity)
    (show 0 ≤ directJoinedMass ρ Couter x T j by unfold directJoinedMass; positivity)
    (by positivity) (by positivity) he
  apply hscalar.trans
  have hp : x ^ (4 * ρ + 4 * κ + 11 * δ) * x ^ ρ * (x ^ η) ^ 6 ≤
      (x ^ (100 * (κ + δ + ρ + η))) ^ 2 := by
    rw [← Real.rpow_natCast (x ^ η) 6, ← Real.rpow_mul hx0.le,
      ← Real.rpow_add hx0, ← Real.rpow_add hx0,
      ← Real.rpow_natCast (x ^ (100 * (κ + δ + ρ + η))) 2,
      ← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ 2048 * ((256 * Real.sqrt 8) * (Cw * x ^ (4 * ρ + 4 * κ + 11 * δ))) *
        (Couter * x ^ ρ) * (x ^ η) ^ 6 * T ^ 2 * R * Real.sqrt R * S ^ 3 / x := by gcongr
    _ = B * (x ^ (4 * ρ + 4 * κ + 11 * δ) * x ^ ρ * (x ^ η) ^ 6) *
        (T ^ 2 * R * Real.sqrt R * S ^ 3 / x) := by dsimp [B]; ring
    _ ≤ C ^ 2 * (x ^ (100 * (κ + δ + ρ + η))) ^ 2 *
        (T ^ 2 * R * Real.sqrt R * S ^ 3 / x) := by gcongr
    _ = _ := by
      rw [← directPaySecondary_body_sq hx0.le hR0 hS0.le]
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
