import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainNormalize

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Exact exponent bookkeeping for the squared, normalized main contribution. -/
theorem directPayMain_global_square {C L x T R S ρ p η : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hx : 0 < x) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    25165824*(C*x^ρ)*(L*x^p)*(x^η)^7*T^(5/2 : ℝ)*R^(7/2 : ℝ)*S^4/x^2 =
      (Real.sqrt (25165824*C*L)*x^((ρ+p+7*η)/2)*
        (T^(5/4 : ℝ)*R^(7/4 : ℝ)*S^2/x))^2 := by
  have hxpow : (x^((ρ+p+7*η)/2))^2 = x^ρ*x^p*(x^η)^7 := by
    rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ((ρ+p+7*η)/2)*2 = ρ+p+η*7 by ring,
      Real.rpow_add hx, Real.rpow_add hx]
  have hTpow : (T^(5/4 : ℝ))^2 = T^(5/2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hT]; norm_num
  have hRpow : (R^(7/4 : ℝ))^2 = R^(7/2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hR]; norm_num
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ 25165824*C*L by positivity),
    hxpow, hTpow, hRpow]
  ring

/-- Pointwise main payment on the actual nonempty retained block.
The squared proof keeps and pays the span/q summand before global enlargement. -/
theorem directPayMain_bound
    (κ δ ρ η Cnonzero Cτ Cjoint Ca Ccoeff Couter : ℝ)
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : 0 ≤ Cnonzero) (hCτ : 0 ≤ Cτ) (hCjoint : 0 ≤ Cjoint)
    (hCa : 0 ≤ Ca) (hCo : 0 ≤ Couter)
    {x M T R S : ℝ} (hx : 4 ≤ x) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hxMT : x = 4*M*T) (hR : 1 ≤ R) (hS : 1 ≤ S) (hRS : R*S ≤ x)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2*T)
    (a : ℤ) (ha : |(a : ℝ)| ≤ x) (F : ℕ) (hF : (F : ℝ) ≤ 2*T)
    {b : ℕ} {K : WExtractedKey} (hK : K ∈ wExtractedKeyBox (x^η))
    (j cap : Fin 5 → ℕ) {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊R*S⌋₊)
        a (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) :
    wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
      Real.sqrt (directJoinedMain κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a R S K F j cap) / T^2 ≤
    Real.sqrt (25165824*Couter*directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff) *
      x^(100*(κ+δ+ρ+η)) * (T^(5/4 : ℝ)*R^(7/4 : ℝ)*S^2/x) := by
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hMpos : 0 < M := by linarith
  have hTpos : 0 < T := by linarith
  have hZ : 1 ≤ x^η := Real.one_le_rpow hx1 hη
  have hQ : ∀ q ∈ Ioc 0 ⌊R*S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hA : 0 ≤ wBlockAmplitude K j := by unfold wBlockAmplitude; positivity
  have hLC : 0 ≤ directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff := by
    unfold directPayMainLossConstant
    positivity
  let L := directPayMainLoss κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a K F j
  have hL : 0 ≤ L := directPayMainLoss_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ hC hCa
  have henergy := directPayMain_energy_le κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x
    a R S K F j cap hκ hC hCa hCτ hCjoint hTpos.le hF
  have hAH : wBlockAmplitude K j * (2 : ℝ)^j 0 ≤ 32*x^η*T/x := by
    calc
      _ ≤ 8*(x^η)/M := directNormalization_floor_frequency_paid hMpos (by positivity) hN hQ ht
      _ = _ := by rw [hxMT]; field_simp; ring
  obtain ⟨hk, hr, hs⟩ := directLocalScale_fullLevel_coordinates hN
    (by positivity : 0 ≤ R*S) (by linarith) (by linarith) ht
  have hn := directPayMain_n_le hN hQ ht hNT
  have hDp := (directLocalScale_key_bounds (by positivity : 0 ≤ x^η) hK).2
  have hpaid := directPayMain_square_paid hA
    (show 0 ≤ Couter*x^ρ by positivity) hL (by positivity)
    (by positivity : 0 < (2 : ℝ)^j 1) (by positivity : 0 < (2 : ℝ)^j 2)
    (by positivity : 0 < (2 : ℝ)^j 3) (by positivity : 0 < (2 : ℝ)^j 4)
    (Nat.cast_nonneg K.D') hZ hT hR hS hxpos hAH hk hn hr hs hDp
  obtain ⟨hTx, hnx, hrx, hsx, hdx, hHx⟩ :=
    directPayMain_geometry hx hη hη1 hM hT hxMT hR hS hRS hN hNT hK ht
  have hal : (a.natAbs : ℝ) ≤ x := by simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
  have hLoss := directPayMain_loss_le κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff hx1 hκ hδ
    hC hCa a K F j hal hdx (hF.trans (by gcongr)) hnx hrx hsx hHx
  have hMass : directJoinedMass ρ Couter x T j =
      8*(Couter*x^ρ)*(2 : ℝ)^j 1*(2 : ℝ)^j 3*T := by unfold directJoinedMass; ring
  calc
    _ ≤ wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
        Real.sqrt (256*L*((2 : ℝ)^j 0)^2*((2 : ℝ)^j 2)^(3/2 : ℝ)*T^2*
          ((2 : ℝ)^j 3)^(3/2 : ℝ)*((2 : ℝ)^j 4)^3*
          ((K.D' : ℝ)+2*(2 : ℝ)^j 1/((2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2))) / T^2 := by
      gcongr
    _ = _ := directPayMain_root_identity hA (by rw [hMass]; positivity) (by positivity)
    _ ≤ Real.sqrt (25165824*(Couter*x^ρ)*L*(x^η)^7*T^(5/2 : ℝ)*R^(7/2 : ℝ)*S^4/x^2) := by
      apply Real.sqrt_le_sqrt
      simpa only [hMass] using hpaid
    _ ≤ Real.sqrt (25165824*(Couter*x^ρ)*
        (directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff*x^(4*ρ+14*δ+4*κ))*
        (x^η)^7*T^(5/2 : ℝ)*R^(7/2 : ℝ)*S^4/x^2) := by gcongr
    _ = Real.sqrt (25165824*Couter*directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff)*
        x^((ρ+(4*ρ+14*δ+4*κ)+7*η)/2)*(T^(5/4 : ℝ)*R^(7/4 : ℝ)*S^2/x) := by
      rw [directPayMain_global_square hCo hLC hxpos (by linarith) (by linarith),
        Real.sqrt_sq (by positivity)]
    _ ≤ _ := by
      gcongr
      linarith

/-- Uniform actual main-term bound. The positive constant is chosen before all
varying scales, arithmetic inputs, finite sets, keys, and block witnesses.
No energy, mass, logarithmic, or target-envelope assumption is present. -/
theorem directPayMain_uniform
    (κ δ ρ η Cnonzero Cτ Cjoint Ca Ccoeff Couter : ℝ)
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : 0 ≤ Cnonzero) (hCτ : 0 ≤ Cτ) (hCjoint : 0 ≤ Cjoint)
    (hCa : 0 ≤ Ca) (hCo : 0 ≤ Couter) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x M T R S : ℝ), 4 ≤ x → 1 ≤ M → 1 ≤ T → x = 4*M*T →
      1 ≤ R → 1 ≤ S → R*S ≤ x →
      ∀ (N : Finset ℕ), (∀ n ∈ N, 0 < n) → (∀ n ∈ N, (n : ℝ) ≤ 2*T) →
      ∀ (a : ℤ), |(a : ℝ)| ≤ x →
      ∀ (F : ℕ), (F : ℝ) ≤ 2*T →
      ∀ (b : ℕ) (K : WExtractedKey), K ∈ wExtractedKeyBox (x^η) →
      ∀ (j cap : Fin 5 → ℕ) (positive : Bool) (t : WExtractedTuple × ℤ),
      t ∈ wAnalyticDyadicBlock
        (wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊R*S⌋₊)
          a (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive →
      wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
        Real.sqrt (directJoinedMain κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a R S K F j cap) / T^2 ≤
        C*x^(100*(κ+δ+ρ+η))*(T^(5/4 : ℝ)*R^(7/4 : ℝ)*S^2/x) := by
  let C₀ := Real.sqrt (25165824*Couter*
    directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff)
  refine ⟨C₀+1, by dsimp [C₀]; positivity, ?_⟩
  intro x M T R S hx hM hT hxMT hR hS hRS N hN hNT a ha F hF b K hK j cap positive t ht
  have hh := directPayMain_bound κ δ ρ η Cnonzero Cτ Cjoint Ca Ccoeff Couter
    hκ hδ hρ hη hη1 hC hCτ hCjoint hCa hCo hx hM hT hxMT hR hS hRS
    hN hNT a ha F hF hK j cap ht
  apply hh.trans
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hRpos : 0 < R := by linarith
  change C₀ * _ * _ ≤ (C₀+1) * _ * _
  gcongr
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
