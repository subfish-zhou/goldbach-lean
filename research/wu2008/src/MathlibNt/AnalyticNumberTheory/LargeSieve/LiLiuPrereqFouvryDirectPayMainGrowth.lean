import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainEnergy

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Extract the upper n-scale from the actual block, not from a replacement n=T. -/
theorem directPayMain_n_le
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ T : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock (wExtractedKeyFiber H N Q a P R S ξ b K) j positive)
    (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2*T) : (2 : ℝ)^j 2 ≤ 2*T := by
  exact (wAnalyticDyadicBlock_bounds hN hQ ht 2).1.trans
    (direct_outer_n_le hN hQ (mem_filter.mp ht).1 hNT).2

/-- Actual floor geometry gives a polynomial cap for every arithmetic loss argument. -/
theorem directPayMain_geometry
    {x η M T R S : ℝ} (hx : 4 ≤ x) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hxMT : x = 4*M*T)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hRS : R*S ≤ x)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2*T)
    {a : ℤ} {b : ℕ} {K : WExtractedKey} (hK : K ∈ wExtractedKeyBox (x^η))
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊R*S⌋₊)
        a (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) :
    T ≤ x ∧ (2 : ℝ)^j 2 ≤ 2*x ∧ (2 : ℝ)^j 3 ≤ x ∧
      (2 : ℝ)^j 4 ≤ x ∧ (K.1.2.1 : ℝ) ≤ x ∧ (2 : ℝ)^j 0 ≤ 32*x^7 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hM0 : 0 < M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hZ0 : 0 ≤ x^η := Real.rpow_nonneg hx0 η
  have hZ : x^η ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hη1
  have hQ : ∀ q ∈ Ioc 0 ⌊R*S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hTx : T ≤ x := by nlinarith
  obtain ⟨hk, hr, hs⟩ := directLocalScale_fullLevel_coordinates hN
    (by positivity : 0 ≤ R*S) (by linarith) (by linarith) ht
  have hRx : R ≤ x := (le_mul_of_one_le_right (by linarith) hS).trans hRS
  have hSx : S ≤ x := (le_mul_of_one_le_left (by linarith) hR).trans hRS
  have hnx := (directPayMain_n_le hN hQ ht hNT).trans (by gcongr : 2*T ≤ 2*x)
  have hd := (directLocalScale_key_bounds hZ0 hK).1
  have hd' : (K.D : ℝ) ≤ x^3 := hd.trans (by gcongr)
  have hkey : (K.1.2.1 : ℝ) ≤ x :=
    ((Nat.cast_le.mpr (mem_wExtractedKeyBox_iff.mp hK).2.1).trans (Nat.floor_le hZ0)).trans hZ
  refine ⟨hTx, hnx, hr.trans hRx, hs.trans hSx, hkey, ?_⟩
  have hf := directLocalScale_floor_frequency_le hM0 hZ0 hN hQ ht
  calc
    _ ≤ 8*((K.D : ℝ)*2^j 1*2^j 3*2^j 4)/M*(x^η) := hf
    _ ≤ 8*(x^3*x*x*x)/1*x := by
      gcongr
      · exact hk.trans hRS
      · exact hr.trans hRx
      · exact hs.trans hSx
    _ ≤ 32*x^7 := by nlinarith [show 0 ≤ x^7 by positivity]

/-- A concrete cap for the actual joint-arithmetic maximum. -/
theorem directPayMain_max_le {x : ℝ} (hx : 1 ≤ x) (a : ℤ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) (ha : (a.natAbs : ℝ) ≤ x)
    (hd : (K.1.2.1 : ℝ) ≤ x) (hF : (F : ℝ) ≤ 2*x)
    (hn : (2 : ℝ)^j 2 ≤ 2*x) (hs : (2 : ℝ)^j 4 ≤ x)
    (hH : (2 : ℝ)^j 0 ≤ 32*x^7) :
    (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
      (2^(j 0+1)) (2^(j 4+1)) : ℝ) ≤ 3072*x^12 := by
  have hx0 : 0 ≤ x := by linarith
  have hm : ((F/K.1.1 : ℕ) : ℝ) ≤ 2*x :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans hF
  have hsum : (K.1.2.1 : ℝ) * ((2 : ℝ)^j 2*2) + ((F/K.1.1 : ℕ) : ℝ) ≤ 6*x^2 := by
    calc
      _ ≤ x*(2*x*2)+2*x := by gcongr
      _ ≤ _ := by nlinarith
  unfold mainRestrictedMax
  push_cast
  simp only [pow_succ]
  calc
    _ ≤ 2*x*(32*x^7*2)*(2*x)*(6*x^2)*(x*2) := by gcongr
    _ = _ := by ring

/-- Logarithm is paid with an arbitrary positive divisor exponent. -/
theorem directPayMain_log_le {x s δ : ℝ} (hx : 1 ≤ x) (hs : 1 ≤ s)
    (hsx : s ≤ x) (hδ : 0 < δ) :
    Real.sqrt (1+Real.log (2*s)) ≤ (1+2^δ/δ)*x^δ := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 < s := by linarith
  have hlog : 0 ≤ Real.log (2*s) := Real.log_nonneg (by linarith)
  have hlog' : Real.log (2*s) ≤ (2*x)^δ/δ :=
    (Real.log_le_rpow_div (by positivity) hδ).trans (by gcongr)
  have hpow : 1 ≤ x^δ := Real.one_le_rpow hx hδ.le
  calc
    _ ≤ 1+Real.log (2*s) := by
      apply (Real.sqrt_le_left (by linarith)).2
      nlinarith [sq_nonneg (Real.log (2*s))]
    _ ≤ x^δ+(2*x)^δ/δ := add_le_add hpow hlog'
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0]; ring

/-- Uniform fixed constant for the complete arithmetic loss. -/
def directPayMainLossConstant (κ δ Cnonzero Cτ Cjoint Ca Ccoeff : ℝ) : ℝ :=
  Ccoeff^4 * Cnonzero * Ca * 32^κ * Real.sqrt (Cτ*Cjoint) * 3072^δ * (1+2^δ/δ)

/-- The true q^κ, joint maximum subpower and logarithmic root are all paid. -/
theorem directPayMain_loss_le (κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff : ℝ)
    {x : ℝ} (hx : 1 ≤ x) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (hC : 0 ≤ Cnonzero) (hCa : 0 ≤ Ca)
    (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (ha : (a.natAbs : ℝ) ≤ x) (hd : (K.1.2.1 : ℝ) ≤ x) (hF : (F : ℝ) ≤ 2*x)
    (hn : (2 : ℝ)^j 2 ≤ 2*x) (hr : (2 : ℝ)^j 3 ≤ x)
    (hs : (2 : ℝ)^j 4 ≤ x) (hH : (2 : ℝ)^j 0 ≤ 32*x^7) :
    directPayMainLoss κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a K F j ≤
      directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff * x^(4*ρ+14*δ+4*κ) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hq : 16*(2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2 ≤ 32*x^4 := by
    calc
      _ ≤ 16*(2*x)*x*x^2 := by gcongr
      _ = _ := by ring
  have hqpow := Real.rpow_le_rpow (by positivity) hq hκ
  have hmax := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (directPayMain_max_le hx a K F j ha hd hF hn hs hH) hδ.le
  have hal := Real.rpow_le_rpow (Nat.cast_nonneg _) ha hδ.le
  have hlog := directPayMain_log_le hx (one_le_pow₀ (by norm_num)) hs hδ
  rw [show 2*(2 : ℝ)^j 4 = (2 : ℝ)^(j 4+1) by rw [pow_succ]; ring] at hlog
  unfold directPayMainLoss
  calc
    _ ≤ ((Ccoeff*x^ρ)*(Ccoeff*x^ρ))^2 * (Cnonzero*(Ca*x^δ)) *
      (32*x^4)^κ * Real.sqrt (Cτ*Cjoint) * (3072*x^12)^δ *
      ((1+2^δ/δ)*x^δ) := by gcongr
    _ = _ := by
      unfold directPayMainLossConstant
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3072) (by positivity),
        ← Real.rpow_natCast_mul hx0 4 κ, ← Real.rpow_natCast_mul hx0 12 δ]
      have he : 4*ρ+14*δ+4*κ = ρ*4+δ+4*κ+12*δ+δ := by ring
      rw [he, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_add hxpos,
        Real.rpow_add hxpos, Real.rpow_mul hx0 ρ 4]
      norm_num only [Nat.cast_ofNat, Real.rpow_ofNat]
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
