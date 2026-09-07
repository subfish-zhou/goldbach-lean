import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainLocal

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The explicit arithmetic loss; this is not an input bound on the energy. -/
def directPayMainLoss (κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x : ℝ)
    (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) : ℝ :=
  ((Ccoeff*x^ρ)*(Ccoeff*x^ρ))^2 * (Cnonzero * (Ca * (a.natAbs : ℝ)^δ)) *
    (16*(2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2)^κ *
    Real.sqrt (Cτ*Cjoint) *
    (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
      (2^(j 0+1)) (2^(j 4+1)) : ℝ)^δ *
    Real.sqrt (1+Real.log ((2 : ℝ)^(j 4+1)))

theorem directPayMainLoss_nonneg (κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x : ℝ)
    (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (hC : 0 ≤ Cnonzero) (hCa : 0 ≤ Ca) :
    0 ≤ directPayMainLoss κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a K F j := by
  unfold directPayMainLoss
  positivity

/-- The literal joint mean pays the entire coefficient-pair length using F≤2T. -/
theorem directPayMain_mean_le (δ Cτ Cjoint : ℝ) (a : ℤ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) {T : ℝ}
    (hCτ : 0 ≤ Cτ) (hCjoint : 0 ≤ Cjoint) (_hT : 0 ≤ T) (hF : (F : ℝ) ≤ 2*T) :
    wGramMainJointMean δ Cτ Cjoint a K F j ≤
      64 * (2 : ℝ)^j 3 * (2 : ℝ)^j 2 * T^2 * ((2 : ℝ)^j 4)^2 *
        ((2 : ℝ)^j 0)^2 * Real.sqrt (Cτ*Cjoint) *
        (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
          (2^(j 0+1)) (2^(j 4+1)) : ℝ)^δ *
        Real.sqrt (1+Real.log ((2 : ℝ)^(j 4+1))) := by
  rw [directPayMain_mean_eq δ Cτ Cjoint a K F j hCτ hCjoint]
  have hm : (F/K.1.1 : ℕ) ≤ F := Nat.div_le_self _ _
  have hm' : ((F/K.1.1 : ℕ) : ℝ) ≤ 2*T := (Nat.cast_le.mpr hm).trans hF
  have hr : ((2^(j 3+1)-1 : ℕ) : ℝ) ≤ 2*(2 : ℝ)^j 3 := by
    have hh := Nat.cast_le (α := ℝ).mpr (Nat.sub_le (2^(j 3+1)) 1)
    push_cast at hh
    simpa only [pow_succ, mul_comm] using hh
  calc
    _ ≤ (2*(2 : ℝ)^j 3) *
      ((2 : ℝ)^(j 2+1) * (2*T)^2 * ((2 : ℝ)^(j 4+1))^2 *
        ((2 : ℝ)^j 0)^2 * Real.sqrt (Cτ*Cjoint) *
        (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
          (2^(j 0+1)) (2^(j 4+1)) : ℝ)^δ *
        Real.sqrt (1+Real.log ((2 : ℝ)^(j 4+1)))) := by gcongr
    _ = _ := by simp only [pow_succ]; ring

/-- The q^(1/2+κ) factor is genuinely split, retaining q^κ in the explicit loss. -/
theorem directPayMain_qpow (κ : ℝ) (hκ : 0 ≤ κ) (j : Fin 5 → ℕ) :
    ((2^(j 2+1)*(2^(j 3+1)-1)*2^(j 4+1)*2^(j 4+1) : ℕ) : ℝ)^(1/2+κ : ℝ) ≤
    4 * ((2 : ℝ)^j 2)^(1/2 : ℝ) * ((2 : ℝ)^j 3)^(1/2 : ℝ) * (2 : ℝ)^j 4 *
      (16*(2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2)^κ := by
  calc
    _ ≤ (16*(2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2)^(1/2+κ : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (directPayMain_modulus j) (by linarith)
    _ = _ := by
      rw [Real.rpow_add (by positivity)]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by positivity)]
      norm_num
      simp [Real.sqrt_eq_rpow]

/-- Fully expanded actual energy. Both completion terms remain visible. -/
theorem directPayMain_energy_le (κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x : ℝ)
    (a : ℤ) (R S : ℝ) (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ)
    {T : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ Cnonzero) (hCa : 0 ≤ Ca)
    (hCτ : 0 ≤ Cτ) (hCjoint : 0 ≤ Cjoint) (hT : 0 ≤ T) (hF : (F : ℝ) ≤ 2*T) :
    directJoinedMain κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a R S K F j cap ≤
      256 * directPayMainLoss κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a K F j *
      ((2 : ℝ)^j 0)^2 * ((2 : ℝ)^j 2)^(3/2 : ℝ) * T^2 *
      ((2 : ℝ)^j 3)^(3/2 : ℝ) * ((2 : ℝ)^j 4)^3 *
      ((K.D' : ℝ) + 2*(2 : ℝ)^j 1 /
        ((2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2)) := by
  have hlen : ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap+1 : ℕ) : ℝ) /
      ((2^j 2*2^j 3*2^j 4*2^j 4 : ℕ) : ℝ)) ≤
      (K.D' : ℝ) + 2*(2 : ℝ)^j 1 /
        ((2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2) := by
    have hh := div_le_div_of_nonneg_right (directPayMain_span R S K j cap)
      (show 0 ≤ ((2^j 2*2^j 3*2^j 4*2^j 4 : ℕ) : ℝ) by positivity)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_two, mul_assoc,
      add_comm] using add_le_add_right hh (K.D' : ℝ)
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left
      (mul_le_mul
        (mul_le_mul_of_nonneg_left hlen (show 0 ≤ Cnonzero * (Ca * (a.natAbs : ℝ)^δ) by positivity))
        (directPayMain_qpow κ hκ j) (by positivity) (by positivity))
      (sq_nonneg ((Ccoeff*x^ρ)*(Ccoeff*x^ρ))))
    (directPayMain_mean_le δ Cτ Cjoint a K F j hCτ hCjoint hT hF)
    (wGramMainJointMean_nonneg δ Cτ Cjoint a K F j) (by positivity)
  unfold directJoinedMain wGramDirectMainSubpowerFactor
  apply hh.trans_eq
  unfold directPayMainLoss
  rw [show (3/2 : ℝ) = (1/2 : ℝ)+1 by norm_num,
    Real.rpow_add (by positivity : 0 < (2 : ℝ)^j 2),
    Real.rpow_add (by positivity : 0 < (2 : ℝ)^j 3), Real.rpow_one, Real.rpow_one]
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
