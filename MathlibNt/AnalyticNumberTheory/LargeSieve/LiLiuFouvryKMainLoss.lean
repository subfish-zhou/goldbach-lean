import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKMainGrowth

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Two and only two arithmetic powers of the fixed multiplier are charged. -/
theorem directPayKMain_loss_le (Cscale κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff : ℝ)
    (hscale : 1 ≤ Cscale) {x : ℝ} (hx : 1 ≤ x) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (hC : 0 ≤ Cnonzero) (hCa : 0 ≤ Ca)
    (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (ha : (a.natAbs : ℝ) ≤ Cscale*x) (hd : (K.1.2.1 : ℝ) ≤ x)
    (hF : (F : ℝ) ≤ 2*x) (hn : (2 : ℝ)^j 2 ≤ 2*x)
    (hr : (2 : ℝ)^j 3 ≤ x) (hs : (2 : ℝ)^j 4 ≤ x)
    (hH : (2 : ℝ)^j 0 ≤ 32*x^7) :
    directPayMainLoss κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x a K F j ≤
      (directPayMainLossConstant κ δ Cnonzero Cτ Cjoint Ca Ccoeff*Cscale^(2*δ)) *
        x^(4*ρ+14*δ+4*κ) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hc0 : 0 ≤ Cscale := by linarith
  have hcpos : 0 < Cscale := by linarith
  have hq : 16*(2 : ℝ)^j 2*(2 : ℝ)^j 3*((2 : ℝ)^j 4)^2 ≤ 32*x^4 := by
    calc
      _ ≤ 16*(2*x)*x*x^2 := by gcongr
      _ = _ := by ring
  have hqpow := Real.rpow_le_rpow (by positivity) hq hκ
  have hmax := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (directPayKMain_max_le hscale hx a K F j ha hd hF hn hs hH) hδ.le
  have hal := directPayKMain_abs_rpow_le hscale hx0 hδ.le a ha
  have hlog := directPayMain_log_le hx (one_le_pow₀ (by norm_num)) hs hδ
  rw [show 2*(2 : ℝ)^j 4 = (2 : ℝ)^(j 4+1) by rw [pow_succ]; ring] at hlog
  unfold directPayMainLoss
  calc
    _ ≤ ((Ccoeff*x^ρ)*(Ccoeff*x^ρ))^2 * (Cnonzero*(Ca*(Cscale^δ*x^δ))) *
      (32*x^4)^κ * Real.sqrt (Cτ*Cjoint) * (3072*Cscale*x^12)^δ *
      ((1+2^δ/δ)*x^δ) := by gcongr
    _ = _ := by
      unfold directPayMainLossConstant
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity),
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 3072*Cscale) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3072) hc0,
        ← Real.rpow_natCast_mul hx0 4 κ, ← Real.rpow_natCast_mul hx0 12 δ,
        show 2*δ = δ+δ by ring, Real.rpow_add hcpos]
      have he : 4*ρ+14*δ+4*κ = ρ*4+δ+4*κ+12*δ+δ := by ring
      rw [he, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_add hxpos,
        Real.rpow_add hxpos, Real.rpow_mul hx0 ρ 4]
      norm_num only [Nat.cast_ofNat, Real.rpow_ofNat]
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


-- Public declaration type and trust audit.
#check MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_loss_le
#print axioms MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_loss_le
