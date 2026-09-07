import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainGrowth

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Only the arithmetic input is enlarged; all physical dyadic scales stay at x. -/
theorem directPayKMain_max_le {Cscale x : ℝ} (hscale : 1 ≤ Cscale) (hx : 1 ≤ x)
    (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (ha : (a.natAbs : ℝ) ≤ Cscale*x)
    (hd : (K.1.2.1 : ℝ) ≤ x) (hF : (F : ℝ) ≤ 2*x)
    (hn : (2 : ℝ)^j 2 ≤ 2*x) (hs : (2 : ℝ)^j 4 ≤ x)
    (hH : (2 : ℝ)^j 0 ≤ 32*x^7) :
    (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
      (2^(j 0+1)) (2^(j 4+1)) : ℝ) ≤ 3072*Cscale*x^12 := by
  have hx0 : 0 ≤ x := by linarith
  have hc0 : 0 ≤ Cscale := by linarith
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
    _ ≤ 2*(Cscale*x)*(32*x^7*2)*(2*x)*(6*x^2)*(x*2) := by gcongr
    _ = _ := by ring

/-- The first of the two arithmetic subpower losses at fixed multiplier Cscale. -/
theorem directPayKMain_abs_rpow_le {Cscale x δ : ℝ} (hscale : 1 ≤ Cscale)
    (hx : 0 ≤ x) (hδ : 0 ≤ δ) (a : ℤ) (ha : (a.natAbs : ℝ) ≤ Cscale*x) :
    (a.natAbs : ℝ)^δ ≤ Cscale^δ*x^δ := by
  calc
    _ ≤ (Cscale*x)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _) ha hδ
    _ = _ := Real.mul_rpow (by linarith) hx

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


-- Public declaration type and trust audit.
#check MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_max_le
#print axioms MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_max_le
#check MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_abs_rpow_le
#print axioms MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.directPayKMain_abs_rpow_le
