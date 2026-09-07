import MathlibNt.SieveTheory.LiLiuGoldbachJRLowerLipschitz
import MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinate

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open JurkatRichert1965ChenGammaOneQOne LiLiuPrereqWF.CoordinateShift

/-- The ideal coordinate retains the actual product, before prime-pair quadrature. -/
noncomputable def goldbachPairIdealWeight (N : ℕ) (ρ : ℝ) (m : ℕ) : ℝ :=
  max 0 (jr1965f ((1/2 - Real.log (m : ℝ)/Real.log (N : ℝ))/(4/53 : ℝ)) - ρ) /
    (Nat.totient m : ℝ)

noncomputable def goldbachPairIdealSum (N : ℕ) (ρ : ℝ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ a ∈ T, goldbachPairIdealWeight N ρ (a.1*a.2)

/-- Uniform transport of a nonnegative clipped lower kernel, including crossings of two. -/
theorem goldbachPair_ideal_clip_eventually (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) →
      max 0 (jr1965f ((1/2 - Real.log (m : ℝ)/Real.log (N : ℝ))/(4/53 : ℝ)) - 2*ρ) ≤
        max 0 (jr1965f (Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
          Real.log ((N : ℝ)^(4/53 : ℝ))) - ρ) := by
  have hL : 0 < jr1965DelayConstant/2 := div_pos delayConstant_pos (by norm_num)
  obtain ⟨N₀, hN₀, hn⟩ := exists_pairLayer_coordinate_threshold B
    (ρ/(jr1965DelayConstant/2)) hB (div_pos hρ hL)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN m hm hmu
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := (hn N hN m hm hmu).2
  have hf := LiLiuGoldbachJRLowerLipschitz.lower_le_add_abs
    (Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
      ((4/53 : ℝ)*Real.log (N : ℝ)))
    ((1/2 - Real.log (m : ℝ)/Real.log (N : ℝ))/(4/53 : ℝ))
  have herr : jr1965DelayConstant/2 *
      |Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
        ((4/53 : ℝ)*Real.log (N : ℝ)) -
        (1/2 - Real.log (m : ℝ)/Real.log (N : ℝ))/(4/53 : ℝ)| < ρ := by
    calc
      _ < jr1965DelayConstant/2 * (ρ/(jr1965DelayConstant/2)) :=
        mul_lt_mul_of_pos_left hc hL
      _ = ρ := by rw [mul_comm, div_mul_cancel₀ _ hL.ne']
  rw [Real.log_rpow hNp]
  exact max_le_max_left 0 (by linarith)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
