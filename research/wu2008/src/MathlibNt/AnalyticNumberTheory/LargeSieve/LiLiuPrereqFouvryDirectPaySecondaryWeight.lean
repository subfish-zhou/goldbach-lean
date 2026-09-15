import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryGeometry

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Genuine payment of all residual arithmetic factors. -/
theorem directPaySecondary_weight_paid
    {κ δ ρ C Csec Ccoeff : ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (hC : 0 ≤ C) (hCsec : 0 ≤ Csec) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ (x : ℝ), 1 ≤ x → ∀ (a : ℤ)
      (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ),
      |(a : ℝ)| ≤ x → (2 : ℝ) ^ j 0 ≤ 8 * x ^ (6 : ℕ) →
      (wGramSecondaryNumeratorMax a K F j : ℝ) ≤ 16 * x ^ (9 : ℕ) →
      16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4 ≤
        16 * x ^ (4 : ℕ) →
      directPaySecondaryWeight κ δ ρ C Csec Ccoeff x a K F j ≤
        Cw * x ^ (4 * ρ + 4 * κ + 11 * δ) := by
  obtain ⟨Ca, hCa, htau⟩ := directPaySecondary_tau hδ
  let B := C * Ccoeff ^ 4 * (1 + Real.log 16 + 6 / δ) * Ca *
    (16 : ℝ) ^ κ * (Csec + 1) * (16 : ℝ) ^ δ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + 1, by positivity, ?_⟩
  intro x hx a K F j ha hH hA hq
  have hx0 : 0 < x := by linarith
  have hlog := directPaySecondary_log hδ hx (by positivity) hH
  have ht := htau x hx a ha
  have hqpow : (16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 *
      (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4) ^ κ ≤ (16 : ℝ) ^ κ * x ^ (4 * κ) := by
    calc
      _ ≤ (16 * x ^ (4 : ℕ)) ^ κ := Real.rpow_le_rpow (by positivity) hq hκ
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hx0.le]
        norm_num
  have hApow : (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ ≤
      (16 : ℝ) ^ δ * x ^ (9 * δ) := by
    calc
      _ ≤ (16 * x ^ (9 : ℕ)) ^ δ := Real.rpow_le_rpow (by positivity) hA hδ.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hx0.le]
        norm_num
  have hlarge : 1 ≤ (16 : ℝ) ^ δ * x ^ (9 * δ) := by
    have h1 := Real.one_le_rpow (show (1 : ℝ) ≤ 16 by norm_num) hδ.le
    have h2 := Real.one_le_rpow hx (show 0 ≤ 9 * δ by positivity)
    nlinarith
  have hroot : Real.sqrt (Csec * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ) ≤
      (Csec + 1) * ((16 : ℝ) ^ δ * x ^ (9 * δ)) := by
    calc
      _ ≤ Real.sqrt (Csec * ((16 : ℝ) ^ δ * x ^ (9 * δ))) := by gcongr
      _ = Real.sqrt Csec * Real.sqrt ((16 : ℝ) ^ δ * x ^ (9 * δ)) := Real.sqrt_mul hCsec _
      _ ≤ (Csec + 1) * ((16 : ℝ) ^ δ * x ^ (9 * δ)) := by
        apply mul_le_mul
        · apply (Real.sqrt_le_left (by positivity)).2
          nlinarith
        · exact Real.sqrt_le_self_iff.mpr (Or.inr hlarge)
        · positivity
        · positivity
  have hcoeff : (Ccoeff * x ^ ρ) ^ 4 = Ccoeff ^ 4 * x ^ (4 * ρ) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ρ) 4, ← Real.rpow_mul hx0.le]
    congr 2
    ring
  unfold directPaySecondaryWeight
  rw [hcoeff]
  calc
    _ ≤ C * (Ccoeff ^ 4 * x ^ (4 * ρ)) *
        ((1 + Real.log 16 + 6 / δ) * x ^ δ) * (Ca * x ^ δ) *
        ((16 : ℝ) ^ κ * x ^ (4 * κ)) *
        ((Csec + 1) * ((16 : ℝ) ^ δ * x ^ (9 * δ))) := by
      gcongr
    _ = B * x ^ (4 * ρ + 4 * κ + 11 * δ) := by
      dsimp [B]
      rw [show 4 * ρ + 4 * κ + 11 * δ = 4 * ρ + δ + δ + 4 * κ + 9 * δ by ring]
      simp only [Real.rpow_add hx0]
      ring
    _ ≤ (B + 1) * x ^ (4 * ρ + 4 * κ + 11 * δ) := by gcongr; linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
