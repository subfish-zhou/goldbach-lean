import PositiveHActual

namespace PositiveH
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- Half the paid logarithmic gain leaves a uniform positive error budget. -/
def lowerCorrection (s : ℝ) : ℝ := (1/20000)*log (2/(s-1))

theorem lowerCorrection_pos {s : ℝ} (hs : 1 < s) (hs3 : s < 3) :
    0 < lowerCorrection s := by
  apply mul_pos (by norm_num)
  exact log_pos ((one_lt_div (by linarith)).mpr (by linarith))

theorem lowerCorrection_uniform {s : ℝ} (hs : 2 ≤ s) (hsmax : s ≤ 29/10) :
    (1/20000)*log (20/19) ≤ lowerCorrection s := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/20000)
  apply log_le_log (by norm_num)
  apply (le_div_iff₀ (by linarith : 0 < s-1)).mpr
  linarith

/-- Actual positive lower improvement on every original box. No limiting
family or unproved target-shaped correction hypothesis is assumed. -/
theorem original_strict_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      (log (s-1)+lowerCorrection s)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s ∧
      log (s-1)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) <
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  have he : 0 < (1/20000 : ℝ)*log (20/19) :=
    mul_pos (by norm_num) (log_pos (by norm_num))
  obtain ⟨T,hT,hbound⟩ := original_lower hδ hδhi he
  refine ⟨T,hT,?_⟩
  intro N hN heven Δ hlo hhi V hV hr s hs hsmax
  obtain ⟨hθ,hp⟩ := hbound N hN heven Δ hlo hhi V hV hr s hs hsmax
  have hb := mul_le_mul_of_nonneg_right (lowerCorrection_uniform hs hsmax) hθ.le
  have hc := lowerCorrection_pos (by linarith : 1 < s) (by linarith : s < 3)
  have hu : (log (s-1)+lowerCorrection s)*
      boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
    dsimp [lowerCorrection] at hb ⊢
    nlinarith only [hp,hb]
  refine ⟨hθ,hu,?_⟩
  nlinarith only [hu,mul_pos hc hθ]

end
end PositiveH
