import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9Scale

noncomputable section
open Filter
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original G9 level has positive power growth when delta is strictly below 1/2. -/
theorem g9WF_level_window {N T δ : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hTup : T ≤ N^(1/10 : ℝ)) (hδ : 0 ≤ δ) :
    N^(1/2-δ) ≤ N^(5/9-δ)/T^(5/9 : ℝ) ∧ N^(5/9-δ)/T^(5/9 : ℝ) ≤ N := by
  have hN0 : 0 < N := by linarith
  have hT0 : 0 < T := by linarith
  have hp : T^(5/9 : ℝ) ≤ N^(1/18 : ℝ) := by
    have h := Real.rpow_le_rpow hT0.le hTup (show (0 : ℝ) ≤ 5/9 by norm_num)
    norm_num [← Real.rpow_mul hN0.le] at h ⊢
    exact h
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 _)).2
    calc
      _ ≤ N^(1/2-δ)*N^(1/18 : ℝ) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  · have hd : 1 ≤ T^(5/9 : ℝ) := Real.one_le_rpow hT (by norm_num)
    have hn : N^(5/9-δ) ≤ N := by
      calc
        _ ≤ N^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = N := Real.rpow_one N
    exact (div_le_self (Real.rpow_nonneg hN0.le _) hd).trans hn

/-- A threshold before every short scale pays the actual internal-level gate.
The strict delta cap is needed for positive growth; no endpoint delta=1/2 claim. -/
theorem g9WF_exists_internal_level_gate {δ η : ℝ} (hδ : 0 ≤ δ) (hδu : δ < 1/2)
    (hη : 0 < η) (Q₀ : ℝ) :
    ∃ N₀ : ℝ, ∀ N T : ℝ, N₀ ≤ N → 1 ≤ T → T ≤ N^(1/10 : ℝ) →
      let Q := N^(5/9-δ)/T^(5/9 : ℝ)
      1 ≤ N ∧ 1 ≤ Q ∧ Q₀ ≤ Q ∧ 2 ≤ externalInternalLevel Q η ∧ Q ≤ N := by
  let b : ℝ := 1+η+η^9
  have hb : 0 < b := by dsimp [b]; positivity
  let C : ℝ := max Q₀ (2^b)
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le C 0 (1/2-δ) (by linarith))
  refine ⟨max 1 N₁, ?_⟩
  intro N T hN hT hTup
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hC : C ≤ N^(1/2-δ) := by simpa using h₁ N ((le_max_right _ _).trans hN)
  obtain ⟨hlo,hhi⟩ := g9WF_level_window hN1 hT hTup hδ
  have hQ1 : 1 ≤ N^(5/9-δ)/T^(5/9 : ℝ) :=
    (Real.one_le_rpow hN1 (by linarith : 0 ≤ 1/2-δ)).trans hlo
  refine ⟨hN1,hQ1,(le_max_left _ _).trans (hC.trans hlo),?_,hhi⟩
  unfold externalInternalLevel
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) b)
    ((le_max_right _ _).trans (hC.trans hlo)) (inv_nonneg.mpr hb.le)
  have heq : ((2 : ℝ)^b)^(b⁻¹) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv_cancel₀ hb.ne', Real.rpow_one]
  simpa only [heq] using hpow

end MathlibNt.SieveTheory.LiLiuPrereqWF
