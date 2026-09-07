import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySeparatedCorrelation
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceBound

/-! Fixed orders, including zero, pay the actual cleaned and split coefficients.
Constants are chosen before every support, family, signed shift and scale. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_tau_subpower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ n : ℕ, (n : ℝ) ≤ X →
      (fouvryTau k n : ℝ) ≤ C * X ^ δ := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1, by norm_num, fun X hX n _ => ?_⟩
    have ht : (fouvryTau 0 n : ℝ) ≤ 1 := by
      by_cases hn : n = 1 <;> simp [fouvryTau, hn]
    simpa using ht.trans (Real.one_le_rpow hX hδ.le)
  · obtain ⟨C, hC, ht⟩ := fouvryTau_le_const_rpow (by omega : 1 ≤ k) hδ
    refine ⟨C, hC, fun X hX n hn => ?_⟩
    by_cases hn0 : n = 0
    · subst n
      simpa using (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) δ))
    · exact (ht n (Nat.pos_of_ne_zero hn0)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hn hδ.le) hC.le)

/-- This simultaneously pays beta, both original WF factors, and the actual
first modulus coefficient, whose order is twice the factor order. -/
theorem direct_fixedOrder_envelopes (k j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (N : Finset ℕ) (β γ ζ : ℕ → ℝ) (a : ℤ) (ξ : ℝ),
      (∀ n ∈ N, (n : ℝ) ≤ X) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau j n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau j n : ℝ)) →
      (∀ n ∈ N, |betaClean β a n| ≤ C * X ^ δ) ∧
      (∀ n : ℕ, (n : ℝ) ≤ X → |γ n| ≤ C * X ^ δ) ∧
      (∀ n : ℕ, (n : ℝ) ≤ X → |ζ n| ≤ C * X ^ δ) ∧
      (∀ n : ℕ, (n : ℝ) ≤ X →
        |factorConvolution γ (betaLowOmega ζ ξ) n| ≤ C * X ^ δ) := by
  obtain ⟨A, hA, hAt⟩ := direct_tau_subpower k hδ
  obtain ⟨B, hB, hBt⟩ := direct_tau_subpower j hδ
  obtain ⟨D, hD, hDt⟩ := direct_tau_subpower (j + j) hδ
  refine ⟨A + B + D, by positivity, ?_⟩
  intro X hX N β γ ζ a ξ hNX hβ hγ hζ
  have hp : 0 ≤ X ^ δ := Real.rpow_nonneg (by linarith) _
  have hCA : A * X ^ δ ≤ (A + B + D) * X ^ δ := by gcongr; linarith
  have hCB : B * X ^ δ ≤ (A + B + D) * X ^ δ := by gcongr; linarith
  have hCD : D * X ^ δ ≤ (A + B + D) * X ^ δ := by gcongr; linarith
  refine ⟨fun n hn => ((betaClean_abs_le_fouvryTau hβ a n hn).trans
    (hAt X hX n (hNX n hn))).trans hCA,
    fun n hn => ((hγ n).trans (hBt X hX n hn)).trans hCB,
    fun n hn => ((hζ n).trans (hBt X hX n hn)).trans hCB, ?_⟩
  intro n hn
  exact ((factorConvolution_abs_le j j γ (betaLowOmega ζ ξ) hγ
    (fun s => (abs_betaLowOmega_le ζ ξ s).trans (hζ s)) n).trans
      (hDt X hX n hn)).trans hCD

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
