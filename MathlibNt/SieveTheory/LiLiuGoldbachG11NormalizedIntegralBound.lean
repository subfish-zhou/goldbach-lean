import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope

open Set LiLiuPrereqBuchstab
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- The loss is selected before all later sieve constants. It is not an assumption
on the target bound; all analytic error terms are absorbed for every fixed B,C. -/
theorem goldbachG11NormalizedIntegral_envelope (W δ : ℝ) (hW0 : 0 ≤ W) (hδ : 0 < δ)
    (hW : ∀ u ∈ Icc (17 / 4 : ℝ) (37 / 4), buchstab u ≤ W) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ B C : ℝ, 0 ≤ B →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
        goldbachG11BuchstabSieveEnvelope N (goldbachG11SieveCutoff B N) 3 C
            (τ * Real.exp Real.eulerMascheroniConstant) τ ≤
          (8*W*goldbachG11PrimeIntegral (fun _ => 1)+δ) *
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨τ,hτ,hτ1,hcoeff⟩ := goldbachG11NormalizedIntegral_choose_loss W (δ/2) (by positivity)
  refine ⟨τ,hτ,hτ1,?_⟩
  intro B C hB
  obtain ⟨N₀,hN₀,hbound⟩ := goldbachG11NormalizedIntegral_envelope_loss
    B C τ τ τ (δ/6) W hB hτ hτ1 hτ hτ (by positivity) hW0 hW
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  have hM : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _)) (sq_nonneg _)
  exact (hbound N hN hEven).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hcoeff]) hM)

/-- Actual G11, uniform in every nonnegative window epsilon. The only optional
input is a scalar raw Buchstab majorant on [17/4,37/4]. -/
theorem goldbachWeightG11_le_normalizedIntegral (W δ : ℝ) (hW0 : 0 ≤ W) (hδ : 0 < δ)
    (hW : ∀ u ∈ Icc (17 / 4 : ℝ) (37 / 4), buchstab u ≤ W) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        (8*W*goldbachG11PrimeIntegral (fun _ => 1)+δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨τ,hτ,_,henv⟩ := goldbachG11NormalizedIntegral_envelope W (δ/2) hW0 (by positivity) hW
  obtain ⟨B,C,hB,_,K,hK,hactual⟩ := goldbachWeightG11_le_concreteBuchstabSieve
    3 (τ*Real.exp Real.eulerMascheroniConstant) (δ/2) τ
    (by norm_num) (mul_pos hτ (Real.exp_pos _)) (by positivity) hτ
  obtain ⟨L,_,hbound⟩ := henv B C hB.le
  refine ⟨max K L,by omega,?_⟩
  intro N hN hEven ε hε
  have ha := hactual N (by omega) hEven ε hε
  have hb := hbound N (by omega) hEven
  linarith only [ha,hb]

/-- Unconditional W=1 closure. This is not the paper's sharper low-band bound
and makes no assertion about final D19 positivity. -/
theorem goldbachWeightG11_le_normalizedIntegral_one (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        (8*goldbachG11PrimeIntegral (fun _ => 1)+δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  simpa only [mul_one] using goldbachWeightG11_le_normalizedIntegral 1 δ zero_le_one hδ
    (fun _ hu => buchstab_le_one (by linarith [hu.1]))

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig