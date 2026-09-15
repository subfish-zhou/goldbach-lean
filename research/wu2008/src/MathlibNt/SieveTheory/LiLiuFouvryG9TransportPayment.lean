import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridCost
import MathlibNt.SieveTheory.LiLiuPrereqWFTransportAbsorption

noncomputable section
open Filter
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def g9TransportMu (δ η : ℝ) : ℝ := ((1/2-δ)*η^2)/4

theorem g9TransportMu_pos {δ η : ℝ} (hδ : δ < 1/2) (hη : 0 < η) :
    0 < g9TransportMu δ η := by unfold g9TransportMu; positivity

/-- The original external level, not a rescaled replacement, gives twice the required saving. -/
theorem g9Transport_internal_power {N T δ η : ℝ} (hN : 1 ≤ N)
    (hT : 1 ≤ T) (hTup : T ≤ N^(1/10 : ℝ)) (hδ : 0 ≤ δ)
    (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    N^(2*g9TransportMu δ η) ≤
      (externalInternalLevel (N^(5/9-δ)/T^(5/9 : ℝ)) η)^(η^2) := by
  have hN0 : 0 < N := by linarith
  have hb : 0 < 1+η+η^9 := by positivity
  have hbu : 1+η+η^9 ≤ 2 := by
    linarith [(external_dilation_bounds hη hηu).2.2]
  have hinv : (1/2 : ℝ) ≤ (1+η+η^9)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hb).2
    linarith
  have hexp : 2*g9TransportMu δ η ≤ (1/2-δ)*((1+η+η^9)⁻¹)*(η^2) := by
    have hh := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ (1/2-δ)*η^2 by positivity)
    dsimp [g9TransportMu]
    nlinarith
  calc
    _ ≤ N^((1/2-δ)*((1+η+η^9)⁻¹)*(η^2)) :=
      Real.rpow_le_rpow_of_exponent_le hN hexp
    _ = ((N^(1/2-δ))^((1+η+η^9)⁻¹))^(η^2) := by
      rw [Real.rpow_mul hN0.le, Real.rpow_mul hN0.le]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_rpow (by positivity) (g9WF_level_window hN hT hTup hδ).1
        (inv_nonneg.mpr hb.le)) (sq_nonneg η)

/-- Per-cell envelope, uniform over the whole occupied short-scale window. -/
theorem g9Transport_one {N : ℕ} {T δ η C : ℝ}
    (hN : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (hT : 1 ≤ T) (hTup : T ≤ (N : ℝ)^(1/10 : ℝ))
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hC : 0 ≤ C) :
    let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
    Real.exp (8*(η⁻¹)^3) * (C*(N : ℝ)^(1+g9TransportMu δ η)) *
      (4/(externalInternalLevel Q η)^(η^2)) * (1+Real.log (⌊Q⌋₊ : ℝ))^2 ≤
      (16*Real.exp (8*(η⁻¹)^3)*C) * (N : ℝ)^(1-g9TransportMu δ η) *
        Real.log (N : ℝ)^2 := by
  dsimp only
  let Q := (N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)
  let μ := g9TransportMu δ η
  have hN0 : 0 < (N : ℝ) := by linarith
  have hsave := g9Transport_internal_power hN hT hTup hδ hδu hη hηu
  have hp0 : 0 < (N : ℝ)^(2*μ) := Real.rpow_pos_of_pos hN0 _
  have hdiv : 4/(externalInternalLevel Q η)^(η^2) ≤ 4/(N : ℝ)^(2*μ) :=
    div_le_div_of_nonneg_left (by norm_num) hp0 hsave
  obtain ⟨hl0, hl⟩ := TransportAbsorption.floor_log_bound
    (g9WF_level_window hN hT hTup hδ).2 hlog
  have hsq : (1+Real.log (⌊Q⌋₊ : ℝ))^2 ≤ 4*Real.log (N : ℝ)^2 := by
    nlinarith [sq_nonneg (1+Real.log (⌊Q⌋₊ : ℝ)-2*Real.log (N : ℝ))]
  have heq : (N : ℝ)^(1+μ)/(N : ℝ)^(2*μ) = (N : ℝ)^(1-μ) := by
    rw [← Real.rpow_sub hN0]; congr 1; ring
  calc
    _ ≤ (Real.exp (8*(η⁻¹)^3)*(C*(N : ℝ)^(1+μ)) *
        (4/(N : ℝ)^(2*μ))) * (4*Real.log (N : ℝ)^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by positivity)) hsq
        (sq_nonneg _) (by positivity)
    _ = _ := by
      calc
        _ = (16*Real.exp (8*(η⁻¹)^3)*C) *
            ((N : ℝ)^(1+μ)/(N : ℝ)^(2*μ)) * Real.log (N : ℝ)^2 := by ring
        _ = _ := by rw [heq]

/-- Fixed constants and the positive power saving pay the five logarithms and any target A. -/
theorem g9Transport_eventually_envelope (K : ℝ) (A : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧
      K*x^(1-μ)*Real.log x^5 ≤ x/Real.log x^A := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    TransportAbsorption.eventually_log_power_budget K ((A+5 : ℕ) : ℝ) hμ]
    with x hx hb
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hl : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hl0 : 0 < Real.log x := by linarith
  rw [Real.rpow_natCast] at hb
  refine ⟨hx1, hl, (le_div_iff₀ (pow_pos hl0 A)).2 ?_⟩
  calc
    _ = (K*Real.log x^(A+5))*x^(1-μ) := by rw [pow_add]; ring
    _ ≤ x^μ*x^(1-μ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = x := by rw [← Real.rpow_add hx0, show μ+(1-μ) = 1 by ring, Real.rpow_one]

/-- Actual occupied-grid exceptional transport at the original external level.
The threshold precedes arbitrary eps and all cell scales. -/
theorem g9Transport_grid_log_payment (δ η ρ C : ℝ) (A : ℕ)
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ eps : ℝ,
      ∀ T : (ℕ × ℕ × ℕ) → ℝ,
      (∀ k ∈ fouvryG9GridUsed N eps ρ, 1 ≤ T k ∧ T k ≤ (N : ℝ)^(1/10 : ℝ)) →
      (∑ k ∈ fouvryG9GridUsed N eps ρ,
        let Q := (N : ℝ)^(5/9-δ)/(T k)^(5/9 : ℝ)
        Real.exp (8*(η⁻¹)^3) * (C*(N : ℝ)^(1+g9TransportMu δ η)) *
          (4/(externalInternalLevel Q η)^(η^2)) * (1+Real.log (⌊Q⌋₊ : ℝ))^2) ≤
        (N : ℝ)/Real.log (N : ℝ)^A := by
  let G : ℝ := (1/Real.log ρ+1)^3
  let B : ℝ := 16*Real.exp (8*(η⁻¹)^3)*C
  let μ := g9TransportMu δ η
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (g9Transport_eventually_envelope (G*B) A (g9TransportMu_pos hδu hη))
  refine ⟨⌈M⌉₊, ?_⟩
  intro N hN eps T hT
  have hMN : M ≤ (N : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast hN)
  obtain ⟨hN1,hlog,hpay⟩ := hM (N : ℝ) hMN
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ _k ∈ fouvryG9GridUsed N eps ρ,
        B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact g9Transport_one hN1 hlog (hT k hk).1 (hT k hk).2 hδ hδu hη hηu hC.le
    _ = ((fouvryG9GridUsed N eps ρ).card : ℝ) *
        (B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) := by simp
    _ ≤ (G*Real.log (N : ℝ)^3) *
        (B*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (fouvryG9GridCost_card hρ hlog) (by positivity)
    _ = (G*B)*(N : ℝ)^(1-μ)*Real.log (N : ℝ)^5 := by ring
    _ ≤ _ := hpay

end MathlibNt.SieveTheory.LiLiuPrereqWF
