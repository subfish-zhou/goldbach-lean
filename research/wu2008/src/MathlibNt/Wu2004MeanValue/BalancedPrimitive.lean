import MathlibNt.Wu2004MeanValue.BalancedLowSource
import MathlibNt.Wu2004MeanValue.CommonPrimitive

/-! The low/high conductor split for a common balanced prime profile. -/

namespace Wu2004MeanValue
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators Topology
noncomputable section

theorem balanced_commonPrimitiveSource_log_saving_of_split (A b eta : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (hAb : A + 6 ≤ b) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ (h Q L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      1 ≤ h → h ≤ x →
      (U : ℝ) ≤ (x : ℝ) ^ (1 - eta) →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ b →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ m ∈ Ioc L U, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      commonPrimitiveSource f r h Q L U ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨C₁, hC₁, N₁, hlow⟩ :=
    balanced_low_source_real_moving A b eta 1 hA hb heta (by norm_num)
  obtain ⟨C₂, hC₂, hhigh⟩ := chosen_high_source_real_moving_profile_log_saving
  obtain ⟨N₂, hhigh⟩ := hhigh b eta hb heta
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hpay := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (A + 2) (show (0 : ℝ) < 2 by norm_num)).bound
      (show (0 : ℝ) < 1 by norm_num))
  refine ⟨C₁ + C₂ + 6984, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlog, hpay, eventually_ge_atTop (max 1 (max N₁ N₂))]
    with x hlog hpay hx
  intro h Q L U f r hh hhx hU hQ hL hf hr
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : N₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx₂ : N₂ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0 : ℝ) < x := by positivity
  have hlog0 : 0 < Real.log (x : ℝ) := by linarith
  have hlogA : 0 < Real.log (x : ℝ) ^ A := Real.rpow_pos_of_pos hlog0 A
  have hS : ∀ m ∈ Ioc L U, 1 ≤ m ∧ (m : ℝ) ≤ (x : ℝ) ^ (1 - eta) := by
    intro m hm
    obtain ⟨hmL, hmU⟩ := mem_Ioc.mp hm
    exact ⟨by omega, (by exact_mod_cast hmU : (m : ℝ) ≤ U).trans hU⟩
  have hlow' := hlow x hx₁ h ⌊Real.log (x : ℝ) ^ b⌋₊ (Ioc L U)
    (panSourceG f h) (fun _ _ => r) hh hhx hS
    (Nat.floor_le (Real.rpow_nonneg hlog0.le b))
    (fun m _ => panSourceG_norm_le f hf h m) (fun _ _ _ m hm => hr m hm)
  have hUx : U ≤ x := by
    have hp : (x : ℝ) ^ (1 - eta) ≤ (x : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hxR (by linarith : 1 - eta ≤ 1)
    exact_mod_cast hU.trans hp
  have hhigh' := hhigh x hx₂ h L U f r hr hUx hU hL hf
  have hmain : C₂ * (x : ℝ) * Real.log (x : ℝ) ^ (6 - b) ≤
      C₂ * x / Real.log (x : ℝ) ^ A := by
    calc
      _ ≤ C₂ * (x : ℝ) * Real.log (x : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)) (by positivity)
      _ = _ := by rw [Real.rpow_neg hlog0.le]; rfl
  have hpay' : Real.log (x : ℝ) ^ (A + 2) ≤ (x : ℝ) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul, Real.rpow_two,
      abs_of_nonneg (sq_nonneg (x : ℝ))] using hpay
  have hresidual : (Real.log (x : ℝ)) ^ 2 / (x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ A := by
    apply (div_le_div_iff₀ hx0 hlogA).mpr
    calc
      _ = Real.log (x : ℝ) ^ (A + 2) := by
        rw [Real.rpow_add hlog0, Real.rpow_two]; ring
      _ ≤ (x : ℝ) ^ 2 := hpay'
      _ = _ := by ring
  calc
    _ ≤ lowRealMovingSource (panSourceG f h) (fun _ _ => r) (Ioc L U)
        h ⌊Real.log (x : ℝ) ^ b⌋₊ + realMovingHighSource f r h x L U b :=
      commonPrimitiveSource_le_low_add_high f r h x Q L U b hlog hb hQ
    _ ≤ C₁ * x / Real.log (x : ℝ) ^ A +
        (C₂ * (x : ℝ) * Real.log (x : ℝ) ^ (6 - b) +
          6984 * (Real.log (x : ℝ)) ^ 2 / (x : ℝ)) :=
      add_le_add hlow' hhigh'
    _ ≤ C₁ * x / Real.log (x : ℝ) ^ A +
        (C₂ * x / Real.log (x : ℝ) ^ A +
          6984 * ((x : ℝ) / Real.log (x : ℝ) ^ A)) := by
      apply add_le_add le_rfl
      apply add_le_add hmain
      simpa only [mul_div_assoc] using
        (mul_le_mul_of_nonneg_left hresidual (by norm_num : (0 : ℝ) ≤ 6984))
    _ = _ := by ring

theorem balanced_commonPrimitiveSource_log_saving_uniform_level (A eta : ℝ)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ B : ℝ, b ≤ B →
      ∀ (h Q L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      1 ≤ h → h ≤ x →
      (U : ℝ) ≤ (x : ℝ) ^ (1 - eta) →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ m ∈ Ioc L U, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      commonPrimitiveSource f r h Q L U ≤ C * x / Real.log (x : ℝ) ^ A := by
  let b := A + 6
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨C, hC, x₁, hbound⟩ :=
    balanced_commonPrimitiveSource_log_saving_of_split A b eta hA hb le_rfl heta
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  refine ⟨b, C, hb, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlog, eventually_ge_atTop x₁] with x hlog hx
  intro B hB h Q L U f r hh hhx hU hQ hL hf hr
  apply hbound x hx h Q L U f r hh hhx hU _ hL hf hr
  exact hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    (Real.rpow_pos_of_pos (by linarith) b)
    (Real.rpow_le_rpow_of_exponent_le hlog hB))

end
end Wu2004MeanValue