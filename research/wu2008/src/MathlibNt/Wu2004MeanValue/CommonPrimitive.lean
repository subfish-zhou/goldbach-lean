import MathlibNt.Wu2004MeanValue.LowRealEndpoints
import MathlibNt.Wu2004MeanValue.EndpointConsumers

/-!
# Whole primitive source for a common real prime profile

The conductor split exponent is independent of any later modulus exponent.
Both source and prime variables retain their cofactor coprimality screens.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators Topology

noncomputable section

def commonPrimitiveSource (f : ℕ → ℂ) (r : ℕ → ℝ) (h Q L U : ℕ) : ℝ :=
  ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖realMovingAmplitude (panSourceG f h) (panSourceD h) r L U χ‖

theorem commonPrimitiveSource_nonneg (f : ℕ → ℂ) (r : ℕ → ℝ)
    (h Q L U : ℕ) : 0 ≤ commonPrimitiveSource f r h Q L U := by
  unfold commonPrimitiveSource
  positivity

theorem panSourceD_sum_eq_lowPrimeSet {q : ℕ} (χ : PrimitiveCharacter q)
    (h : ℕ) (r : ℝ) :
    (∑ p ∈ Icc 1 ⌊r⌋₊, panSourceD h p * χ.1 (p : ZMod q)) =
      ∑ p ∈ lowPrimeSet r h, χ.1 (p : ZMod q) := by
  have hs : (Icc 1 ⌊r⌋₊).filter (fun p => p.Coprime h ∧ p.Prime) =
      lowPrimeSet r h := by
    ext p
    simp only [lowPrimeSet, mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨_, hp⟩, hc, hprime⟩
      exact ⟨by omega, hprime, hc⟩
    · rintro ⟨hp, hprime, hc⟩
      exact ⟨⟨hprime.one_le, by omega⟩, hc, hprime⟩
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro p _
  simp only [panSourceD, ite_mul, one_mul, zero_mul]

theorem commonPrimitiveSource_eq_lowRealMovingSource (f : ℕ → ℂ) (r : ℕ → ℝ)
    (h Q L U : ℕ) :
    commonPrimitiveSource f r h Q L U =
      lowRealMovingSource (panSourceG f h) (fun _ _ => r) (Ioc L U) h Q := by
  simp only [commonPrimitiveSource, lowRealMovingSource, realMovingAmplitude,
    panSourceD_sum_eq_lowPrimeSet]

theorem commonPrimitiveSource_mono (f : ℕ → ℂ) (r : ℕ → ℝ)
    (h L U : ℕ) {Q R : ℕ} (hQR : Q ≤ R) :
    commonPrimitiveSource f r h Q L U ≤ commonPrimitiveSource f r h R L U := by
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hQR)
  intro q _ _
  positivity

theorem commonPrimitiveSource_split (f : ℕ → ℂ) (r : ℕ → ℝ)
    (h Q L U T : ℕ) (hT : 1 ≤ T) :
    commonPrimitiveSource f r h Q L U =
      commonPrimitiveSource f r h (min Q T) L U +
        ∑ q ∈ Ioc T Q, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
          ‖realMovingAmplitude (panSourceG f h) (panSourceD h) r L U χ‖ := by
  have hs : Icc 2 Q = Icc 2 (min Q T) ∪ Ioc T Q := by
    ext q
    simp only [mem_union, mem_Icc, mem_Ioc, le_min_iff]
    omega
  have hd : Disjoint (Icc 2 (min Q T)) (Ioc T Q) := by
    apply disjoint_left.mpr
    intro q hq hq'
    have := mem_Icc.mp hq
    have := mem_Ioc.mp hq'
    omega
  unfold commonPrimitiveSource
  rw [hs, sum_union hd]

theorem commonPrimitiveSource_le_low_add_high (f : ℕ → ℂ) (r : ℕ → ℝ)
    (h x Q L U : ℕ) (b : ℝ)
    (hlog : 1 ≤ Real.log (x : ℝ)) (hb : 0 ≤ b)
    (hQ : (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ b) :
    commonPrimitiveSource f r h Q L U ≤
      lowRealMovingSource (panSourceG f h) (fun _ _ => r)
        (Ioc L U) h ⌊Real.log (x : ℝ) ^ b⌋₊ +
      realMovingHighSource f r h x L U b := by
  have hT : 1 ≤ ⌊Real.log (x : ℝ) ^ b⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using
      (Real.one_le_rpow hlog hb))
  rw [commonPrimitiveSource_split f r h Q L U _ hT]
  apply add_le_add
  · rw [← commonPrimitiveSource_eq_lowRealMovingSource]
    exact commonPrimitiveSource_mono f r h L U (min_le_right _ _)
  · apply sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc le_rfl (Nat.le_floor hQ))
    intro q _ _
    positivity

/-- The source cutoff uses the conductor split exponent `b`, not a subsequent
modulus-level exponent. The low and high analytic producers are both consumed
with the same screened coefficients and common real prime profile. -/
theorem commonPrimitiveSource_log_saving_of_split (A b : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (hAb : A + 6 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ (h Q L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      1 ≤ h → (h : ℝ) ≤ Real.sqrt x →
      (U : ℝ) ≤ Real.sqrt x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ b →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ m ∈ Ioc L U, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      commonPrimitiveSource f r h Q L U ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨C₁, hC₁, N₁, hlow⟩ :=
    low_source_real_moving A b 1 1 hA hb (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hhigh⟩ := chosen_high_source_real_moving_profile_log_saving
  obtain ⟨N₂, hhigh⟩ := hhigh b (1 / 2) hb (by norm_num)
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
  have hS : ∀ m ∈ Ioc L U, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x := by
    intro m hm
    obtain ⟨hmL, hmU⟩ := mem_Ioc.mp hm
    exact ⟨by omega, (by exact_mod_cast hmU : (m : ℝ) ≤ U).trans hU⟩
  have hlow' := hlow x hx₁ h ⌊Real.log (x : ℝ) ^ b⌋₊ (Ioc L U)
    (panSourceG f h) (fun _ _ => r) hh hhx hS
    (Nat.floor_le (Real.rpow_nonneg hlog0.le b))
    (fun m _ => panSourceG_norm_le f hf h m)
    (fun _ _ _ m hm => by simpa only [one_mul] using hr m hm)
  have hUx : U ≤ x := by
    have hroot : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hxR (by norm_num : (1 / 2 : ℝ) ≤ 1))
    exact_mod_cast hU.trans hroot
  have hUpow : (U : ℝ) ≤ (x : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow] using hU
  have hhigh' := hhigh x hx₂ h L U f r hr hUx hUpow hL hf
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
        rw [Real.rpow_add hlog0, Real.rpow_two]
        ring
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

/-- Arbitrary logarithmic saving with constants and split exponent chosen
before the cofactor, modulus bound, source interval, coefficients and profile. -/
theorem commonPrimitiveSource_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ (h Q L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      1 ≤ h → (h : ℝ) ≤ Real.sqrt x →
      (U : ℝ) ≤ Real.sqrt x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ b →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ m ∈ Ioc L U, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      commonPrimitiveSource f r h Q L U ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨C, hC, x₀, hbound⟩ := commonPrimitiveSource_log_saving_of_split
    A (A + 6) hA (by linarith) le_rfl
  exact ⟨A + 6, C, by linarith, hC, x₀, hbound⟩

/-- A later modulus-level exponent may be increased arbitrarily without
changing the source support cutoff or the constants already chosen. -/
theorem commonPrimitiveSource_log_saving_uniform_level (A : ℝ) (hA : 0 < A) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ B : ℝ, b ≤ B →
      ∀ (h Q L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      1 ≤ h → (h : ℝ) ≤ Real.sqrt x →
      (U : ℝ) ≤ Real.sqrt x →
      (Q : ℝ) ≤ Real.sqrt x / Real.log (x : ℝ) ^ B →
      Real.log (x : ℝ) ^ (2 * b) ≤ L →
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ m ∈ Ioc L U, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      commonPrimitiveSource f r h Q L U ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨b, C, hb, hC, x₁, hbound⟩ := commonPrimitiveSource_log_saving A hA
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