import MathlibNt.Wu2004MeanValue.BalancedLowPrefix
import MathlibNt.Wu2004MeanValue.LowRealEndpoints

/-! Low conductors on every fixed balanced cofactor range. -/

namespace Wu2004MeanValue
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped BigOperators Topology
noncomputable section


theorem balanced_low_source_nat_moving (A b eta F : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (h U Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (t : (q : ℕ) → PrimitiveCharacter q → ℕ → ℕ),
      1 ≤ h → h ≤ N →
      (U : ℝ) ≤ (N : ℝ) ^ (1 - eta) → S ⊆ Icc 1 U →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S, t q χ a ≤ N / a) →
      lowMovingSource f t S h Q ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨J, hJ, Nsw, hsw⟩ :=
    balanced_low_primePrefix_nat_div_max b (A + b + 1) eta hb (by linarith) heta
  have hlim := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (A + b + 1) heta).bound
      (show (0 : ℝ) < 1 by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  refine ⟨(F + 1) * (2 * J + (Real.log 2)⁻¹), by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlim, hlog, eventually_ge_atTop (max 3 Nsw)] with N hlim hlog hN
  dsimp only [Function.comp_apply] at hlog
  intro h U Q S f t hh hhN hU hS hQ hf ht
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNsw : Nsw ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  have hUN : U ≤ N := by
    have hr : (N : ℝ) ^ (1 - eta) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1 - eta ≤ 1)
    exact_mod_cast hU.trans hr
  have hp := balanced_lowMovingSource_le_budget f t S N U h Q J (A + b + 1) F
    hN3 hUN hS hh hJ.le hF hf (by
      intro a ha q hq χ
      obtain ⟨ha1, haU⟩ := mem_Icc.mp (hS ha)
      obtain ⟨hq2, hqQ⟩ := mem_Icc.mp hq
      exact hsw N hNsw a ha1 ((by exact_mod_cast haU : (a : ℝ) ≤ U).trans hU)
        q hq2 ((by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQ)
        χ (t q χ a) (ht q hq χ a ha))
  have hpay : Real.log (N : ℝ) ^ (A + b + 1) ≤ (N : ℝ) ^ eta := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0.le _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hlim
  have hmain :
      Real.log (N : ℝ) ^ b *
        ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) * (1 + Real.log N)) ≤
      2 * J * N / Real.log (N : ℝ) ^ A := by
    calc
      _ ≤ Real.log (N : ℝ) ^ b *
          ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) * (2 * Real.log N)) := by
        gcongr; linarith
      _ = _ := by
        rw [show A + b + 1 = A + (b + 1) by ring,
          Real.rpow_add hlog0, Real.rpow_add hlog0, Real.rpow_one]
        field_simp
  have hdel :
      Real.log (N : ℝ) ^ b * ((U : ℝ) * h.primeFactors.card) ≤
      (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ ≤ Real.log (N : ℝ) ^ b *
          ((N : ℝ) ^ (1 - eta) * ((Real.log 2)⁻¹ * Real.log N)) *
          Real.log (N : ℝ) ^ A := by
        gcongr
        exact primeFactors_card_le_log_of_le hh (by exact_mod_cast hhN)
      _ = (Real.log 2)⁻¹ * (N : ℝ) ^ (1 - eta) *
          Real.log (N : ℝ) ^ (A + b + 1) := by
        rw [show A + b + 1 = A + (b + 1) by ring,
          Real.rpow_add hlog0, Real.rpow_add hlog0, Real.rpow_one]
        ring
      _ ≤ (Real.log 2)⁻¹ * (N : ℝ) ^ (1 - eta) * (N : ℝ) ^ eta := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; simp
  calc
    _ ≤ F * ((Q : ℝ) * ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) *
        (1 + Real.log N) + (U : ℝ) * h.primeFactors.card)) := hp
    _ ≤ F * (Real.log (N : ℝ) ^ b * ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) *
        (1 + Real.log N) + (U : ℝ) * h.primeFactors.card)) := by gcongr
    _ ≤ F * (2 * J * N / Real.log (N : ℝ) ^ A +
        (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A) := by
      rw [mul_add]
      exact mul_le_mul_of_nonneg_left (add_le_add hmain hdel) hF
    _ ≤ (F + 1) * (2 * J * N / Real.log (N : ℝ) ^ A +
        (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A) := by gcongr; linarith
    _ = _ := by ring

theorem balanced_low_source_real_moving (A b eta F : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (h Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (r : (q : ℕ) → PrimitiveCharacter q → ℕ → ℝ),
      1 ≤ h → h ≤ N →
      (∀ a ∈ S, 1 ≤ a ∧ (a : ℝ) ≤ (N : ℝ) ^ (1 - eta)) →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S,
        0 ≤ r q χ a ∧ (a : ℝ) * r q χ a ≤ N) →
      lowRealMovingSource f r S h Q ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, N₀, hbound⟩ := balanced_low_source_nat_moving A b eta F hA hb heta hF
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN h Q S f r hh hhN hS hQ hf hr
  rw [lowRealMovingSource_eq_natural]
  apply hbound N hN h ⌊(N : ℝ) ^ (1 - eta)⌋₊ Q S f
    (fun q χ a => ⌊r q χ a⌋₊) hh hhN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (fun a ha => mem_Icc.mpr ⟨(hS a ha).1, Nat.le_floor (hS a ha).2⟩) hQ hf
  intro q hq χ a ha
  apply (Nat.le_div_iff_mul_le (hS a ha).1).mpr
  have hp := (mul_le_mul_of_nonneg_left (Nat.floor_le (hr q hq χ a ha).1)
    (Nat.cast_nonneg a)).trans (hr q hq χ a ha).2
  have hp' : a * ⌊r q χ a⌋₊ ≤ N := by exact_mod_cast hp
  simpa only [Nat.mul_comm] using hp'

end
end Wu2004MeanValue
