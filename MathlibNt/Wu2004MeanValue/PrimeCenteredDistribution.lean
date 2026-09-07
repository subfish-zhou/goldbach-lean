import MathlibNt.Wu2004MeanValue.BalancedAP
import MathlibNt.Wu2004MeanValue.PrimeCentered

/-!
# Balanced distribution centered at the actual prime count

This consumes the proved actual AP producer and the filtered principal
transport. No distribution or PNT estimate is a caller-supplied premise.
It supplies the prime-count normalization used in Wu (2004), (5.7).
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators

noncomputable section

theorem balanced_common_profile_primeCentered_natural (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ m ∈ S, (N : ℝ) ^ eta ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (1 - eta)) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ N) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |primeCenteredAPSum S f r d (b d)|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, J, hB, hJ, N₁, hAP⟩ :=
    balanced_common_profile_weighted_natural A eta F hA heta hF
  obtain ⟨P, hP, x₂, htransport⟩ :=
    weighted_primeCenteredAPSum_le_actual_add A eta F hA heta hF
  refine ⟨B, J + P, hB, by positivity, max 3 (max N₁ ⌈x₂⌉₊), ?_⟩
  intro N hN Q S f r b hQ hS hf hr hb
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hx₂ : x₂ ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNexp : Real.exp 1 ≤ (N : ℝ) :=
    (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans
      (by exact_mod_cast hN3)
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hNexp
  have hQN : (Q : ℝ) ≤ N :=
    (hQ.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hlog1 hB.le))).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hN1))
  have hS' : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (1 - eta) := by
    intro m hm
    exact ⟨by exact_mod_cast (Real.one_le_rpow hN1 heta.le).trans (hS m hm).1,
      (hS m hm).2⟩
  calc
    _ ≤ (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) +
        P * N / Real.log (N : ℝ) ^ A :=
      htransport N hx₂ Q (fun _ => S) (fun _ => f) (fun _ => r) b hQN
        (fun _ _ => hS') (fun _ _ => hf) (fun _ _ => hr)
    _ ≤ J * N / Real.log (N : ℝ) ^ A + P * N / Real.log (N : ℝ) ^ A :=
      add_le_add (hAP N hN₁ Q S f r b hQ hS hf hr hb) le_rfl
    _ = _ := by ring

end
end Wu2004MeanValue