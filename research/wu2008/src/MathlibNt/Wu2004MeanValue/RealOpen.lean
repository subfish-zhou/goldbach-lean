import MathlibNt.Wu2004MeanValue.CommonProfileEndpoints
import MathlibNt.Wu2004MeanValue.ActualOpenIntervals
import MathlibNt.Wu2004MeanValue.APWeightTransferAtoms
import MathlibNt.Wu2004MeanValue.MuSquare

/-! Real-scale open-interval discrepancies with fully paid endpoint atoms.
The literal manuscript block is then an actual counting specialization. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem common_profile_open_weighted_real (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ (S : Finset ℕ) (f lo hi : ℕ → ℝ) (b : ℕ → ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ lo m / m ∧ lo m < hi m ∧ hi m ≤ x) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualOpenErrorSum S f lo hi d (b d)|) ≤ C * x / Real.log x ^ A := by
  obtain ⟨B₁, J, hB₁, hJ, x₁, hAP⟩ :=
    common_profile_weighted_real A F 1 hA hF (by norm_num)
  obtain ⟨E, hE, hatoms⟩ := actualEndpointSum_weighted_log_saving A F hA hF
  refine ⟨max B₁ (A + 6), 2 * J + E, hB₁.trans_le (le_max_left _ _),
    by positivity, max 3 x₁, ?_⟩
  intro x hx Q hQ S f lo hi b hS hf hr hb
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : x₁ ≤ x := (le_max_right _ _).trans hx
  have hxexp : Real.exp 1 ≤ x :=
    (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans hx3
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hcut (T : ℝ) (hT : T ≤ max B₁ (A + 6)) :
      (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ T :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos hlog0 T) (Real.rpow_le_rpow_of_exponent_le hlog1 hT))
  have hlo : ∀ m ∈ S, 0 ≤ lo m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
    have h := (le_div_iff₀ hm0).mp (hr m hm).1
    linarith
  have hdomain (m : ℕ) (hm : m ∈ S) :
      (2 ≤ hi m / m ∧ (m : ℝ) * (hi m / m) ≤ 1 * x) ∧
        (2 ≤ lo m / m ∧ (m : ℝ) * (lo m / m) ≤ 1 * x) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
    have hmul (t : ℝ) : (m : ℝ) * (t / m) = t := by field_simp
    rw [hmul, hmul, one_mul]
    exact ⟨⟨(hr m hm).1.trans (div_le_div_of_nonneg_right (hr m hm).2.1.le hm0.le),
      (hr m hm).2.2⟩, ⟨(hr m hm).1, (hr m hm).2.1.le.trans (hr m hm).2.2⟩⟩
  have hupper := hAP x hx₁ Q (hcut B₁ (le_max_left _ _)) S f
    (fun m => hi m / m) b hS hf (fun m hm => (hdomain m hm).1) hb
  have hlower := hAP x hx₁ Q (hcut B₁ (le_max_left _ _)) S f
    (fun m => lo m / m) b hS hf (fun m hm => (hdomain m hm).2) hb
  have hE' := hatoms x Q S f (fun _ => hi) b hxexp
    (hcut (A + 6) (le_max_right _ _)) hS hf
  calc
    _ ≤ (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => hi m / m) d (b d)|) +
        (∑ d ∈ Icc 1 Q, wuModulusWeight d *
          |actualAPSum S f (fun m => lo m / m) d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualEndpointSum S f hi d (b d)| :=
      weighted_actualOpenErrorSum_le S f lo hi Q b (fun m hm => (hS m hm).1)
        hlo (fun m hm => (hr m hm).2.1)
    _ ≤ J * x / Real.log x ^ A + J * x / Real.log x ^ A +
        E * x / Real.log x ^ A := add_le_add (add_le_add hupper hlower) hE'
    _ = _ := by ring

theorem manuscript_block_open_weighted (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℝ,
      ∀ H : ℝ, X₀ ≤ 2 * H →
      ∀ (N : ℕ) (a η : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ m ∈ S, m.Prime ∧ blockLower H m < blockUpper H N a η m) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∑ d ∈ (Icc 1 Q).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualOpenErrorSum S f (blockLower H) (blockUpper H N a η) d N|) ≤
          C * (2 * H) / Real.log (2 * H) ^ A := by
  obtain ⟨B, C, hB, hC, X₀, hbound⟩ := common_profile_open_weighted_real A F hA hF
  refine ⟨B, C, hB, hC, X₀, ?_⟩
  intro H hH N a η Q hQ S f hS hf
  let b : ℕ → ℕ := fun d => if N.Coprime d then N else 1
  have hb : ∀ d ∈ Icc 1 Q, (b d).Coprime d := by
    intro d _
    dsimp [b]
    split_ifs with hd
    · exact hd
    · exact Nat.coprime_one_left d
  have hsource : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt (2 * H) := by
    intro m hm
    exact ⟨(hS m hm).1.one_le, block_source_sqrt_domain H N a η m (hS m hm).2⟩
  have hdom : ∀ m ∈ S, 2 ≤ blockLower H m / m ∧
      blockLower H m < blockUpper H N a η m ∧ blockUpper H N a η m ≤ 2 * H := by
    intro m hm
    exact ⟨(block_prime_endpoint_domain H N a η m (hS m hm).1 (hS m hm).2).1.1,
      (hS m hm).2, (min_le_left _ _).trans (min_le_left _ _)⟩
  calc
    _ = ∑ d ∈ (Icc 1 Q).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualOpenErrorSum S f (blockLower H) (blockUpper H N a η) d (b d)| := by
      apply sum_congr rfl
      intro d hd
      simp only [b, if_pos (mem_filter.mp hd).2]
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualOpenErrorSum S f (blockLower H) (blockUpper H N a η) d (b d)| := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ _ := hbound (2 * H) hH Q hQ S f (blockLower H) (blockUpper H N a η)
      b hsource hf hdom hb

theorem manuscript_block_open_muSquare (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℝ,
      ∀ H : ℝ, X₀ ≤ 2 * H →
      ∀ (N : ℕ) (a η : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ m ∈ S, m.Prime ∧ blockLower H m < blockUpper H N a η m) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∑ d ∈ (Icc 1 Q).filter (fun d => N.Coprime d),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |actualOpenErrorSum S f (blockLower H) (blockUpper H N a η) d N|) ≤
          C * (2 * H) / Real.log (2 * H) ^ A := by
  obtain ⟨B, C, hB, hC, X₀, hbound⟩ := manuscript_block_open_weighted A F hA hF
  refine ⟨B, C, hB, hC, X₀, ?_⟩
  intro H hH N a η Q hQ S f hS hf
  exact (muSquare_sum_le_wu _ _ (fun _ _ => abs_nonneg _)).trans
    (hbound H hH N a η Q hQ S f hS hf)

end
end Wu2004MeanValue
