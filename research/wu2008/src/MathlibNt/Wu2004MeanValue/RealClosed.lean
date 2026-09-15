import MathlibNt.Wu2004MeanValue.ClosedIntervals
import MathlibNt.Wu2004MeanValue.CommonProfileEndpoints
import MathlibNt.Wu2004MeanValue.APWeightTransferAtoms

/-! The inclusive tail consumes the two proved W1 endpoints and the full
Wu-weighted lower-atom budget. No endpoint error is left to the caller. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem manuscript_tail_closed_weighted (A F η : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) (hη : 0 < η) (hη1 : η < 1) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℝ,
      ∀ N : ℕ, X₀ ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ B →
      ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt N) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∑ d ∈ (Icc 1 Q).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualClosedErrorSum S f (fun _ => η * N) (fun _ => N) d N|) ≤
          C * N / Real.log N ^ A := by
  obtain ⟨B₁, J, hB₁, hJ, X₁, hAP⟩ :=
    common_profile_W1_tail_residueSup A F η hA hF hη hη1.le
  obtain ⟨E, hE, hEbound⟩ := actualEndpointSum_weighted_log_saving A F hA hF
  refine ⟨max B₁ (A + 6), 2 * J + E, hB₁.trans_le (le_max_left _ _),
    by positivity, max (Real.exp 1) X₁, ?_⟩
  intro N hN Q hQ S f hS hf
  have hexp : Real.exp 1 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := (Real.exp_pos 1).trans_le hexp
  have hlog1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hexp
  have hlog0 : 0 < Real.log N := by linarith
  have hcut (T : ℝ) (hT : T ≤ max B₁ (A + 6)) :
      (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ T :=
    hQ.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos hlog0 T) (Real.rpow_le_rpow_of_exponent_le hlog1 hT))
  obtain ⟨hhi, hlo⟩ := hAP N ((le_max_right _ _).trans hN) Q
    (hcut B₁ (le_max_left _ _)) S f hS hf
  let b : ℕ → ℕ := fun d => if N.Coprime d then N else 1
  have hb (d : ℕ) : (b d).Coprime d := by
    dsimp [b]
    split_ifs with hd
    · exact hd
    · exact Nat.coprime_one_left d
  have hprefix (r : ℕ → ℝ) :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        ∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPResidueSup S f r d := by
    apply sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_left
      (actualAPSum_le_residueSup S f r d (b d) (mem_Icc.mp hd).1 (hb d))
      (wuModulusWeight_nonneg d)
  have hatoms := hEbound N Q S f (fun _ _ => η * N) b hexp
    (hcut (A + 6) (le_max_right _ _)) hS hf
  have hfull :
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualClosedErrorSum S f (fun _ => η * N) (fun _ => N) d (b d)|) ≤
          (2 * J + E) * N / Real.log N ^ A := by
    refine (weighted_actualClosedErrorSum_le S f (fun _ => η * N) (fun _ => N)
      Q b (fun m hm => (hS m hm).1) (fun _ _ => by positivity)
      (fun _ _ => by nlinarith)).trans ?_
    calc
      _ ≤ J * N / Real.log N ^ A + J * N / Real.log N ^ A +
          E * N / Real.log N ^ A :=
        add_le_add (add_le_add ((hprefix _).trans hhi) ((hprefix _).trans hlo)) hatoms
      _ = _ := by ring
  calc
    _ = ∑ d ∈ (Icc 1 Q).filter (fun d => N.Coprime d), wuModulusWeight d *
        |actualClosedErrorSum S f (fun _ => η * N) (fun _ => N) d (b d)| := by
      apply sum_congr rfl
      intro d hd
      simp only [b, if_pos (mem_filter.mp hd).2]
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualClosedErrorSum S f (fun _ => η * N) (fun _ => N) d (b d)| := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ _ := hfull

end
end Wu2004MeanValue
