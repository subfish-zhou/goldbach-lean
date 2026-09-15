import MixedEtaScalar
import MixedEtaWeighted

namespace MixedEta
open Real Filter Wu2008DoubleSieve
open scoped Topology
noncomputable section

/-- One eta pays the complete negative debit for every delta and coarse grid. -/
theorem uniform_eta_payment {ε : ℝ} (hε : 0<ε) : ∃ η : ℝ,0<η ∧
    ∀ᶠ N : ℕ in atTop,∀ δ : ℝ,0≤δ → ∀ n : ℕ,
      MixedSixth.main N n δ 0-ε*truncatedSixthMassScale N≤MixedSixth.main N n δ η := by
  let c : ℝ := 15*etaConstant
  have hc : 0<c := mul_pos (by norm_num) etaConstant_pos
  let η : ℝ := ε/(c+1)
  have hη : 0<η := div_pos hε (by linarith)
  have hpay : 15*η*etaConstant≤ε := by
    change 15*(ε/(c+1))*etaConstant≤ε
    have he : 15*(ε/(c+1))*etaConstant=ε*c/(c+1) := by dsimp [c]; ring
    rw [he]
    apply (div_le_iff₀ (show 0<c+1 by linarith)).mpr
    nlinarith only [hε]
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^truncatedSixthLowerAlpha) atTop atTop :=
    (tendsto_rpow_atTop truncatedSixthLower_parameters.1).comp tendsto_natCast_atTop_atTop
  refine ⟨η,hη,?_⟩
  filter_upwards [total_classical_upper,eventually_ge_atTop (4:ℕ),ht.eventually_ge_atTop (3:ℝ)] with N hmass hN hlarge
  intro δ hδ n
  have ha := actual_main_eta_lower hN hδ hη.le hlarge n
  have hm := mul_le_mul_of_nonneg_left (hmass δ hδ) (show 0≤15*η by positivity)
  have hp := mul_le_mul_of_nonneg_right hpay (truncatedSixthClosure_scale_nonneg hN)
  nlinarith only [ha,hm,hp]

end
end MixedEta
