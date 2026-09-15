import LowComplementCinf

namespace LowComplement
open Real Wu2008DoubleSieve Filter
open scoped Classical Topology
noncomputable section

/-- Cap the already proved explicit global eta construction; no mass constant is re-proved. -/
theorem uniform_eta_payment_capped {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ,
        MixedSixth.main N n δ 0-ε*truncatedSixthMassScale N ≤ MixedSixth.main N n δ η := by
  let c : ℝ := 15*MixedEta.etaConstant
  have hc : 0 < c := mul_pos (by norm_num) MixedEta.etaConstant_pos
  let e : ℝ := min ε 1
  have he : 0 < e := lt_min hε zero_lt_one
  let η : ℝ := e/(c+1)
  have hη : 0 < η := div_pos he (by linarith)
  have hη1 : η ≤ 1 := by
    apply (div_le_one (show 0 < c+1 by linarith)).mpr
    exact (min_le_right ε 1).trans (by linarith)
  have hpay : 15*η*MixedEta.etaConstant ≤ ε := by
    have heq : 15*η*MixedEta.etaConstant=e*c/(c+1) := by dsimp [η,c]; ring
    rw [heq]
    apply le_trans _ (min_le_left ε 1)
    apply (div_le_iff₀ (show 0 < c+1 by linarith)).mpr
    nlinarith only [he]
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^truncatedSixthLowerAlpha) atTop atTop :=
    (tendsto_rpow_atTop truncatedSixthLower_parameters.1).comp tendsto_natCast_atTop_atTop
  refine ⟨η,hη,hη1,?_⟩
  filter_upwards [MixedEta.total_classical_upper,eventually_ge_atTop (4:ℕ),
    ht.eventually_ge_atTop (3:ℝ)] with N hmass hN hlarge
  intro δ hδ n
  have ha := MixedEta.actual_main_eta_lower hN hδ hη.le hlarge n
  have hm := mul_le_mul_of_nonneg_left (hmass δ hδ) (show 0 ≤ 15*η by positivity)
  have hp := mul_le_mul_of_nonneg_right hpay (truncatedSixthClosure_scale_nonneg hN)
  nlinarith only [ha,hm,hp]

/-- Pointwise composition with exactly the independently owned high incremental term. -/
theorem combine_pointwise {N n : ℕ} {δ εL εH H : ℝ}
    (hB : (truncatedSixthLowerF6lin+FeedbackLimit.Cinf-εL)*truncatedSixthMassScale N ≤ B N n δ)
    (hE : (H-εH)*truncatedSixthMassScale N ≤
      MixedEta.highMain N n δ-truncatedSixthLowerNormalizedMain N δ 0
        (MixedEta.selected N n (MixedSixth.highCells δ n))) :
    (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+H-(εL+εH))*truncatedSixthMassScale N ≤
      MixedSixth.main N n δ 0 := by
  unfold B at hB
  linarith only [hB,hE]

/-- CONDITIONAL high-lane consumer. Only the displayed exact E normalization remains a binder.
No G is fixed, and no G/delta quantifier exchange is used. -/
theorem combine_with_high_payment {H : ℝ}
    (high_payment : ∀ ε : ℝ, 0 < ε → ∃ d0 : ℝ, 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ < d0 → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (H-ε)*truncatedSixthMassScale N ≤ MixedEta.highMain N n δ-
          truncatedSixthLowerNormalizedMain N δ 0
            (MixedEta.selected N n (MixedSixth.highCells δ n)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d0 → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+FeedbackLimit.Cinf+H-ε)*truncatedSixthMassScale N ≤
          MixedSixth.main N n δ η := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,hahi,hB⟩ := B_normalization he
  obtain ⟨b,hb,hE⟩ := high_payment (ε/3) he
  obtain ⟨η,hη,hη1,hpay⟩ := uniform_eta_payment_capped he
  refine ⟨η,hη,hη1,min a b,lt_min ha hb,(min_le_left _ _).trans hahi,?_⟩
  intro δ hδ hδ0
  filter_upwards [hB δ hδ (hδ0.trans_le (min_le_left _ _)),
    hE δ hδ (hδ0.trans_le (min_le_right _ _))] with n hBn hEn
  filter_upwards [hBn,hEn,hpay] with N hBN hEN hηN
  have hm := combine_pointwise hBN hEN
  have hp := hηN δ hδ.le n
  linarith only [hm,hp]

end
end LowComplement
