import LowComplementNormalize

namespace LowComplement
open Real Wu2008DoubleSieve Filter
open DirectFiniteF6 ActualNineFeedback QuarterTrim
open scoped Classical Topology
noncomputable section

/-- Existing finite feedback payments, made uniform on a complete right neighbourhood.
The finite iterate is selected symbolically by convergence, never evaluated. -/
theorem Cinf_Hadm_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      FeedbackLimit.Cinf-ε ≤ truncatedSixthLowerHadmdelta δ := by
  obtain ⟨k,hk⟩ := (FeedbackLimit.C_tendsto.eventually_const_lt
    (show FeedbackLimit.Cinf-ε/3 < FeedbackLimit.Cinf by linarith)).exists
  let L := loss (transferredLower k)
  have hL : 0 ≤ L := loss_nonneg _
  let t : ℝ := min (1/1000) (ε/(3*(L+1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht' : t ≤ 1/1000 := min_le_left _ _
  have htp : t ≤ ε/(3*(L+1)) := min_le_right _ _
  have hpayt : L*t < ε/3 := by
    have h := (le_div_iff₀ (show 0 < 3*(L+1) by positivity)).mp htp
    nlinarith only [h,ht]
  let d0 : ℝ := min (1/100) (min (t/2) (marginRadius (E k) (ε/3)))
  have hd0 : 0 < d0 := lt_min (by norm_num) (lt_min (half_pos ht)
    (marginRadius_pos (E_nonneg k) (by positivity)))
  refine ⟨d0,hd0,min_le_left _ _,?_⟩
  intro δ hδ hδ0
  have hδt : δ ≤ t/2 := hδ0.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ < marginRadius (E k) (ε/3) :=
    hδ0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpayd := deltaLoss_mul_lt_margin (E_nonneg k) (show 0 < ε/3 by positivity) hδ hδr
  have hp := finite_Gamma_payment ht ht' hδ hδt k
  change C k-L*t-deltaLoss δ*E k ≤ _ at hp
  linarith only [hk,hpayt,hpayd,hp]

/-- Actual B reaches F6lin+Cinf; all sufficiently fine original grids remain available. -/
theorem B_normalization {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+FeedbackLimit.Cinf-ε)*truncatedSixthMassScale N ≤ B N n δ := by
  obtain ⟨a,ha,hahi,hFa⟩ := truncatedSixthZeroDelta_Fdelta_close (show 0 < ε/3 by positivity)
  obtain ⟨b,hb,_,hHb⟩ := Cinf_Hadm_payment (show 0 < ε/3 by positivity)
  refine ⟨min a b,lt_min ha hb,(min_le_left _ _).trans hahi,?_⟩
  intro δ hδ hδ0
  have hδa := hδ0.trans_le (min_le_left a b)
  have hδb := hδ0.trans_le (min_le_right a b)
  have hF := (abs_lt.mp (hFa δ hδ hδa)).1
  have hH := hHb δ hδ hδb
  filter_upwards [B_delta_normalization hδ (hδa.trans_le hahi) (show 0 < ε/3 by positivity)] with n hn
  filter_upwards [hn,eventually_ge_atTop (4:ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [hF,hH])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

/-- Explicit arbitrary-threshold form for a high-lane consumer. -/
theorem B_normalization_cofinal {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+FeedbackLimit.Cinf-ε)*truncatedSixthMassScale N ≤ B N n δ := by
  obtain ⟨d0,hd0,hdhi,h⟩ := B_normalization hε
  refine ⟨d0,hd0,hdhi,?_⟩
  intro δ hδ hδ0 m
  obtain ⟨n,hn,hm⟩ := ((h δ hδ hδ0).and (eventually_ge_atTop m)).exists
  exact ⟨n,hm,hn⟩

end
end LowComplement
