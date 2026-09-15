import W03Area
import Wu04BypassActual

namespace WuTarget.W03
open Set MeasureTheory QuarterTrim DirectFiniteF6 ActualNineFeedback NodeExtension
open Wu2008DoubleSieve
open scoped Classical BigOperators
noncomputable section

theorem nodes_profile_lower {w : Fin 21 → ℝ} {δ t x y : ℝ}
    (ht : 0 < t) (hd : 0 < δ) (hdt : δ ≤ t/2) (hdhi : δ ≤ 1/10)
    (hn : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1)))
    (hv : (x,y) ∈ StaircaseShrink.domain t) :
    profile w (u x y) ≤
      wuImprovementLimit false δ (truncatedSixthLowerS δ x y) := by
  have hm : AntitoneOn (wuImprovementLimit false δ) (Icc 2 (41/10)) := by
    apply (wuImprovementLimit_lower_antitone hd (by linarith)).mono
    intro s hs
    exact ⟨hs.1,by linarith [hs.2]⟩
  have hb := StaircaseShrink.source_budgets ht hd hdt hv
  have hsu := hb.2.2.2.2.2.2.2
  have hs : StaircaseShrink.shiftedU δ x y ∈ Icc 2 (41/10) :=
    ⟨hb.2.2.2.2.2.2.1, hsu.trans (StaircaseShrink.original_u_upper hv)⟩
  apply StaircaseShrink.eval_le_of_nodes (rows w) _ hm
    (fun r hr => ⟨row_endpoint w hr, ?_⟩) hs hsu
    (wuImprovementLimit_nonneg false hd (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]))
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  change w j ≤ wuImprovementLimit false δ (originalRow j).2.1
  rw [originalRow_node]
  exact hn j

theorem nodes_uniform_le_actual {w : Fin 21 → ℝ} {δ t : ℝ}
    (hw : ∀ j, 0 ≤ w j) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2)
    (hn : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1)))
    (v : ℝ × ℝ) :
    uniform w t v ≤ truncatedSixthMassHKernel δ v := by
  by_cases hv : v ∈ StaircaseShrink.domain t
  · have hvt : truncatedSixthLowerAdmissibleRegion t v.1 v.2 := by
      have he := congrArg (fun S : Set (ℝ × ℝ) => v ∈ S) (StaircaseActual.domain_eq ht.le)
      exact he.mp hv
    have hvd := StaircaseActual.region_mono (show δ ≤ t by linarith) hvt
    rw [uniform, if_pos hv, truncatedSixthMassHKernel, if_pos hvd]
    have hb := truncatedSixthLower_region_bounds hd.le hvd.1
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤
        v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.1.le hb.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    have hp := profile_nonneg hw (u v.1 v.2)
    have hl := nodes_profile_lower ht hd hdt (by linarith) hn hv
    exact div_le_div₀ (hp.trans hl) hl (StaircaseActual.denominator_pos hd.le hvd) hz
  · rw [uniform, if_neg hv]
    exact (truncatedSixthMass_kernels_bounds hd (by linarith) v).2.1

theorem nodes_Gamma_payment {w : Fin 21 → ℝ} {δ t : ℝ}
    (hw : ∀ j, 0 ≤ w j) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2)
    (hn : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1))) :
    Gamma w 0 - DirectFiniteF6.loss w * t ≤ truncatedSixthLowerHadmdelta δ := by
  have hp : Gamma w t ≤ truncatedSixthLowerHadmdelta δ := by
    rw [Gamma, (truncatedSixthMass_literal_integrals hd (by linarith)).2]
    exact mul_le_mul_of_nonneg_left
      (integral_mono (uniform_integrable w ht.le)
        (truncatedSixthMass_kernels_integrable hd (by linarith)).2
        (nodes_uniform_le_actual hw ht ht' hd hdt hn)) (by norm_num)
  have hl := (Gamma_loss hw ht.le ht').2
  linarith only [hp,hl]

def frozen : Fin 21 → ℝ := matrixApply transferMatrix Wu04Bypass.v8

theorem frozen_nonneg (j : Fin 21) : 0 ≤ frozen j :=
  matrixApply_nonneg transferMatrix_nonneg Wu04Bypass.v8_nonneg j

theorem frozen_exact :
    Gamma (matrixApply transferMatrix Wu04Bypass.v8) 0 =
      ∑ j : Fin 21, weight j * matrixApply transferMatrix Wu04Bypass.v8 j :=
  Gamma_eq_weights _

theorem frozen_rational_lower :
    (∑ j : Fin 21, rationalWeight j * matrixApply transferMatrix Wu04Bypass.v8 j) ≤
      Gamma (matrixApply transferMatrix Wu04Bypass.v8) 0 :=
  rational_weights_consumer frozen_nonneg

theorem frozen_Hadm_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      Gamma (matrixApply transferMatrix Wu04Bypass.v8) 0 - ε ≤
        truncatedSixthLowerHadmdelta δ := by
  obtain ⟨d,hd,_,hn⟩ := Wu04Bypass.new_nine_and_twentyone_actual
  let L := DirectFiniteF6.loss frozen
  have hL : 0 ≤ L := loss_nonneg _
  let t : ℝ := min (1/1000) (ε/(L+1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht' : t ≤ 1/1000 := min_le_left _ _
  have hpay : L*t < ε := by
    have hp := (le_div_iff₀ (show 0 < L+1 by positivity)).mp (min_le_right (1/1000) (ε/(L+1)))
    nlinarith only [hp,ht]
  refine ⟨min (1/100) (min d (t/2)), lt_min (by norm_num) (lt_min hd (half_pos ht)),
    min_le_left _ _, ?_⟩
  intro δ hδ hδ0
  have hδd : δ ≤ d := hδ0.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδt : δ ≤ t/2 := hδ0.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp := nodes_Gamma_payment frozen_nonneg ht ht' hδ hδt (hn δ hδ hδd).2
  change Gamma (matrixApply transferMatrix Wu04Bypass.v8) 0 - L*t ≤ _ at hp
  linarith only [hp,hpay]

theorem frozen_weighted_Hadm_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      (∑ j : Fin 21, weight j * matrixApply transferMatrix Wu04Bypass.v8 j) - ε ≤
        truncatedSixthLowerHadmdelta δ := by
  simpa only [frozen_exact] using frozen_Hadm_payment hε

theorem frozen_rational_Hadm_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      (∑ j : Fin 21, rationalWeight j * matrixApply transferMatrix Wu04Bypass.v8 j) - ε ≤
        truncatedSixthLowerHadmdelta δ := by
  obtain ⟨d,hd,hcap,hp⟩ := frozen_Hadm_payment hε
  exact ⟨d,hd,hcap,fun δ hδ hδd =>
    (sub_le_sub_right frozen_rational_lower ε).trans (hp δ hδ hδd)⟩

end
end WuTarget.W03
