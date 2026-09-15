import DirectCount
import Wu04BypassActual

noncomputable section
namespace WuTarget.W01
open Set MeasureTheory Wu2008DoubleSieve QuarterTrim
open ActualNineFeedback NodeExtension DirectFiniteF6
open scoped Classical

def lowGain (x : Fin 9 → ℝ) : ℝ := Gamma (matrixApply transferMatrix x) 0

theorem lowGain_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ lowGain x :=
  Gamma_nonneg (matrixApply_nonneg transferMatrix_nonneg hx) le_rfl

theorem lowGain_mono {x y : Fin 9 → ℝ} (hxy : ∀ i, x i ≤ y i) :
    lowGain x ≤ lowGain y :=
  Gamma_mono (matrixApply_mono transferMatrix_nonneg hxy) le_rfl

theorem transferred_actual {x : Fin 9 → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hx : ∀ i, x i ≤ actualNine δ i)
    (j : Fin 21) :
    matrixApply transferMatrix x j ≤ wuImprovementLimit false δ (rNode (j.val+1)) :=
  (matrixApply_mono transferMatrix_nonneg hx j).trans (actual_twentyone_matrix hδ hδhi j)

theorem profile_lower_of_nodes {w : Fin 21 → ℝ} {δ t x y : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1/1000) (hδ : 0 < δ) (hδt : δ ≤ t/2)
    (hw : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1)))
    (hv : (x,y) ∈ StaircaseShrink.domain t) :
    profile w (u x y) ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ x y) := by
  have hm : AntitoneOn (wuImprovementLimit false δ) (Icc 2 (41/10)) := by
    apply (wuImprovementLimit_lower_antitone hδ (by linarith)).mono
    intro s hs
    exact ⟨hs.1, by linarith [hs.2]⟩
  have hb := StaircaseShrink.source_budgets ht hδ hδt hv
  have hsu := hb.2.2.2.2.2.2.2
  have hs : StaircaseShrink.shiftedU δ x y ∈ Icc 2 (41/10) :=
    ⟨hb.2.2.2.2.2.2.1, hsu.trans (StaircaseShrink.original_u_upper hv)⟩
  change profile w (u x y) ≤ wuImprovementLimit false δ (StaircaseShrink.shiftedU δ x y)
  apply StaircaseShrink.eval_le_of_nodes (rows w) _ hm ?_ hs hsu
    (wuImprovementLimit_nonneg false hδ (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]))
  intro r hr
  refine ⟨row_endpoint w hr, ?_⟩
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  change w j ≤ wuImprovementLimit false δ (originalRow j).2.1
  rw [originalRow_node]
  exact hw j

theorem uniform_le_actual_of_nodes {w : Fin 21 → ℝ} {δ t : ℝ}
    (hn : ∀ j, 0 ≤ w j) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2)
    (hw : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1)))
    (v : ℝ × ℝ) :
    uniform w t v ≤ truncatedSixthMassHKernel δ v := by
  by_cases hv : v ∈ StaircaseShrink.domain t
  · have hvt : truncatedSixthLowerAdmissibleRegion t v.1 v.2 := by
      have he := congrArg (fun S : Set (ℝ × ℝ) => v ∈ S) (StaircaseActual.domain_eq ht.le)
      exact he.mp hv
    have hvd := StaircaseActual.region_mono (show δ ≤ t by linarith) hvt
    rw [uniform, if_pos hv, truncatedSixthMassHKernel, if_pos hvd]
    have hb := truncatedSixthLower_region_bounds hδ.le hvd.1
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤ v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.1.le hb.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    have hp := profile_nonneg hn (u v.1 v.2)
    have hl := profile_lower_of_nodes ht ht' hδ hδt hw hv
    exact div_le_div₀ (hp.trans hl) hl (StaircaseActual.denominator_pos hδ.le hvd) hz
  · rw [uniform, if_neg hv]
    exact (truncatedSixthMass_kernels_bounds hδ (by linarith) v).2.1

theorem Gamma_payment_of_nodes {w : Fin 21 → ℝ} {δ t : ℝ}
    (hn : ∀ j, 0 ≤ w j) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2)
    (hw : ∀ j, w j ≤ wuImprovementLimit false δ (rNode (j.val+1))) :
    Gamma w t ≤ truncatedSixthLowerHadmdelta δ := by
  rw [Gamma, (truncatedSixthMass_literal_integrals hδ (by linarith)).2]
  exact mul_le_mul_of_nonneg_left
    (integral_mono (uniform_integrable _ ht.le)
      (truncatedSixthMass_kernels_integrable hδ (by linarith)).2
      (uniform_le_actual_of_nodes hn ht ht' hδ hδt hw)) (by norm_num)

/-- The only loss is the original deleted strip; the input already pays its own delta loss. -/
theorem lowGain_trim_payment {x : Fin 9 → ℝ} {δ t : ℝ}
    (hn : ∀ i, 0 ≤ x i) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hx : ∀ i, x i ≤ actualNine δ i) :
    lowGain x-loss (matrixApply transferMatrix x)*t ≤ truncatedSixthLowerHadmdelta δ := by
  have hw := matrixApply_nonneg transferMatrix_nonneg hn
  have hl := (Gamma_loss hw ht.le ht').2
  have hp := Gamma_payment_of_nodes hw ht ht' hδ hδt
    (transferred_actual hδ (by linarith) hx)
  dsimp [lowGain]
  linarith only [hl, hp]

theorem lowGain_Hadm_payment {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d →
        lowGain x-ε ≤ truncatedSixthLowerHadmdelta δ := by
  let L := loss (matrixApply transferMatrix x)
  have hL : 0 ≤ L := loss_nonneg _
  let t : ℝ := min (1/1000) (ε/(L+1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by linarith))
  have ht' : t ≤ 1/1000 := min_le_left _ _
  have hpay : L*t < ε := by
    have h := (le_div_iff₀ (show 0 < L+1 by linarith)).mp
      (show t ≤ ε/(L+1) from min_le_right _ _)
    nlinarith only [h, ht]
  refine ⟨min d0 (min (1/100) (t/2)),
    lt_min hd0 (lt_min (by norm_num) (half_pos ht)), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro δ hδ hδd
  have hδ0 : δ ≤ d0 := hδd.le.trans (min_le_left _ _)
  have hδt : δ ≤ t/2 := hδd.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp := lowGain_trim_payment hn ht ht' hδ hδt (hx δ hδ hδ0)
  change lowGain x-L*t ≤ _ at hp
  linarith only [hp, hpay]

end WuTarget.W01
