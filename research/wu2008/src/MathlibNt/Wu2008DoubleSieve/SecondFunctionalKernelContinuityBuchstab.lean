import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailGeometry

/-! Parameter continuity of the original gated Buchstab integrals. The null
face is removed separately for each fixed parameter, never uniformly in it. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory Filter
open scoped BigOperators Topology

 theorem legal_face_ae {n : ℕ} (j : Fin n) (phi : ℝ) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → (∑ i, t i) + t j ≠ phi := by
  have he := measure_eq_zero_iff_ae_notMem.mp (HighNonunitLegal.legal_face_null j phi)
  filter_upwards [he] with t hn ht heq
  exact hn ⟨ht, heq⟩

/-- Only the stable legal branch invokes Buchstab continuity. -/
theorem G_phi_continuousAt {n : ℕ} (j : Fin n) {phi : ℝ}
    {t : Fin n → ℝ} (ht : t ∈ continuousCube n)
    (hne : (∑ i, t i) + t j ≠ phi) :
    ContinuousAt (fun x => HighNonunitLegal.G j x t) phi := by
  have hj : 0 < t j := by linarith [(ht j (mem_univ j)).1]
  rcases lt_or_gt_of_ne hne with hl | hi
  · have he : ∀ᶠ x in 𝓝 phi, t ∈ HighNonunitLegal.legal j x :=
      (eventually_gt_nhds hl).mono (fun _ hx => hx.le)
    have hu : 1 < (phi - ∑ i, t i) / t j := by
      apply (lt_div_iff₀ hj).2
      linarith
    have harg : ContinuousAt (fun x : ℝ => (x - ∑ i, t i) / t j) phi :=
      (continuousAt_id.sub_const _).div_const _
    have hb0 : ContinuousAt LiLiuPrereqBuchstab.buchstab ((phi - ∑ i, t i) / t j) :=
      (LiLiuPrereqBuchstab.continuous_buchstab.continuousOn (s := Ici 1)).continuousAt
        (Ici_mem_nhds hu)
    have hb : ContinuousAt (fun x => LiLiuPrereqBuchstab.buchstab
        ((x - ∑ i, t i) / t j)) phi :=
      hb0.comp (x := phi) (f := fun x : ℝ => (x - ∑ i, t i) / t j) harg
    exact (hb.div_const (t j)).congr_of_eventuallyEq
      (he.mono (fun _ hx => HighNonunitLegal.G_of_legal hx))
  · have he : ∀ᶠ x in 𝓝 phi, t ∉ HighNonunitLegal.legal j x :=
      (eventually_lt_nhds hi).mono (fun _ hx => not_le_of_gt hx)
    exact continuousAt_const.congr_of_eventuallyEq
      (he.mono (fun _ hx => HighNonunitLegal.G_of_illegal hx))

/-- Genuine DCT with the original reciprocal density as an integrable majorant. -/
theorem buchstab_integral_continuous {n : ℕ} (j : Fin n)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    Continuous (fun phi => ∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t) := by
  rw [continuous_iff_continuousAt]
  intro phi
  apply continuousAt_of_dominated (bound := fun t => 10 * continuousDensity t)
  · exact Eventually.of_forall (fun x =>
      (HighNonunitLegal.G_weighted_integrable j x).mono_set hsub |>.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro x
    filter_upwards [ae_restrict_mem hD] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (HighNonunitLegal.G_bounds j x (hsub ht)).1
        (continuousDensity_nonneg (hsub ht)))]
    exact mul_le_mul_of_nonneg_right (HighNonunitLegal.G_bounds j x (hsub ht)).2
      (continuousDensity_nonneg (hsub ht))
  · exact ((continuousDensity_integrable n).mono_set hsub).const_mul 10
  · filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae (legal_face_ae j phi)] with t ht hn
    exact (G_phi_continuousAt j (hsub ht) (hn (hsub ht))).mul_const _

/-- All six original lower domains, for arbitrary admissible reciprocal parameters. -/
theorem lower_K_continuous {a b c e f : ℝ}
    (hp : LowerTripleContinuous.CompactParameters a b c e f) (j : Fin 6) :
    Continuous (LowerTripleContinuous.K a b c e f j) :=
  buchstab_integral_continuous 1 _ (LowerTripleContinuous.D_measurable a b c e f j)
    (LowerTripleContinuous.D_subset_cube hp j)

end Wu2008DoubleSieve.SecondFunctionalJointTail
