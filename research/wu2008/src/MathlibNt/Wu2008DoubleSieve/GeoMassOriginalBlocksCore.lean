import MathlibNt.Wu2008DoubleSieve.GeoMassOrderedBase

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

/-- Concatenation of two coordinate blocks, with the original coordinate order. -/
noncomputable def join (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (m+n) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m+n) => ℝ) finSumFinEquiv)

theorem join_preserving (m n : ℕ) : MeasurePreserving (join m n) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (m+n) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => ℝ))

theorem join_apply (m n : ℕ) (z : (Fin m → ℝ) × (Fin n → ℝ)) :
    join m n z = Fin.append z.1 z.2 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [join, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm]

/-- Fubini on genuine product blocks; absolute integrability is used explicitly. -/
theorem integral_blocks {m n : ℕ} (D : Set (Fin (m+n) → ℝ))
    (A : Set (Fin m → ℝ)) (B : Set (Fin n → ℝ))
    (w : (Fin (m+n) → ℝ) → ℝ) (u : (Fin m → ℝ) → ℝ)
    (v : (Fin n → ℝ) → ℝ)
    (hD : join m n ⁻¹' D = A ×ˢ B)
    (hw : ∀ z, w (join m n z) = u z.1 * v z.2)
    (hu : IntegrableOn u A) (hv : IntegrableOn v B) :
    (∫ t in D, w t) = (∫ x in A, u x) * (∫ y in B, v y) := by
  rw [← (join_preserving m n).setIntegral_preimage_emb
    (join m n).measurableEmbedding, hD]
  simp_rw [hw]
  rw [MeasureTheory.Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod _ (hu.mul_prod hv)]
  simp_rw [integral_const_mul, integral_mul_const]

theorem ordered_selected_integrable {n : ℕ} (j : Fin n) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (geometricWeight j) (orderedDomain n a b) := by
  apply (rectangle_integrable j (fun _ => a) (fun _ => b) (fun _ => ha)).mono_set
  intro t ht i _hi
  exact ht.1 i

theorem ordered_pure_integrable (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn continuousDensity (orderedDomain n a b) := by
  have hi : IntegrableOn (@continuousDensity n) (continuousRectangle (fun _ => a) (fun _ => b)) := by
    change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
    rw [continuousRectangle, Measure.restrict_pi_pi]
    apply Integrable.fintype_prod
    intro i
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id
      (fun x hx => ne_of_gt (ha.trans_le hx.1))
  apply hi.mono_set
  intro t ht i _hi
  exact ht.1 i

theorem density_join {m n : ℕ} (z : (Fin m → ℝ) × (Fin n → ℝ)) :
    continuousDensity (join m n z) = continuousDensity z.1 * continuousDensity z.2 := by
  rw [join_apply]
  simp only [continuousDensity, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem weight_join_left {m n : ℕ} (j : Fin m) (z : (Fin m → ℝ) × (Fin n → ℝ)) :
    geometricWeight (j.castAdd n) (join m n z) =
      geometricWeight j z.1 * continuousDensity z.2 := by
  unfold geometricWeight
  rw [density_join, join_apply, Fin.append_left]
  ring

theorem weight_join_right {m n : ℕ} (j : Fin n) (z : (Fin m → ℝ) × (Fin n → ℝ)) :
    geometricWeight (j.natAdd m) (join m n z) =
      continuousDensity z.1 * geometricWeight j z.2 := by
  unfold geometricWeight
  rw [density_join, join_apply, Fin.append_right]
  ring

/-- Selected coordinate stays in the left block; no closed simplex formula is used. -/
theorem mass_blocks_left {m n : ℕ} (j : Fin m) {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (D : Set (Fin (m+n) → ℝ))
    (hD : join m n ⁻¹' D = orderedDomain m a b ×ˢ orderedDomain n c d) :
    geometricMass (j.castAdd n) D = selectedOrderedMass j a b * pureOrderedMass n c d :=
  integral_blocks D _ _ _ _ _ hD (weight_join_left j)
    (ordered_selected_integrable j ha) (ordered_pure_integrable n hc)

/-- Selected coordinate stays in the right block, including its index shift. -/
theorem mass_blocks_right {m n : ℕ} (j : Fin n) {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (D : Set (Fin (m+n) → ℝ))
    (hD : join m n ⁻¹' D = orderedDomain m a b ×ˢ orderedDomain n c d) :
    geometricMass (j.natAdd m) D = pureOrderedMass m a b * selectedOrderedMass j c d :=
  integral_blocks D _ _ _ _ _ hD (weight_join_right j)
    (ordered_pure_integrable m ha) (ordered_selected_integrable j hc)

/-- The only pure mass evaluated here is one coordinate. -/
theorem pure_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    pureOrderedMass 1 a b = Real.log (b/a) := by
  unfold pureOrderedMass
  have h := ((volume_preserving_funUnique (Fin 1) ℝ).symm
    (MeasurableEquiv.funUnique (Fin 1) ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
    (@continuousDensity 1) (orderedDomain 1 a b)
  erw [← h]
  have hD : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹' orderedDomain 1 a b = Icc a b := by
    ext x
    simp [orderedDomain, Fin.monotone_iff_le_succ, Fin.forall_fin_one]
  rw [hD]
  change (∫ x in Icc a b, ∏ _i : Fin 1, 1 / x) = _
  simp only [Fin.prod_univ_one]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
