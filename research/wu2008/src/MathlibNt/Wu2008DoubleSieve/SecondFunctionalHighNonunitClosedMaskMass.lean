import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitAffineDomains

namespace Wu2008DoubleSieve.HighNonunitLegal
open Set MeasureTheory
open scoped BigOperators Classical

-- Keep literal-mask conditionals on one uniform classical decision procedure.
noncomputable local instance (priority := high) affineDomainsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Every closed prime atom keeps its complete reciprocal product and legal kernel. -/
noncomputable def closedPrimeK20 (R a2 a3 b phi : ℝ) : ℝ :=
  ∑ f : Fin 5 → primeSlabPrimes R, if gridCoordinates R f ∈ D20 a2 a3 b phi then
    primeSlabWeight R f * G 3 phi (gridCoordinates R f) else 0

noncomputable def closedPrimeK21 (R a3 b phi : ℝ) : ℝ :=
  ∑ f : Fin 6 → primeSlabPrimes R, if gridCoordinates R f ∈ D21 a3 b phi then
    primeSlabWeight R f * G 4 phi (gridCoordinates R f) else 0

private theorem closed_atom {n : ℕ} (j : Fin n) (phi w : ℝ)
    (t : Fin n → ℝ) (P : Prop) :
    (if P ∧ t ∈ legal j phi then w * G j phi t else 0) =
      w * (if P then G j phi t else 0) := by
  by_cases hp : P <;> by_cases hl : t ∈ legal j phi <;>
    simp [hp, hl, G_of_illegal]

theorem closedPrimeK20_literal (R a2 a3 b phi : ℝ) :
    closedPrimeK20 R a2 a3 b phi =
      ∑ f : Fin 5 → primeSlabPrimes R, primeSlabWeight R f *
        (if ∀ q, (∑ i, C20 q i * gridCoordinates R f i) ≤ gamma20 a2 a3 b q
         then G 3 phi (gridCoordinates R f) else 0) := by
  unfold closedPrimeK20
  rw [D20_eq_closed_affine]
  apply Finset.sum_congr rfl
  intro f _
  simpa only [mem_inter_iff, mem_ofPred_eq] using
    (closed_atom 3 phi (primeSlabWeight R f) (gridCoordinates R f)
      (∀ q, (∑ i, C20 q i * gridCoordinates R f i) ≤ gamma20 a2 a3 b q))

theorem closedPrimeK21_literal (R a3 b phi : ℝ) :
    closedPrimeK21 R a3 b phi =
      ∑ f : Fin 6 → primeSlabPrimes R, primeSlabWeight R f *
        (if ∀ q, (∑ i, C21 q i * gridCoordinates R f i) ≤ gamma21 a3 b q
         then G 4 phi (gridCoordinates R f) else 0) := by
  unfold closedPrimeK21
  rw [D21_eq_closed_affine]
  apply Finset.sum_congr rfl
  intro f _
  simpa only [mem_inter_iff, mem_ofPred_eq] using
    (closed_atom 4 phi (primeSlabWeight R f) (gridCoordinates R f)
      (∀ q, (∑ i, C21 q i * gridCoordinates R f i) ≤ gamma21 a3 b q))

private theorem closed_indicator {n : ℕ} (j : Fin n) (phi : ℝ)
    (s : Set (Fin n → ℝ)) (t : Fin n → ℝ) :
    (s ∩ legal j phi).indicator (fun t => G j phi t * continuousDensity t) t =
      (if t ∈ s then G j phi t else 0) * continuousDensity t := by
  by_cases hs : t ∈ s <;> by_cases hl : t ∈ legal j phi <;>
    simp [Set.indicator, hs, hl, G_of_illegal]

theorem closed_mask_integrable {n : ℕ} {Q : Type*} [Countable Q]
    (j : Fin n) (phi : ℝ) (C : Q → Fin n → ℝ) (gamma : Q → ℝ) :
    IntegrableOn (fun t => (if ∀ q, (∑ i, C q i * t i) ≤ gamma q
      then G j phi t else 0) * continuousDensity t) (continuousCube n) := by
  have h := (G_weighted_integrable j phi).indicator
    ((closed_affine_measurable C gamma).inter (legal_measurable j phi))
  change IntegrableOn (fun t =>
    ({t | ∀ q, (∑ i, C q i * t i) ≤ gamma q} ∩ legal j phi).indicator
      (fun t => G j phi t * continuousDensity t) t) (continuousCube n) at h
  simpa only [closed_indicator, mem_ofPred_eq] using h

theorem closed_mask_measurable {n : ℕ} {Q : Type*} [Countable Q]
    (j : Fin n) (phi : ℝ) (C : Q → Fin n → ℝ) (gamma : Q → ℝ) :
    Measurable (fun t => (if ∀ q, (∑ i, C q i * t i) ≤ gamma q
      then G j phi t else 0) * continuousDensity t) := by
  have hg := (G_measurable j phi).indicator (closed_affine_measurable C gamma)
  have hd : Measurable (continuousDensity : (Fin n → ℝ) → ℝ) := by
    unfold continuousDensity
    fun_prop
  exact hg.mul hd

private theorem integral_closed_mask {n : ℕ} (j : Fin n) (phi : ℝ)
    (s : Set (Fin n → ℝ)) (hs : MeasurableSet s)
    (hsub : s ∩ legal j phi ⊆ continuousCube n) :
    (∫ t in s ∩ legal j phi, G j phi t * continuousDensity t) =
      ∫ t in continuousCube n, (if t ∈ s then G j phi t else 0) * continuousDensity t := by
  have h := setIntegral_indicator (μ := volume) (s := continuousCube n)
    (f := fun t => G j phi t * continuousDensity t) (hs.inter (legal_measurable j phi))
  rw [inter_eq_right.mpr hsub] at h
  simpa only [closed_indicator] using h.symm

theorem K20_closed_mask_integrable (a2 a3 b phi : ℝ) :
    IntegrableOn (fun t : Fin 5 → ℝ =>
      (if ∀ q, (∑ i, C20 q i * t i) ≤ gamma20 a2 a3 b q then G 3 phi t else 0) *
        continuousDensity t) (continuousCube 5) :=
  by simpa only using closed_mask_integrable 3 phi C20 (gamma20 a2 a3 b)

theorem K21_closed_mask_integrable (a3 b phi : ℝ) :
    IntegrableOn (fun t : Fin 6 → ℝ =>
      (if ∀ q, (∑ i, C21 q i * t i) ≤ gamma21 a3 b q then G 4 phi t else 0) *
        continuousDensity t) (continuousCube 6) :=
  by simpa only using closed_mask_integrable 4 phi C21 (gamma21 a3 b)

theorem K20_closed_mask_literal {a2 a3 b : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2)
    (phi : ℝ) :
    K20 a2 a3 b phi = ∫ t in continuousCube 5,
      (if ∀ q, (∑ i, C20 q i * t i) ≤ gamma20 a2 a3 b q then G 3 phi t else 0) *
        continuousDensity t := by
  have hsub := D20_subset_cube (a3 := a3) (phi := phi) ha hb
  rw [D20_eq_closed_affine] at hsub
  unfold K20
  rw [D20_eq_closed_affine]
  simpa only [mem_ofPred_eq] using
    integral_closed_mask 3 phi _ (closed_affine_measurable C20 (gamma20 a2 a3 b)) hsub

theorem K21_closed_mask_literal {a3 b : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2)
    (phi : ℝ) :
    K21 a3 b phi = ∫ t in continuousCube 6,
      (if ∀ q, (∑ i, C21 q i * t i) ≤ gamma21 a3 b q then G 4 phi t else 0) *
        continuousDensity t := by
  have hsub := D21_subset_cube (phi := phi) ha hb
  rw [D21_eq_closed_affine] at hsub
  unfold K21
  rw [D21_eq_closed_affine]
  simpa only [mem_ofPred_eq] using
    integral_closed_mask 4 phi _ (closed_affine_measurable C21 (gamma21 a3 b)) hsub

end Wu2008DoubleSieve.HighNonunitLegal
