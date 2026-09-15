import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitChamberIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousRectangle

open scoped BigOperators Classical
open MeasureTheory Set
namespace Wu2008DoubleSieve.HighUnit

/-- The active full graph box lies in the accepted free-coordinate cube. -/
theorem graphBox_cube {n : ℕ} {A B : Fin (n+1) → ℝ} {phi : ℝ}
    (hA : ∀ i, 1/10 ≤ A i) (hB : ∀ i, B i ≤ 1/2)
    {t : Fin n → ℝ} (ht : graphBox A B phi t) : t ∈ continuousCube n := by
  intro i _
  have hi := ht i.castSucc
  simpa only [append, Fin.snoc_castSucc, mem_Icc] using
    And.intro ((hA i.castSucc).trans hi.1) (hi.2.trans (hB i.castSucc))

/-- The S6 sum is the complete unsorted density almost everywhere. -/
theorem section21_sum_ae {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    (fun t => ∑ p : Equiv.Perm (Fin 6), section21 a b phi (graphPerm phi p t)) =ᵐ[volume]
      graphWeight (fun _ => a) (fun _ => b) phi := by
  filter_upwards [append_injective_ae (n := 5) phi] with t ht
  simp only [section21_chamber, append_graphPerm, graphWeight21_perm]
  by_cases hc : t ∈ continuousCube 5
  · exact weighted_sorting_partition (append phi t) (ht hc) _
  · have hw : graphWeight (fun _ : Fin 6 => a) (fun _ => b) phi t = 0 := by
      apply if_neg
      exact fun h => hc (graphBox_cube (fun _ => ha) (fun _ => hb) h)
    simp [hw]

/-- The S4 sum fixes the low label and includes the omitted high coordinate. -/
theorem section20_sum_ae {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    (fun t => ∑ p : Equiv.Perm (Fin 4), section20 a2 a b phi (graphPerm phi (fixLow p) t)) =ᵐ[volume]
      graphWeight (Fin.cons a2 (fun _ => a)) (Fin.cons a (fun _ => b)) phi := by
  filter_upwards [append_injective_ae (n := 4) phi] with t ht
  simp only [section20_chamber, append_graphPerm, fixLow_succ, graphWeight20_perm]
  by_cases hc : t ∈ continuousCube 4
  · exact weighted_sorting_partition (fun j : Fin 4 => append phi t j.succ)
      ((ht hc).comp (Fin.succ_injective 4)) _
  · have hw : graphWeight (Fin.cons a2 (fun _ : Fin 4 => a))
        (Fin.cons a (fun _ => b)) phi t = 0 := by
      apply if_neg
      intro h
      apply hc
      apply graphBox_cube (A := Fin.cons a2 (fun _ => a)) (B := Fin.cons a (fun _ => b)) _ _ h
      · intro i; exact Fin.cases ha (fun _ => ha.trans haa) i
      · intro i; exact Fin.cases (hab.trans hb) (fun _ => hb) i
    simp [hw]

/-- Unsorted integrability is produced from the already proved ordered sections. -/
theorem graphWeight21_integrable {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    Integrable (graphWeight (fun _ : Fin 6 => a) (fun _ => b) phi) := by
  have hi : ∀ p : Equiv.Perm (Fin 6), Integrable (fun t => section21 a b phi (graphPerm phi p t)) :=
    fun p => (graphPerm_measurePreserving phi p).integrable_comp_of_integrable (section21_integrable ha hb phi)
  exact (integrable_finsetSum _ (fun p _ => hi p)).congr (section21_sum_ae ha hb phi)

theorem graphWeight20_integrable {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    Integrable (graphWeight (Fin.cons a2 (fun _ : Fin 4 => a)) (Fin.cons a (fun _ => b)) phi) := by
  have hi : ∀ p : Equiv.Perm (Fin 4), Integrable (fun t => section20 a2 a b phi (graphPerm phi (fixLow p) t)) :=
    fun p => (graphPerm_measurePreserving phi (fixLow p)).integrable_comp_of_integrable (section20_integrable ha hb phi)
  exact (integrable_finsetSum _ (fun p _ => hi p)).congr (section20_sum_ae ha haa hab hb phi)

/-- The factorial is an integral identity for the original J, not a definition. -/
theorem J21_chamber_factor {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    720 * J21 a b phi = ∫ t, graphWeight (fun _ : Fin 6 => a) (fun _ => b) phi t := by
  rw [← integral_congr_ae (section21_sum_ae ha hb phi)]
  rw [integral_finsetSum (f := fun p t => section21 a b phi (graphPerm phi p t)) _ (fun p _ => (graphPerm_measurePreserving phi p).integrable_comp_of_integrable
    (section21_integrable ha hb phi))]
  simp only [integral_graphPerm]
  simp [J21, Fintype.card_perm, Nat.factorial]

theorem J20_chamber_factor {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    24 * J20 a2 a b phi = ∫ t, graphWeight (Fin.cons a2 (fun _ : Fin 4 => a))
      (Fin.cons a (fun _ => b)) phi t := by
  rw [← integral_congr_ae (section20_sum_ae ha haa hab hb phi)]
  rw [integral_finsetSum (f := fun p t => section20 a2 a b phi (graphPerm phi (fixLow p) t)) _ (fun p _ => (graphPerm_measurePreserving phi (fixLow p)).integrable_comp_of_integrable
    (section20_integrable ha hb phi))]
  simp only [integral_graphPerm]
  simp [J20, Fintype.card_perm, Nat.factorial]

/-- The reciprocal rectangle used below is measurable in the actual free coordinates. -/
theorem reciprocalRectangle_measurable {n : ℕ} (A B : Fin n → ℝ) :
    MeasurableSet (continuousRectangle A B) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- Positivity of the literal reciprocal density on a positive rectangle. -/
theorem rectangle_density_nonneg {n : ℕ} {A B : Fin n → ℝ}
    (hA : ∀ i, 1/10 ≤ A i) {t : Fin n → ℝ} (ht : t ∈ continuousRectangle A B) :
    0 ≤ continuousDensity t := by
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg zero_le_one (by linarith [(ht i (mem_univ i)).1, hA i])

/-- Only after symmetrization, discard the omitted reciprocal using its true lower gate. -/
theorem graphWeight_rectangle_bound {n : ℕ} (A B : Fin (n+1) → ℝ) (phi c : ℝ)
    (hc : 0 < c) (hA : ∀ i, 1/10 ≤ A i) (hlast : c ≤ A (Fin.last n))
    (t : Fin n → ℝ) :
    0 ≤ graphWeight A B phi t ∧ graphWeight A B phi t ≤
      (1/c) * (continuousRectangle (fun i => A i.castSucc) (fun i => B i.castSucc)).indicator
        continuousDensity t := by
  let R := continuousRectangle (fun i : Fin n => A i.castSucc) (fun i => B i.castSucc)
  have hpos : ∀ t ∈ R, 0 ≤ continuousDensity t :=
    fun t ht => rectangle_density_nonneg (fun i => hA i.castSucc) ht
  by_cases ht : graphBox A B phi t
  · have hr : t ∈ R := by
      intro i _
      simpa only [append, Fin.snoc_castSucc, mem_Icc] using ht i.castSucc
    have hv : c ≤ phi - ∑ i, t i := by
      simpa only [append, Fin.snoc_last] using hlast.trans (ht (Fin.last n)).1
    have hp : (∏ i, append phi t i) = (∏ i, t i) * (phi - ∑ i, t i) := by
      rw [Fin.prod_univ_castSucc]
      simp only [append, Fin.snoc_castSucc, Fin.snoc_last]
    rw [graphWeight, if_pos ht, hp, density_reciprocal, indicator_of_mem hr]
    exact ⟨mul_nonneg (div_nonneg zero_le_one (hc.le.trans hv)) (hpos t hr),
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hc hv) (hpos t hr)⟩
  · rw [graphWeight, if_neg ht]
    refine ⟨le_refl _, mul_nonneg (by positivity) ?_⟩
    by_cases hr : t ∈ R
    · rw [indicator_of_mem hr]
      exact hpos t hr
    · rw [indicator_of_notMem hr]

theorem reciprocalRectangle_log_integral {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 1/10 ≤ A i) (hAB : ∀ i, A i ≤ B i) :
    (∫ t in continuousRectangle A B, continuousDensity t) = ∏ i, Real.log (B i / A i) := by
  rw [continuousRectangle_factorization A B hAB]
  apply Finset.prod_congr rfl
  intro i _
  have ha : 0 < A i := by linarith [hA i]
  have hb : 0 < B i := ha.trans_le (hAB i)
  exact integral_one_div_of_pos ha hb

/-- An integral comparison with an actually integrable free reciprocal rectangle. -/
theorem graphWeight_integral_log_le {n : ℕ} (A B : Fin (n+1) → ℝ) (phi c : ℝ)
    (hc : 0 < c) (hA : ∀ i, 1/10 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hlast : c ≤ A (Fin.last n)) (hi : Integrable (graphWeight A B phi)) :
    (∫ t, graphWeight A B phi t) ≤ (1/c) * ∏ i : Fin n, Real.log (B i.castSucc / A i.castSucc) := by
  let A' : Fin n → ℝ := fun i => A i.castSucc
  let B' : Fin n → ℝ := fun i => B i.castSucc
  have hm := reciprocalRectangle_measurable A' B'
  have hr := (integrable_indicator_iff hm).mpr
    (continuousRectangle_integrable A' B' (fun i => hA i.castSucc))
  calc
    _ ≤ ∫ t, (1/c) * (continuousRectangle A' B').indicator continuousDensity t :=
      integral_mono hi (hr.const_mul (1/c)) (fun t => (graphWeight_rectangle_bound A B phi c hc hA hlast t).2)
    _ = _ := by
      rw [integral_const_mul, integral_indicator hm,
        reciprocalRectangle_log_integral A' B' (fun i => hA i.castSucc) (fun i => hAB i.castSucc)]

/-- All-real-phi logarithmic bound for the original five-free-coordinate J21. -/
theorem J21_log_cap {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    J21 a b phi ≤ Real.log (b/a)^5 / (720*a) := by
  have ha0 : 0 < a := by linarith
  have h := graphWeight_integral_log_le (fun _ : Fin 6 => a) (fun _ => b) phi a ha0
    (fun _ => ha) (fun _ => hab) (le_refl a) (graphWeight21_integrable ha hb phi)
  rw [← J21_chamber_factor ha hb phi] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply (le_div_iff₀ (by positivity : 0 < 720*a)).mpr
  have h' := (mul_le_mul_of_nonneg_right h ha0.le)
  field_simp at h'
  nlinarith [h']

/-- All-real-phi logarithmic bound with one low and three free high reciprocals. -/
theorem J20_log_cap {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    J20 a2 a b phi ≤ Real.log (a/a2) * Real.log (b/a)^3 / (24*a) := by
  have ha0 : 0 < a := by linarith
  have hA : ∀ i : Fin 5, (1:ℝ)/10 ≤ (Fin.cons a2 (fun _ => a) : Fin 5 → ℝ) i :=
    fun i => Fin.cases ha (fun _ => ha.trans haa) i
  have hAB : ∀ i : Fin 5, (Fin.cons a2 (fun _ => a) : Fin 5 → ℝ) i ≤ (Fin.cons a (fun _ => b) : Fin 5 → ℝ) i :=
    fun i => Fin.cases haa (fun _ => hab) i
  have h := graphWeight_integral_log_le (Fin.cons a2 (fun _ : Fin 4 => a))
    (Fin.cons a (fun _ => b)) phi a ha0 hA hAB (le_refl a)
    (graphWeight20_integrable ha haa hab hb phi)
  rw [← J20_chamber_factor ha haa hab hb phi, Fin.prod_univ_succ] at h
  simp only [Fin.castSucc_zero, ← Fin.succ_castSucc, Fin.cons_zero, Fin.cons_succ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply (le_div_iff₀ (by positivity : 0 < 24*a)).mpr
  have h' := mul_le_mul_of_nonneg_right h ha0.le
  field_simp at h'
  nlinarith [h']

/-- Nonnegativity uses the full zero-extended graph density. -/
theorem J21_nonneg {a b : ℝ} (ha : 1/10 ≤ a) (hb : b ≤ 1/2) (phi : ℝ) :
    0 ≤ J21 a b phi := by
  have ha0 : 0 < a := by linarith
  have h : (0:ℝ) ≤ ∫ t, graphWeight (fun _ : Fin 6 => a) (fun _ => b) phi t :=
    integral_nonneg (fun t : Fin 5 → ℝ =>
    (graphWeight_rectangle_bound (fun _ => a) (fun _ => b) phi a ha0
      (fun _ => ha) (le_refl a) t).1)
  rw [← J21_chamber_factor ha hb phi] at h
  linarith

theorem J20_nonneg {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    0 ≤ J20 a2 a b phi := by
  have ha0 : 0 < a := by linarith
  have hA : ∀ i : Fin 5, (1:ℝ)/10 ≤ (Fin.cons a2 (fun _ => a) : Fin 5 → ℝ) i :=
    fun i => Fin.cases ha (fun _ => ha.trans haa) i
  have h : (0:ℝ) ≤ ∫ t, graphWeight (Fin.cons a2 (fun _ : Fin 4 => a)) (Fin.cons a (fun _ => b)) phi t :=
    integral_nonneg (fun t : Fin 4 → ℝ =>
    (graphWeight_rectangle_bound (Fin.cons a2 (fun _ => a)) (Fin.cons a (fun _ => b))
      phi a ha0 hA (le_refl a) t).1)
  rw [← J20_chamber_factor ha haa hab hb phi] at h
  linarith

/-- The concrete endpoint has only compact window hypotheses and arbitrary real phi. -/
theorem J21_log_bounds {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    0 ≤ J21 a b phi ∧ J21 a b phi ≤ Real.log (b/a)^5 / (720*a) :=
  ⟨J21_nonneg ha hb phi, J21_log_cap ha hab hb phi⟩

theorem J20_log_bounds {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) :
    0 ≤ J20 a2 a b phi ∧ J20 a2 a b phi ≤ Real.log (a/a2) * Real.log (b/a)^3 / (24*a) :=
  ⟨J20_nonneg ha haa hab hb phi, J20_log_cap ha haa hab hb phi⟩

/-- Zero high width follows from the same logarithmic endpoint, without dividing by width. -/
theorem J21_log_zero_width {a : ℝ} (ha : 1/10 ≤ a) (hb : a ≤ 1/2) (phi : ℝ) :
    J21 a a phi = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have h := J21_log_bounds ha (le_refl a) hb phi
  apply le_antisymm _ h.1
  simpa [div_self ha0] using h.2

/-- Both possible zero widths are included in the actual J20 log cap. -/
theorem J20_log_zero_width {a2 a b : ℝ} (ha : 1/10 ≤ a2) (haa : a2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) (phi : ℝ) (hz : a2 = a ∨ a = b) :
    J20 a2 a b phi = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have h := J20_log_bounds ha haa hab hb phi
  apply le_antisymm _ h.1
  rcases hz with hz | hz
  · simpa [hz, div_self ha0] using h.2
  · simpa [← hz, div_self ha0] using h.2

end Wu2008DoubleSieve.HighUnit
