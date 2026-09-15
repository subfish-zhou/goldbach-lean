import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitLegalKernel

/-! Genuine five/six-dimensional weighted Lebesgue masses, with the penultimate
coordinate selected. Degenerate windows retain these same integral objects. -/
namespace Wu2008DoubleSieve.HighNonunitLegal
open Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators

/-- Closed continuous colour/order domain for the complete word [2,3,3,3,3]. -/
def D20 (a2 a3 b phi : ℝ) : Set (Fin 5 → ℝ) :=
  {t | a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧ Monotone t ∧ t 4 ≤ b} ∩ legal 3 phi

/-- Closed continuous colour/order domain for the complete word [3,3,3,3,3,3]. -/
def D21 (a3 b phi : ℝ) : Set (Fin 6 → ℝ) :=
  {t | a3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ b} ∩ legal 4 phi

noncomputable def K20 (a2 a3 b phi : ℝ) : ℝ :=
  ∫ t in D20 a2 a3 b phi, G 3 phi t * continuousDensity t

noncomputable def K21 (a3 b phi : ℝ) : ℝ :=
  ∫ t in D21 a3 b phi, G 4 phi t * continuousDensity t

theorem monotone_measurable (n : ℕ) : MeasurableSet {t : Fin n → ℝ | Monotone t} := by
  change MeasurableSet {t : Fin n → ℝ | ∀ i j, i ≤ j → t i ≤ t j}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))))

theorem D20_measurable (a2 a3 b phi : ℝ) : MeasurableSet (D20 a2 a3 b phi) := by
  unfold D20
  exact ((measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    ((measurableSet_le measurable_const (measurable_pi_apply 1)).inter
    ((monotone_measurable 5).inter
    (measurableSet_le (measurable_pi_apply 4) measurable_const))))).inter (legal_measurable 3 phi)

theorem D21_measurable (a3 b phi : ℝ) : MeasurableSet (D21 a3 b phi) := by
  unfold D21
  exact ((measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((monotone_measurable 6).inter
    (measurableSet_le (measurable_pi_apply 5) measurable_const))).inter (legal_measurable 4 phi)

theorem D20_subset_cube {a2 a3 b phi : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2) :
    D20 a2 a3 b phi ⊆ continuousCube 5 := by
  intro t ht i _
  exact ⟨ha.trans (ht.1.1.trans (ht.1.2.2.2.1 (Fin.zero_le i))),
    (ht.1.2.2.2.1 (show i ≤ 4 from Fin.le_last i)).trans (ht.1.2.2.2.2.trans hb)⟩

theorem D21_subset_cube {a3 b phi : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2) :
    D21 a3 b phi ⊆ continuousCube 6 := by
  intro t ht i _
  exact ⟨ha.trans (ht.1.1.trans (ht.1.2.1 (Fin.zero_le i))),
    (ht.1.2.1 (show i ≤ 5 from Fin.le_last i)).trans (ht.1.2.2.trans hb)⟩

theorem weighted_integrable_on {n : ℕ} (j : Fin n) (phi : ℝ) {s : Set (Fin n → ℝ)}
    (hs : s ⊆ continuousCube n) :
    IntegrableOn (fun t => G j phi t * continuousDensity t) s :=
  (G_weighted_integrable j phi).mono_set hs

/-- A fixed coarse cap used only for errors, not for the leading mass. -/
theorem integral_bounds {n : ℕ} (j : Fin n) (phi : ℝ) {s : Set (Fin n → ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ continuousCube n) :
    0 ≤ (∫ t in s, G j phi t * continuousDensity t) ∧
    (∫ t in s, G j phi t * continuousDensity t) ≤ 10 * (4 : ℝ) ^ n := by
  constructor
  · apply setIntegral_nonneg hs
    intro t ht
    exact mul_nonneg (G_bounds j phi (hsub ht)).1 (continuousDensity_nonneg (hsub ht))
  · calc
      _ ≤ ∫ t in s, 10 * continuousDensity t := by
        apply setIntegral_mono_on (weighted_integrable_on j phi hsub)
          (((continuousDensity_integrable n).mono_set hsub).const_mul 10) hs
        intro t ht
        exact mul_le_mul_of_nonneg_right (G_bounds j phi (hsub ht)).2
          (continuousDensity_nonneg (hsub ht))
      _ ≤ ∫ t in continuousCube n, 10 * continuousDensity t := by
        apply setIntegral_mono_set ((continuousDensity_integrable n).const_mul 10) _
          (Filter.Eventually.of_forall hsub)
        filter_upwards [ae_restrict_mem (continuousCube_measurable n)] with t ht
        exact mul_nonneg (by norm_num) (continuousDensity_nonneg ht)
      _ = 10 * (∫ t in continuousCube n, continuousDensity t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (continuousCube_integral_bounds n).2 (by norm_num)

theorem K20_integrable {a2 a3 b : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2) (phi : ℝ) :
    IntegrableOn (fun t => G 3 phi t * continuousDensity t) (D20 a2 a3 b phi) :=
  weighted_integrable_on 3 phi (D20_subset_cube ha hb)

theorem K21_integrable {a3 b : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2) (phi : ℝ) :
    IntegrableOn (fun t => G 4 phi t * continuousDensity t) (D21 a3 b phi) :=
  weighted_integrable_on 4 phi (D21_subset_cube ha hb)

theorem K20_bounds {a2 a3 b : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2) (phi : ℝ) :
    0 ≤ K20 a2 a3 b phi ∧ K20 a2 a3 b phi ≤ 10 * (4 : ℝ) ^ 5 :=
  integral_bounds 3 phi (D20_measurable a2 a3 b phi) (D20_subset_cube ha hb)

theorem K21_bounds {a3 b : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2) (phi : ℝ) :
    0 ≤ K21 a3 b phi ∧ K21 a3 b phi ≤ 10 * (4 : ℝ) ^ 6 :=
  integral_bounds 4 phi (D21_measurable a3 b phi) (D21_subset_cube ha hb)

/-- Exact density identity, retaining the extra reciprocal at the selected coordinate. -/
theorem weighted_formula {n : ℕ} {j : Fin n} {phi : ℝ} {t : Fin n → ℝ}
    (hl : t ∈ legal j phi) :
    G j phi t * continuousDensity t =
      buchstab ((phi - ∑ i, t i) / t j) / (t j * ∏ i, t i) := by
  rw [G_of_legal hl]
  unfold continuousDensity
  simp only [one_div]
  rw [Finset.prod_inv_distrib]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The denominator contains precisely the square of the penultimate coordinate. -/
theorem weighted_formula_square {n : ℕ} {j : Fin n} {phi : ℝ} {t : Fin n → ℝ}
    (hl : t ∈ legal j phi) :
    G j phi t * continuousDensity t =
      buchstab ((phi - ∑ i, t i) / t j) /
        (t j ^ 2 * ∏ i ∈ Finset.univ.erase j, t i) := by
  rw [weighted_formula hl, ← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ j)]
  congr 1
  ring

theorem K20_literal (a2 a3 b phi : ℝ) :
    K20 a2 a3 b phi = ∫ t in D20 a2 a3 b phi,
      buchstab ((phi - ∑ i, t i) / t 3) / (t 3 * ∏ i, t i) := by
  apply setIntegral_congr_fun (D20_measurable a2 a3 b phi)
  intro t ht
  exact weighted_formula ht.2

theorem K21_literal (a3 b phi : ℝ) :
    K21 a3 b phi = ∫ t in D21 a3 b phi,
      buchstab ((phi - ∑ i, t i) / t 4) / (t 4 * ∏ i, t i) := by
  apply setIntegral_congr_fun (D21_measurable a3 b phi)
  intro t ht
  exact weighted_formula ht.2

theorem literal_integrable_on {n : ℕ} (j : Fin n) (phi : ℝ) {s : Set (Fin n → ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ continuousCube n) (hl : s ⊆ legal j phi) :
    IntegrableOn (fun t => buchstab ((phi - ∑ i, t i) / t j) / (t j * ∏ i, t i)) s :=
  (weighted_integrable_on j phi hsub).congr_fun (fun _ ht => weighted_formula (hl ht)) hs

/-- Five coordinates, with precisely the fourth coordinate squared. -/
theorem K20_expanded (a2 a3 b phi : ℝ) :
    K20 a2 a3 b phi = ∫ t in D20 a2 a3 b phi,
      buchstab ((phi - ∑ i, t i) / t 3) / (t 0 * t 1 * t 2 * t 3 ^ 2 * t 4) := by
  rw [K20_literal]
  apply setIntegral_congr_fun (D20_measurable a2 a3 b phi)
  intro t _
  have hd : t 3 * (∏ i, t i) = t 0 * t 1 * t 2 * t 3 ^ 2 * t 4 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change t 3 * (t 0 * (t 1 * (t 2 * (t 3 * t 4)))) = _
    ring
  dsimp only
  rw [hd]

/-- Six coordinates, with precisely the fifth coordinate squared. -/
theorem K21_expanded (a3 b phi : ℝ) :
    K21 a3 b phi = ∫ t in D21 a3 b phi,
      buchstab ((phi - ∑ i, t i) / t 4) / (t 0 * t 1 * t 2 * t 3 * t 4 ^ 2 * t 5) := by
  rw [K21_literal]
  apply setIntegral_congr_fun (D21_measurable a3 b phi)
  intro t _
  have hd : t 4 * (∏ i, t i) = t 0 * t 1 * t 2 * t 3 * t 4 ^ 2 * t 5 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change t 4 * (t 0 * (t 1 * (t 2 * (t 3 * (t 4 * t 5))))) = _
    ring
  dsimp only
  rw [hd]

end Wu2008DoubleSieve.HighNonunitLegal
