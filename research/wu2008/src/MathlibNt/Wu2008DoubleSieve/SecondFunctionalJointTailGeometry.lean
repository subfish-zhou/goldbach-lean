import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledKernel

/-! Tail geometry for the literal same-parameter kernels. Unit sections are
handled separately from the full-dimensional Buchstab integrals. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory
open scoped BigOperators

/-- A coordinate-independent sum bound on the authoritative reciprocal cube. -/
theorem cube_sum_le {n : ℕ} {t : Fin n → ℝ} (ht : t ∈ continuousCube n) :
    (∑ i, t i) ≤ (n : ℝ) / 2 := by
  calc
    _ ≤ ∑ _i : Fin n, (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (ht i (mem_univ i)).2)
    _ = _ := by simp [div_eq_mul_inv]

/-- A genuine argument threshold, uniform on the entire cube. -/
theorem cube_argument_ge {n : ℕ} (j : Fin n) {m phi : ℝ}
    (hm : 0 ≤ m) (hphi : ((n : ℝ) + m) / 2 ≤ phi)
    {t : Fin n → ℝ} (ht : t ∈ continuousCube n) :
    m ≤ (phi - ∑ i, t i) / t j := by
  have hj := ht j (mem_univ j)
  have hs := cube_sum_le ht
  have hmul := mul_le_mul_of_nonneg_left hj.2 hm
  apply (le_div_iff₀ (by linarith [hj.1] : 0 < t j)).2
  linarith

/-- Once the displayed threshold is crossed, the original legal gate is redundant. -/
theorem cube_legal {n : ℕ} (j : Fin n) {phi : ℝ}
    (hphi : ((n : ℝ) + 1) / 2 ≤ phi) :
    continuousCube n ⊆ HighNonunitLegal.legal j phi := by
  intro t ht
  have hs := cube_sum_le ht
  have hj := (ht j (mem_univ j)).2
  change (∑ i, t i) + t j ≤ phi
  linarith

/-- All dimensions used in the twelve Buchstab terms share this threshold. -/
theorem argument_ge_six {n : ℕ} (hn : n ≤ 6) (j : Fin n) {m phi : ℝ}
    (hm : 0 ≤ m) (hphi : (6 + m) / 2 ≤ phi)
    {t : Fin n → ℝ} (ht : t ∈ continuousCube n) :
    m ≤ (phi - ∑ i, t i) / t j := by
  apply cube_argument_ge j hm _ ht
  have hn' : (n : ℝ) ≤ 6 := by exact_mod_cast hn
  linarith

theorem sum_four (t : Fin 4 → ℝ) : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change t 0 + (t 1 + (t 2 + t 3)) = _
  ring

theorem sum_five (t : Fin 5 → ℝ) : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 + t 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change t 0 + (t 1 + (t 2 + (t 3 + t 4))) = _
  ring

/-- The precise closed support interval of the five-coordinate unit chain. -/
theorem unit20_support {a2 a3 b phi : ℝ} {t : Fin 4 → ℝ}
    (ht : HighUnit.D20 a2 a3 b (HighUnit.append phi t)) :
    a2 + 4 * a3 ≤ phi ∧ phi ≤ a3 + 4 * b := by
  rcases (HighUnit.D20_append a2 a3 b phi t).mp ht with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  simp only [sum_four] at h5 h6
  constructor <;> linarith

/-- The precise closed support interval of the six-coordinate unit chain. -/
theorem unit21_support {a3 b phi : ℝ} {t : Fin 5 → ℝ}
    (ht : HighUnit.D21 a3 b (HighUnit.append phi t)) :
    6 * a3 ≤ phi ∧ phi ≤ 6 * b := by
  rcases (HighUnit.D21_append a3 b phi t).mp ht with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  simp only [sum_five] at h5 h6
  constructor <;> linarith

/-- Above the support, vanishing is pointwise, not a Buchstab approximation. -/
theorem J20_zero_of_gt {a2 a3 b phi : ℝ} (hphi : a3 + 4 * b < phi) :
    HighUnit.J20 a2 a3 b phi = 0 := by
  have he (t : Fin 4 → ℝ) : HighUnit.section20 a2 a3 b phi t = 0 := by
    apply if_neg
    intro ht
    exact (not_le_of_gt hphi) (unit20_support ht).2
  simp only [HighUnit.J20, he, integral_zero]

/-- The six-coordinate unit section is also exactly zero beyond its support. -/
theorem J21_zero_of_gt {a3 b phi : ℝ} (hphi : 6 * b < phi) :
    HighUnit.J21 a3 b phi = 0 := by
  have he (t : Fin 5 → ℝ) : HighUnit.section21 a3 b phi t = 0 := by
    apply if_neg
    intro ht
    exact (not_le_of_gt hphi) (unit21_support ht).2
  simp only [HighUnit.J21, he, integral_zero]

/-- The endpoint section is null as well; no finite prime atoms are removed. -/
theorem J20_zero_of_ge {a2 a3 b phi : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2)
    (hphi : a3 + 4 * b ≤ phi) : HighUnit.J20 a2 a3 b phi = 0 := by
  unfold HighUnit.J20
  calc
    _ = ∫ _t : Fin 4 → ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [HighUnit.cap_ae (0 : Fin 4) phi b] with t ht
      unfold HighUnit.section20
      split_ifs with hd
      · have hc := HighUnit.D20_cube ha hb hd
        have hn := ht hc
        rcases (HighUnit.D20_append a2 a3 b phi t).mp hd with
          ⟨h0, h1, h2, h3, h4, h5, h6⟩
        exfalso
        apply hn
        simp only [sum_four] at h5 h6 ⊢
        linarith
      · rfl
    _ = 0 := integral_zero _ _

/-- Endpoint nullness for the six-coordinate section. -/
theorem J21_zero_of_ge {a3 b phi : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2)
    (hphi : 6 * b ≤ phi) : HighUnit.J21 a3 b phi = 0 := by
  unfold HighUnit.J21
  calc
    _ = ∫ _t : Fin 5 → ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [HighUnit.cap_ae (0 : Fin 5) phi b] with t ht
      unfold HighUnit.section21
      split_ifs with hd
      · have hc := HighUnit.D21_cube ha hb hd
        have hn := ht hc
        rcases (HighUnit.D21_append a3 b phi t).mp hd with
          ⟨h0, h1, h2, h3, h4, h5, h6⟩
        exfalso
        apply hn
        simp only [sum_five] at h5 h6 ⊢
        linarith
      · rfl
    _ = 0 := integral_zero _ _

/-- The original five-dimensional domain, with only its now-redundant gate removed. -/
theorem D20_eq_of_tail {a2 a3 b phi : ℝ} (hphi : a3 + 5 * b ≤ phi) :
    HighNonunitLegal.D20 a2 a3 b phi =
      {t : Fin 5 → ℝ | a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧
        Monotone t ∧ t 4 ≤ b} := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, ?_⟩
    have h1 : t 1 ≤ t 4 := ht.2.2.2.1 (Fin.le_last (1 : Fin 5))
    have h2 : t 2 ≤ t 4 := ht.2.2.2.1 (Fin.le_last (2 : Fin 5))
    have h3 : t 3 ≤ t 4 := ht.2.2.2.1 (Fin.le_last (3 : Fin 5))
    change (∑ i, t i) + t 3 ≤ phi
    rw [sum_five]
    linarith [ht.2.1, ht.2.2.2.2]

/-- The six-dimensional gate disappears at the exact endpoint 7*b. -/
theorem D21_eq_of_tail {a3 b phi : ℝ} (hphi : 7 * b ≤ phi) :
    HighNonunitLegal.D21 a3 b phi =
      {t : Fin 6 → ℝ | a3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ b} := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    refine ⟨ht, ?_⟩
    have hs : (∑ i, t i) ≤ 6 * b := by
      calc
        _ ≤ ∑ _i : Fin 6, b := Finset.sum_le_sum (fun i _ =>
          (ht.2.1 (Fin.le_last i)).trans ht.2.2)
        _ = _ := by simp
    have hj := (ht.2.1 (Fin.le_last (4 : Fin 6))).trans ht.2.2
    change (∑ i, t i) + t 4 ≤ phi
    linarith

/-- At one common tail parameter both unit summands vanish exactly. -/
theorem mother_unit_pair_zero (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 3 ≤ phi) :
    HighUnit.J20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi = 0 ∧
      HighUnit.J21 (1 / p.kappa3) (1 / p.s) phi = 0 := by
  obtain ⟨ha, haa, hab, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  constructor
  · apply J20_zero_of_ge ha hb
    linarith
  · apply J21_zero_of_ge (ha.trans haa) hb
    linarith

/-- The actual fourteen-term kernel becomes exactly its twelve Buchstab terms,
with the same phi retained in every summand. -/
theorem mother_kernel_tail (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 3 ≤ phi) :
    SecondFunctionalCoupled.kernel p phi =
      (∑ j : Fin 6, LowerTripleContinuous.K (1 / p.S) (1 / p.kappa1)
        (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) j phi) +
      ((HighNonunitLegal.K20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi +
        HighNonunitLegal.K21 (1 / p.kappa3) (1 / p.s) phi) +
        ∑ j : Fin 4, FourPrimeNonunit.legalK (1 / p.kappa1) (1 / p.kappa2)
          (1 / p.kappa3) (1 / p.s) phi j) := by
  obtain ⟨h20, h21⟩ := mother_unit_pair_zero p hp hs hphi
  simp only [SecondFunctionalCoupled.kernel, h20, h21, add_zero, zero_add]

end Wu2008DoubleSieve.SecondFunctionalJointTail
