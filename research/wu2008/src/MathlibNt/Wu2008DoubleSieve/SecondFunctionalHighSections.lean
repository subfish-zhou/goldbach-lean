import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighDictionary

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnit
open Set MeasureTheory SecondFunctionalUnitKernel SecondFunctionalUnitFiniteKernel

/-- Append the unit-section coordinate, without imposing a cube restriction. -/
noncomputable def append {n : ℕ} (phi : ℝ) (t : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc t (phi - ∑ i, t i)

/-- These are full-space unit sections of the original closed D domains, not Wu's I. -/
noncomputable def section20 (a2 a3 b phi : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  if D20 a2 a3 b (append phi t) then 1 / ((∏ i, t i) * (phi - ∑ i, t i)) else 0
noncomputable def section21 (a3 b phi : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  if D21 a3 b (append phi t) then 1 / ((∏ i, t i) * (phi - ∑ i, t i)) else 0
noncomputable def J20 (a2 a3 b phi : ℝ) : ℝ := ∫ t, section20 a2 a3 b phi t
noncomputable def J21 (a3 b phi : ℝ) : ℝ := ∫ t, section21 a3 b phi t

/-- Closed affine gates are used only as an intermediate proved dictionary. -/
def closedMask {n r : ℕ} (C : Fin r → Fin n → ℝ) (gamma : Fin r → ℝ)
    (t : Fin n → ℝ) : Prop := ∀ q, dot (C q) t ≤ gamma q

theorem D20_append (a2 a3 b phi : ℝ) (t : Fin 4 → ℝ) :
    D20 a2 a3 b (append phi t) ↔
      a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧
      t 3 ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b := by
  rfl

theorem D21_append (a3 b phi : ℝ) (t : Fin 5 → ℝ) :
    D21 a3 b (append phi t) ↔
      a3 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ t 4 ∧
      t 4 ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b := by
  rfl

theorem D20_closed_dictionary (a2 a3 b phi : ℝ) (t : Fin 4 → ℝ) :
    D20 a2 a3 b (append phi t) ↔ closedMask C20 (gamma20 a2 a3 b) t ∧
      t (Fin.last 3) ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b := by
  rw [D20_append]
  generalize hv : phi - ∑ i, t i = v
  simp only [closedMask, C20, gamma20, dot, Fin.forall_fin_succ, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, Fin.forall_fin_zero,
    and_true, zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  change (a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧
    t 3 ≤ v ∧ v ≤ b) ↔
    (-t 0 ≤ -a2 ∧ t 0 ≤ a3 ∧ -t 1 ≤ -a3 ∧ t 1 + -t 2 ≤ 0 ∧
      t 2 + -t 3 ≤ 0 ∧ t 3 ≤ b) ∧ t 3 ≤ v ∧ v ≤ b
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    refine ⟨⟨?_,h1,?_,?_,?_,?_⟩,h5,h6⟩ <;> linarith
  · rintro ⟨⟨h0,h1,h2,h3,h4,_⟩,h5,h6⟩
    refine ⟨?_,h1,?_,?_,?_,h5,h6⟩ <;> linarith

theorem D21_closed_dictionary (a3 b phi : ℝ) (t : Fin 5 → ℝ) :
    D21 a3 b (append phi t) ↔ closedMask C21 (gamma21 a3 b) t ∧
      t (Fin.last 4) ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b := by
  rw [D21_append]
  generalize hv : phi - ∑ i, t i = v
  simp only [closedMask, C21, gamma21, dot, Fin.forall_fin_succ, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, Fin.forall_fin_zero,
    and_true, zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  change (a3 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ t 4 ∧
    t 4 ≤ v ∧ v ≤ b) ↔
    (-t 0 ≤ -a3 ∧ t 0 + -t 1 ≤ 0 ∧ t 1 + -t 2 ≤ 0 ∧ t 2 + -t 3 ≤ 0 ∧
      t 3 + -t 4 ≤ 0 ∧ t 4 ≤ b) ∧ t 4 ≤ v ∧ v ≤ b
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,h5,h6⟩ <;> linarith
  · rintro ⟨⟨h0,h1,h2,h3,h4,_⟩,h5,h6⟩
    refine ⟨?_,?_,?_,?_,?_,h5,h6⟩ <;> linarith

/-- Cube support is a consequence of the independent closed chain. -/
theorem D20_cube {a2 a3 b phi : ℝ} (ha : 1/10 ≤ a2) (hb : b ≤ 1/2)
    {t : Fin 4 → ℝ} (ht : D20 a2 a3 b (append phi t)) : t ∈ continuousCube 4 := by
  rcases (D20_append a2 a3 b phi t).mp ht with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  simp only [continuousCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc,
    Fin.forall_fin_succ]
  change (1/10 ≤ t 0 ∧ t 0 ≤ 1/2) ∧ (1/10 ≤ t 1 ∧ t 1 ≤ 1/2) ∧ (1/10 ≤ t 2 ∧ t 2 ≤ 1/2) ∧ (1/10 ≤ t 3 ∧ t 3 ≤ 1/2) ∧ (∀ i : Fin 0, _)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩, fun i => Fin.elim0 i⟩ <;> linarith

theorem D21_cube {a3 b phi : ℝ} (ha : 1/10 ≤ a3) (hb : b ≤ 1/2)
    {t : Fin 5 → ℝ} (ht : D21 a3 b (append phi t)) : t ∈ continuousCube 5 := by
  rcases (D21_append a3 b phi t).mp ht with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  simp only [continuousCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc,
    Fin.forall_fin_succ]
  change (1/10 ≤ t 0 ∧ t 0 ≤ 1/2) ∧ (1/10 ≤ t 1 ∧ t 1 ≤ 1/2) ∧ (1/10 ≤ t 2 ∧ t 2 ≤ 1/2) ∧ (1/10 ≤ t 3 ∧ t 3 ≤ 1/2) ∧ (1/10 ≤ t 4 ∧ t 4 ≤ 1/2) ∧ (∀ i : Fin 0, _)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩, fun i => Fin.elim0 i⟩ <;> linarith

/-- The exact reciprocal density accounts for every prefix coordinate once. -/
theorem density_reciprocal {n : ℕ} (t : Fin n → ℝ) (v : ℝ) :
    1 / ((∏ i, t i) * v) = (1/v) * continuousDensity t := by
  simp [continuousDensity, mul_comm]

/-- All six affine equalities are avoided a.e. on the cube, using real Lebesgue nullness. -/
theorem rows_ae {n r : ℕ} (C : Fin r → Fin n → ℝ) (gamma : Fin r → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → ∀ q, dot (C q) t ≠ gamma q := by
  have hh : ∀ q, ∀ᵐ t ∂volume, t ∈ continuousCube n → dot (C q) t ≠ gamma q := by
    intro q
    obtain ⟨j,hj⟩ := hC q
    have hz := continuousHyperplane_null j (C q) (gamma q) hj
    have he := (measure_eq_zero_iff_ae_notMem).mp hz
    filter_upwards [he] with t ht hcube heq
    exact ht ⟨hcube, heq⟩
  filter_upwards [ae_all_iff.mpr hh] with t ht hcube q
  exact ht q hcube

theorem lower_ae {m : ℕ} (phi : ℝ) :
    ∀ᵐ t ∂volume, t ∈ continuousCube (m+1) →
      t (Fin.last m) ≠ phi - ∑ i, t i := by
  have he := (measure_eq_zero_iff_ae_notMem).mp (continuousLowerFace_null (n := m) phi)
  filter_upwards [he] with t ht hc heq
  apply ht
  refine ⟨hc,?_⟩
  simp [continuousLowerFace, ← heq]

theorem cap_ae {n : ℕ} (j : Fin n) (phi b : ℝ) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → phi - ∑ i, t i ≠ b := by
  have he := (measure_eq_zero_iff_ae_notMem).mp (continuousCapFace_null j phi b)
  filter_upwards [he] with t ht hc heq
  apply ht
  refine ⟨hc,?_⟩
  simp [continuousCapFace, heq]

theorem closedMask_iff {n r : ℕ} (C : Fin r → Fin n → ℝ) (gamma : Fin r → ℝ)
    (flags : Fin r → Bool) (t : Fin n → ℝ) (ht : ∀ q, dot (C q) t ≠ gamma q) :
    closedMask C gamma t ↔ mask C gamma flags t := by
  unfold closedMask mask
  apply forall_congr'
  intro q
  unfold row
  cases flags q <;> simp only [Bool.false_eq_true, ↓reduceIte]
  exact ⟨fun h => lt_of_le_of_ne h (ht q), le_of_lt⟩

/-- A full-space a.e. comparison, with the cube indicator on the genuine weighted G. -/
theorem closed_section_ae {m r : ℕ} (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (flags : Fin r → Bool)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|)
    (D : (Fin (m+1) → ℝ) → Prop)
    (hD : ∀ t, D t ↔ closedMask C gamma t ∧
      t (Fin.last m) ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b)
    (hS : ∀ t, D t → t ∈ continuousCube (m+1)) :
    (fun t => if D t then 1 / ((∏ i, t i) * (phi - ∑ i, t i)) else 0) =ᵐ[volume]
      (continuousCube (m+1)).indicator (fun t => G phi b C gamma flags t * continuousDensity t) := by
  filter_upwards [rows_ae C gamma hC, lower_ae (m := m) phi,
    cap_ae (Fin.last m) phi b] with t hr hl hu
  by_cases hc : t ∈ continuousCube (m+1)
  · rw [Set.indicator_of_mem hc]
    have hd : D t ↔ mask C gamma flags t ∧
        t (Fin.last m) < phi - ∑ i, t i ∧ phi - ∑ i, t i < b := by
      rw [hD t, closedMask_iff C gamma flags t (hr hc)]
      exact and_congr_right (fun _ => and_congr
        ⟨fun h => lt_of_le_of_ne h (hl hc), le_of_lt⟩
        ⟨fun h => lt_of_le_of_ne h (hu hc), le_of_lt⟩)
    simp only [hd, G, U, F, density_reciprocal]
    split_ifs <;> simp_all
  · rw [Set.indicator_of_notMem hc, if_neg (fun h => hc (hS t h))]

/-- Genuine full-space integrability is produced from the proved a.e. equality. -/
theorem closed_section_integrable {m r : ℕ} (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (flags : Fin r → Bool)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|)
    (D : (Fin (m+1) → ℝ) → Prop)
    (hD : ∀ t, D t ↔ closedMask C gamma t ∧
      t (Fin.last m) ≤ phi - ∑ i, t i ∧ phi - ∑ i, t i ≤ b)
    (hS : ∀ t, D t → t ∈ continuousCube (m+1)) :
    Integrable (fun t => if D t then 1 / ((∏ i, t i) * (phi - ∑ i, t i)) else 0) := by
  have hi := (integrable_indicator_iff (continuousCube_measurable (m+1))).mpr
    (G_weighted_integrable phi b C gamma flags)
  exact hi.congr (closed_section_ae phi b C gamma flags hC D hD hS).symm

end Wu2008DoubleSieve.HighUnit
