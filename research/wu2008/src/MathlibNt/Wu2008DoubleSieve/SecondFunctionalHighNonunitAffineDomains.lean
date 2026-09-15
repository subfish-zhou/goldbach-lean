import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitLegalMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalReciprocalGridBoundary

namespace Wu2008DoubleSieve.HighNonunitLegal
open Set MeasureTheory
open scoped BigOperators Classical

/-- Adjacent order rows and four signed endpoint rows in dimension n+2. -/
abbrev AffineRow (n : ℕ) := Fin (n + 1) ⊕ (Bool ⊕ Bool)

noncomputable def affineC (n : ℕ) : AffineRow n → Fin (n + 2) → ℝ
  | .inl k => fun i => gridFaceCoeff k.castSucc i - gridFaceCoeff k.succ i
  | .inr (.inl false) => fun i => -gridFaceCoeff 0 i
  | .inr (.inl true) => gridFaceCoeff 0
  | .inr (.inr false) => fun i => -gridFaceCoeff 1 i
  | .inr (.inr true) => gridFaceCoeff (Fin.last (n + 1))

def affineGamma (n : ℕ) (lower firstUpper secondLower upper : ℝ) : AffineRow n → ℝ
  | .inl _ => 0
  | .inr (.inl false) => -lower
  | .inr (.inl true) => firstUpper
  | .inr (.inr false) => -secondLower
  | .inr (.inr true) => upper

theorem affineC_adjacent (n : ℕ) (k : Fin (n + 1)) (t : Fin (n + 2) → ℝ) :
    (∑ i, affineC n (.inl k) i * t i) = t k.castSucc - t k.succ := by
  simp only [affineC, sub_mul, Finset.sum_sub_distrib, gridFaceCoeff_sum]

theorem affineC_nonzero (n : ℕ) (q : AffineRow n) :
    ∃ i, 1 ≤ |affineC n q i| := by
  cases q with
  | inl k =>
    refine ⟨k.castSucc, ?_⟩
    have h : k.castSucc ≠ k.succ := by
      intro he
      have hv := congrArg Fin.val he
      exact Nat.ne_add_one k.val hv
    simp [affineC, gridFaceCoeff, h]
  | inr q =>
    cases q with
    | inl b => cases b <;> exact ⟨0, by simp [affineC, gridFaceCoeff]⟩
    | inr b =>
      cases b
      · exact ⟨1, by simp [affineC, gridFaceCoeff]⟩
      · exact ⟨Fin.last (n + 1), by simp [affineC, gridFaceCoeff]⟩

theorem affine_iff (n : ℕ) (lower firstUpper secondLower upper : ℝ)
    (t : Fin (n + 2) → ℝ) :
    (∀ q, (∑ i, affineC n q i * t i) ≤ affineGamma n lower firstUpper secondLower upper q) ↔
      lower ≤ t 0 ∧ t 0 ≤ firstUpper ∧ secondLower ≤ t 1 ∧
        Monotone t ∧ t (Fin.last (n + 1)) ≤ upper := by
  have he : (∀ q : Bool ⊕ Bool, (∑ i, affineC n (.inr q) i * t i) ≤
      affineGamma n lower firstUpper secondLower upper (.inr q)) ↔
      (lower ≤ t 0 ∧ t 0 ≤ firstUpper) ∧
        (secondLower ≤ t 1 ∧ t (Fin.last (n + 1)) ≤ upper) := by
    simp [Sum.forall, Bool.forall_bool, affineC, affineGamma,
      Finset.sum_neg_distrib, gridFaceCoeff_sum]
  rw [Sum.forall, he]
  simp only [affineGamma, affineC_adjacent, sub_nonpos, ← Fin.monotone_iff_le_succ]
  tauto

/-- Fixed five-dimensional matrix; all moving data occurs in gamma20. -/
noncomputable abbrev C20 := affineC 3
noncomputable abbrev C21 := affineC 4
abbrev gamma20 (a2 a3 b : ℝ) := affineGamma 3 a2 a3 a3 b
abbrev gamma21 (a3 b : ℝ) := affineGamma 4 a3 b a3 b

theorem C20_nonzero (q : AffineRow 3) : ∃ i, 1 ≤ |C20 q i| := affineC_nonzero 3 q
theorem C21_nonzero (q : AffineRow 4) : ∃ i, 1 ≤ |C21 q i| := affineC_nonzero 4 q

theorem D20_eq_closed_affine (a2 a3 b phi : ℝ) :
    D20 a2 a3 b phi = {t | ∀ q, (∑ i, C20 q i * t i) ≤ gamma20 a2 a3 b q} ∩
      legal 3 phi := by
  ext t
  simp only [D20, mem_inter_iff, mem_ofPred_eq, C20, gamma20, affine_iff]
  rfl

/-- Both extra endpoint conditions follow from the original monotonicity and bounds. -/
theorem D21_redundant_endpoints (a3 b : ℝ) (t : Fin 6 → ℝ) :
    (a3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ b) ↔
      a3 ≤ t 0 ∧ t 0 ≤ b ∧ a3 ≤ t 1 ∧ Monotone t ∧ t 5 ≤ b := by
  constructor
  · rintro ⟨hl, hm, hu⟩
    exact ⟨hl, (hm (Fin.zero_le 5)).trans hu,
      hl.trans (hm (Fin.zero_le 1)), hm, hu⟩
  · rintro ⟨hl, _, _, hm, hu⟩
    exact ⟨hl, hm, hu⟩

theorem D21_eq_closed_affine (a3 b phi : ℝ) :
    D21 a3 b phi = {t | ∀ q, (∑ i, C21 q i * t i) ≤ gamma21 a3 b q} ∩
      legal 4 phi := by
  ext t
  simp only [D21, mem_inter_iff, mem_ofPred_eq, C21, gamma21, affine_iff]
  exact and_congr (D21_redundant_endpoints a3 b t) Iff.rfl

theorem closed_affine_measurable {n : ℕ} {Q : Type*} [Countable Q]
    (C : Q → Fin n → ℝ) (gamma : Q → ℝ) :
    MeasurableSet {t : Fin n → ℝ | ∀ q, (∑ i, C q i * t i) ≤ gamma q} := by
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply measurableSet_le _ measurable_const
  fun_prop

end Wu2008DoubleSieve.HighNonunitLegal
