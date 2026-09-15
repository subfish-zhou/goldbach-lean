import MathlibNt.Wu2004MeanValue.CutoffSeparation
import Mathlib.Tactic

/-! Exact dyadic geometry for the small-product decomposition in manuscript
lines 315–334. The last retained interval has index equal to the first scale
strictly below the square root. -/

namespace Wu2004MeanValue

noncomputable section

def dyadicScale (η x : ℝ) (j : ℕ) : ℝ := η * x / 2 ^ (j + 1)

theorem dyadicScale_pos {η x : ℝ} (hη : 0 < η) (hx : 0 < x) (j : ℕ) :
    0 < dyadicScale η x j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_zero (η x : ℝ) : dyadicScale η x 0 = η * x / 2 := by
  simp [dyadicScale]

theorem dyadicScale_succ (η x : ℝ) (j : ℕ) :
    2 * dyadicScale η x (j + 1) = dyadicScale η x j := by
  simp only [dyadicScale, pow_succ]
  ring

theorem dyadicScale_antitone {η x : ℝ} (hη : 0 < η) (hx : 0 < x) :
    Antitone (dyadicScale η x) := by
  apply antitone_nat_of_succ_le
  intro j
  have hp := dyadicScale_pos hη hx (j + 1)
  have hs := dyadicScale_succ η x j
  linarith

theorem exists_dyadicScale_lt_sqrt {η x : ℝ} (_hη : 0 < η) (hx : 0 < x) :
    ∃ j : ℕ, dyadicScale η x j < Real.sqrt x := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨j, hj⟩ := (ht.eventually
    (Filter.eventually_gt_atTop (η * x / Real.sqrt x))).exists
  refine ⟨j, ?_⟩
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hmul := (div_lt_iff₀ hs).mp hj
  unfold dyadicScale
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ (j + 1))).mpr
  rw [pow_succ]
  nlinarith [mul_pos hp hs]

/-- The first index strictly below `sqrt x`, made total for all real parameters. -/
def dyadicLast (η x : ℝ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, dyadicScale η x j < Real.sqrt x then Nat.find h else 0

theorem dyadicLast_spec {η x : ℝ} (hη : 0 < η) (hx : 0 < x) :
    dyadicScale η x (dyadicLast η x) < Real.sqrt x ∧
      ∀ j < dyadicLast η x, Real.sqrt x ≤ dyadicScale η x j := by
  have hex := exists_dyadicScale_lt_sqrt hη hx
  rw [dyadicLast, dif_pos hex]
  exact ⟨Nat.find_spec hex, fun j hj => le_of_not_gt (Nat.find_min hex hj)⟩

theorem dyadicLast_pos {η x : ℝ} (hη : 0 < η) (hx : 0 < x)
    (hfirst : Real.sqrt x ≤ dyadicScale η x 0) : 0 < dyadicLast η x := by
  have hs := (dyadicLast_spec hη hx).1
  by_contra h
  have hz : dyadicLast η x = 0 := by omega
  rw [hz] at hs
  exact (not_lt_of_ge hfirst) hs

theorem dyadicLast_scale_lower {η x : ℝ} (hη : 0 < η) (hx : 0 < x)
    (hfirst : Real.sqrt x ≤ dyadicScale η x 0) :
    Real.sqrt x / 2 ≤ dyadicScale η x (dyadicLast η x) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (dyadicLast_pos hη hx hfirst))
  have hp := (dyadicLast_spec hη hx).2 k (by omega)
  have hs := dyadicScale_succ η x k
  rw [hk]
  linarith

theorem dyadicScale_retained_lower {η x : ℝ} (hη : 0 < η) (hx : 0 < x)
    (hfirst : Real.sqrt x ≤ dyadicScale η x 0) {j : ℕ}
    (hj : j ≤ dyadicLast η x) :
    Real.sqrt x / 2 ≤ dyadicScale η x j :=
  (dyadicLast_scale_lower hη hx hfirst).trans (dyadicScale_antitone hη hx hj)

/-- Exact interval membership, valid for any finite terminal index. -/
theorem dyadic_cover_iff {η x t : ℝ} (hη : 0 < η) (hx : 0 < x) (J : ℕ) :
    (0 < t ∧ t ≤ η * x) ↔
      (0 < t ∧ t ≤ dyadicScale η x J) ∨
        ∃ j ≤ J, dyadicScale η x j < t ∧ t ≤ 2 * dyadicScale η x j := by
  induction J with
  | zero =>
      rw [dyadicScale_zero]
      constructor
      · intro ht
        by_cases h : t ≤ η * x / 2
        · exact Or.inl ⟨ht.1, h⟩
        · refine Or.inr ⟨0, le_rfl, ?_, ?_⟩
          · simpa [dyadicScale_zero] using lt_of_not_ge h
          · rw [dyadicScale_zero]
            linarith [ht.2]
      · rintro (ht | ⟨j, hj, ht⟩)
        · have hp := mul_pos hη hx
          exact ⟨ht.1, by linarith⟩
        · have hj0 : j = 0 := by omega
          subst j
          rw [dyadicScale_zero] at ht
          constructor <;> nlinarith [mul_pos hη hx]
  | succ J ih =>
      rw [ih]
      have hs := dyadicScale_succ η x J
      have hp := dyadicScale_pos hη hx (J + 1)
      constructor
      · rintro (ht | ⟨j, hj, ht⟩)
        · by_cases h : t ≤ dyadicScale η x (J + 1)
          · exact Or.inl ⟨ht.1, h⟩
          · exact Or.inr ⟨J + 1, le_rfl, lt_of_not_ge h, by linarith⟩
        · exact Or.inr ⟨j, by omega, ht⟩
      · rintro (ht | ⟨j, hj, ht⟩)
        · exact Or.inl ⟨ht.1, by linarith⟩
        · by_cases h : j ≤ J
          · exact Or.inr ⟨j, h, ht⟩
          · have he : j = J + 1 := by omega
            subst j
            exact Or.inl ⟨lt_trans hp ht.1, by linarith⟩

theorem dyadic_blocks_disjoint {η x : ℝ} (hη : 0 < η) (hx : 0 < x)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Set.Ioc (dyadicScale η x i) (2 * dyadicScale η x i))
      (Set.Ioc (dyadicScale η x j) (2 * dyadicScale η x j)) := by
  suffices h : ∀ i j : ℕ, i < j →
      Disjoint (Set.Ioc (dyadicScale η x i) (2 * dyadicScale η x i))
        (Set.Ioc (dyadicScale η x j) (2 * dyadicScale η x j)) by
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact h i j hij
    · exact (h j i hij).symm
  intro i j hij
  have ha := dyadicScale_antitone hη hx (show i + 1 ≤ j by omega)
  have hs := dyadicScale_succ η x i
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases hi with ⟨hi, _⟩
  rcases hj with ⟨_, hj⟩
  linarith

theorem dyadic_low_block_disjoint {η x : ℝ} (hη : 0 < η) (hx : 0 < x)
    {j J : ℕ} (hj : j ≤ J) :
    Disjoint (Set.Ioc 0 (dyadicScale η x J))
      (Set.Ioc (dyadicScale η x j) (2 * dyadicScale η x j)) := by
  have ha := dyadicScale_antitone hη hx hj
  apply Set.disjoint_left.mpr
  intro t ht hu
  rcases ht with ⟨_, ht⟩
  rcases hu with ⟨hu, _⟩
  linarith

theorem sum_dyadicScale (η x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicScale η x j) =
      η * x - dyadicScale η x J := by
  induction J with
  | zero => simp [dyadicScale_zero]; ring
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hs := dyadicScale_succ η x J
      linarith

theorem sum_dyadicScale_le {η x : ℝ} (hη : 0 < η) (hx : 0 < x) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicScale η x j) ≤ η * x := by
  rw [sum_dyadicScale]
  linarith [dyadicScale_pos hη hx J]

end
end Wu2004MeanValue
