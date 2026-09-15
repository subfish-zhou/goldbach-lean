import QuarterTrimGeometry

open Set MeasureTheory

namespace Wu08Staircase

/-- Literal Table 2 data, restricted to indices 1 through 21.
The columns are the open left endpoint, closed right endpoint, and printed rational.
No assertion about the actual sieve function h is made. -/
noncomputable def table : List (ℝ × ℝ × ℝ) := [
  (20 / 10, 21 / 10, 211041 / 10000000),
  (21 / 10, 22 / 10, 191556 / 10000000),
  (22 / 10, 23 / 10, 173631 / 10000000),
  (23 / 10, 24 / 10, 157035 / 10000000),
  (24 / 10, 25 / 10, 141585 / 10000000),
  (25 / 10, 26 / 10, 127132 / 10000000),
  (26 / 10, 27 / 10, 113556 / 10000000),
  (27 / 10, 28 / 10, 100756 / 10000000),
  (28 / 10, 29 / 10, 88648 / 10000000),
  (29 / 10, 30 / 10, 77162 / 10000000),
  (30 / 10, 31 / 10, 66236 / 10000000),
  (31 / 10, 32 / 10, 55818 / 10000000),
  (32 / 10, 33 / 10, 46164 / 10000000),
  (33 / 10, 34 / 10, 37529 / 10000000),
  (34 / 10, 35 / 10, 30123 / 10000000),
  (35 / 10, 36 / 10, 23901 / 10000000),
  (36 / 10, 37 / 10, 18997 / 10000000),
  (37 / 10, 38 / 10, 15336 / 10000000),
  (38 / 10, 39 / 10, 12593 / 10000000),
  (39 / 10, 40 / 10, 10120 / 10000000),
  (40 / 10, 41 / 10, 8099 / 10000000)]

/-- A cell has the literal half-open convention (a,b]. -/
noncomputable def eval : List (ℝ × ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a,b,c) :: rest, t => if a < t ∧ t ≤ b then c else eval rest t

noncomputable def profile : ℝ → ℝ := eval table

theorem eval_bounds (L : List (ℝ × ℝ × ℝ))
    (hL : ∀ r ∈ L, 0 ≤ r.2.2 ∧ r.2.2 ≤ QuarterTrim.q) (t : ℝ) :
    0 ≤ eval L t ∧ eval L t ≤ QuarterTrim.q := by
  induction L with
  | nil => simpa [eval] using le_of_lt QuarterTrim.q_pos
  | cons r L ih =>
    rcases r with ⟨a, b, c⟩
    simp only [eval]
    split
    · exact hL _ (List.mem_cons_self ..)
    · exact ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))

theorem table_bounds : ∀ r ∈ table, 0 ≤ r.2.2 ∧ r.2.2 ≤ QuarterTrim.q := by
  intro r hr
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r; norm_num [QuarterTrim.q]

theorem profile_bounds (t : ℝ) : 0 ≤ profile t ∧ profile t ≤ QuarterTrim.q :=
  eval_bounds table table_bounds t

theorem measurable_eval (L : List (ℝ × ℝ × ℝ)) : Measurable (eval L) := by
  induction L with
  | nil => exact measurable_const
  | cons r L ih =>
    rcases r with ⟨a, b, c⟩
    exact Measurable.ite measurableSet_Ioc measurable_const ih

theorem measurable_profile : Measurable profile := measurable_eval table

theorem triangle_profile_bounds (x y : ℝ) (_h : QuarterTrim.triangle x y) :
    0 ≤ profile (QuarterTrim.u x y) ∧ profile (QuarterTrim.u x y) ≤ QuarterTrim.q :=
  profile_bounds _

theorem eval_skip (a b c t : ℝ) (L : List (ℝ × ℝ × ℝ))
    (h : ¬ (a < t ∧ t ≤ b)) : eval ((a,b,c) :: L) t = eval L t := if_neg h

theorem eval_hit (a b c t : ℝ) (L : List (ℝ × ℝ × ℝ))
    (h : a < t ∧ t ≤ b) : eval ((a,b,c) :: L) t = c := if_pos h

/-- Every listed cell really has its stated value, including its right endpoint. -/
theorem profile_on_cell (r : ℝ × ℝ × ℝ) (hr : r ∈ table) (t : ℝ)
    (ht : r.1 < t ∧ t ≤ r.2.1) : profile t = r.2.2 := by
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r; dsimp only at ht ⊢; unfold profile table
  · exact eval_hit _ _ _ _ _ ht
  · iterate 1 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 2 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 3 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 4 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 5 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 6 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 7 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 8 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 9 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 10 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 11 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 12 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 13 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 14 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 15 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 16 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 17 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 18 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 19 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht
  · iterate 20 rw [eval_skip _ _ _ _ _ (by rintro ⟨h₁, h₂⟩; linarith)]
    exact eval_hit _ _ _ _ _ ht

theorem eval_zero (L : List (ℝ × ℝ × ℝ)) (t : ℝ)
    (hL : ∀ r ∈ L, ¬ (r.1 < t ∧ t ≤ r.2.1)) : eval L t = 0 := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    rcases r with ⟨a,b,c⟩
    rw [eval_skip _ _ _ _ _ (hL _ (List.mem_cons_self ..))]
    exact ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))

/-- The convention is zero at 2, below 2, and beyond the last cell at 4.1. -/
theorem profile_zero_outside (t : ℝ) (ht : t ≤ 2 ∨ 41 / 10 < t) : profile t = 0 := by
  apply eval_zero
  intro r hr
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r; rintro ⟨h₁,h₂⟩; rcases ht with ht | ht <;> dsimp only at h₁ h₂ <;> linarith

end Wu08Staircase
