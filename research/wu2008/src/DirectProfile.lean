import FiniteNodeCertificate

open Set MeasureTheory QuarterTrim Wu2008DoubleSieve
open scoped Classical BigOperators

namespace DirectFiniteF6
noncomputable section

def row (w : Fin 21 → ℝ) (j : Fin 21) : ℝ × ℝ × ℝ :=
  ((ActualNineFeedback.originalRow j).1, (ActualNineFeedback.originalRow j).2.1, w j)

def rows (w : Fin 21 → ℝ) : List (ℝ × ℝ × ℝ) := (List.finRange 21).map (row w)

def profile (w : Fin 21 → ℝ) : ℝ → ℝ := Wu08Staircase.eval (rows w)

theorem eval_map_sub_mul (L : List (Fin 21)) (w d : Fin 21 → ℝ) (a s : ℝ) :
    Wu08Staircase.eval (L.map (row (fun j => w j - a * d j))) s =
      Wu08Staircase.eval (L.map (row w)) s - a * Wu08Staircase.eval (L.map (row d)) s := by
  induction L with
  | nil => simp [Wu08Staircase.eval]
  | cons j L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval]
    split_ifs <;> first | rfl | exact ih

theorem profile_sub_mul (w d : Fin 21 → ℝ) (a s : ℝ) :
    profile (fun j => w j - a * d j) s = profile w s - a * profile d s :=
  eval_map_sub_mul _ w d a s

theorem eval_map_mono (L : List (Fin 21)) {w z : Fin 21 → ℝ}
    (h : ∀ j, w j ≤ z j) (s : ℝ) :
    Wu08Staircase.eval (L.map (row w)) s ≤ Wu08Staircase.eval (L.map (row z)) s := by
  induction L with
  | nil => exact le_rfl
  | cons j L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval]
    split_ifs <;> first | exact h j | exact ih

theorem profile_mono {w z : Fin 21 → ℝ} (h : ∀ j, w j ≤ z j) (s : ℝ) :
    profile w s ≤ profile z s := eval_map_mono _ h s

theorem eval_map_bounds (L : List (Fin 21)) {w : Fin 21 → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ j, |w j| ≤ K) (s : ℝ) :
    |Wu08Staircase.eval (L.map (row w)) s| ≤ K := by
  induction L with
  | nil => simpa only [List.map_nil, Wu08Staircase.eval, abs_zero] using hK
  | cons j L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval]
    split_ifs <;> first | exact h j | exact ih

def mass (w : Fin 21 → ℝ) : ℝ := ∑ j, |w j|

theorem mass_nonneg (w : Fin 21 → ℝ) : 0 ≤ mass w :=
  Finset.sum_nonneg (fun j _ => abs_nonneg (w j))

theorem profile_abs (w : Fin 21 → ℝ) (s : ℝ) : |profile w s| ≤ mass w :=
  eval_map_bounds _ (mass_nonneg w)
    (fun j => Finset.single_le_sum (fun k _ => abs_nonneg (w k)) (Finset.mem_univ j)) s

theorem profile_zero (s : ℝ) : profile (fun _ => 0) s = 0 := by
  have h := profile_abs (fun _ => 0) s
  have hz : |profile (fun _ => 0) s| = 0 := le_antisymm
    (by simpa only [mass, abs_zero, Finset.sum_const_zero] using h) (abs_nonneg _)
  exact abs_eq_zero.mp hz

theorem profile_nonneg {w : Fin 21 → ℝ} (h : ∀ j, 0 ≤ w j) (s : ℝ) :
    0 ≤ profile w s := by
  simpa only [profile_zero] using profile_mono h s

theorem measurable_profile (w : Fin 21 → ℝ) : Measurable (profile w) :=
  Wu08Staircase.measurable_eval _

theorem row_endpoint (w : Fin 21 → ℝ) {r : ℝ × ℝ × ℝ} (hr : r ∈ rows w) :
    r.2.1 ∈ Icc (2 : ℝ) (41 / 10) := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact StaircaseShrink.table_right_endpoints (ActualNineFeedback.originalRow j)
    (List.get_mem Wu08Staircase.table _)

def clipped (n : ℕ) (δ : ℝ) (j : Fin 21) : ℝ :=
  max 0 (ActualNineFeedback.transferredLower n j -
    ActualNineFeedback.deltaLoss δ * ActualNineFeedback.transferredDebit n j)

theorem clipped_nonneg (n : ℕ) (δ : ℝ) (j : Fin 21) : 0 ≤ clipped n δ j :=
  le_max_left _ _

theorem clipped_nodes {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (n : ℕ)
    {r : ℝ × ℝ × ℝ} (hr : r ∈ rows (clipped n δ)) :
    r.2.2 ≤ wuImprovementLimit false δ r.2.1 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have he := row_endpoint (clipped n δ) (List.mem_map.mpr ⟨j, hj, rfl⟩)
  change (ActualNineFeedback.originalRow j).2.1 ∈ Icc 2 (41/10) at he
  rw [ActualNineFeedback.originalRow_node] at he
  change _ ≤ wuImprovementLimit false δ (ActualNineFeedback.originalRow j).2.1
  rw [ActualNineFeedback.originalRow_node]
  apply max_le
  · exact wuImprovementLimit_nonneg false hd (by linarith) (by linarith [he.1]) (by linarith [he.2])
  · exact ActualNineFeedback.finite_actual_twentyone hd hh n j

theorem clipped_profile_lower {δ t x y : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 1000)
    (hd : 0 < δ) (hdt : δ ≤ t / 2) (n : ℕ)
    (hv : (x,y) ∈ StaircaseShrink.domain t) :
    profile (clipped n δ) (u x y) ≤
      wuImprovementLimit false δ (truncatedSixthLowerS δ x y) := by
  have hm : AntitoneOn (wuImprovementLimit false δ) (Icc 2 (41/10)) := by
    apply (wuImprovementLimit_lower_antitone hd (by linarith)).mono
    intro s hs
    exact ⟨hs.1, by linarith [hs.2]⟩
  have hb := StaircaseShrink.source_budgets ht hd hdt hv
  have hsu := hb.2.2.2.2.2.2.2
  have hs : StaircaseShrink.shiftedU δ x y ∈ Icc 2 (41 / 10) :=
    ⟨hb.2.2.2.2.2.2.1, hsu.trans (StaircaseShrink.original_u_upper hv)⟩
  change profile (clipped n δ) (u x y) ≤
    wuImprovementLimit false δ (StaircaseShrink.shiftedU δ x y)
  exact StaircaseShrink.eval_le_of_nodes (rows (clipped n δ)) _ hm
    (fun r hr => ⟨row_endpoint _ hr, clipped_nodes hd (by linarith) n hr⟩) hs hsu
    (wuImprovementLimit_nonneg false hd (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2]))

theorem clipped_dominates (n : ℕ) (δ s : ℝ) :
    profile (ActualNineFeedback.transferredLower n) s -
      ActualNineFeedback.deltaLoss δ * profile (ActualNineFeedback.transferredDebit n) s ≤
        profile (clipped n δ) s := by
  rw [← profile_sub_mul]
  exact profile_mono (fun j => le_max_right _ _) s

end
end DirectFiniteF6
