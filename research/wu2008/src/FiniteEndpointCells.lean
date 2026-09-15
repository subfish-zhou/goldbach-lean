import FirstFeedbackTerminalLower
import CoupledEndpointLog

namespace FiniteEndpointPayment
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

/-- Clipping uses only the original two endpoints and the original nine nodes. -/
def clip (a b x : ℝ) : ℝ := min b (max a x)
def left (a b : ℝ) (k : Fin 9) : ℝ := clip a b (upperLeft k)
def right (a b : ℝ) (k : Fin 9) : ℝ := clip a b (upperNode k)

theorem clip_bounds {a b x : ℝ} (hab : a ≤ b) :
    a ≤ clip a b x ∧ clip a b x ≤ b :=
  ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩

theorem clip_mono (a b : ℝ) : Monotone (clip a b) := by
  intro x y h
  exact min_le_min_left b (max_le_max_left a h)

theorem node_order (k : Fin 9) : upperLeft k ≤ upperNode k := by
  unfold upperLeft upperNode
  split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) k.val]

theorem cell_order (a b : ℝ) (k : Fin 9) : left a b k ≤ right a b k :=
  clip_mono a b (node_order k)

theorem cell_value (z : Fin 9 → ℝ) (a b : ℝ) (k : Fin 9) {t : ℝ}
    (ht : t ∈ Ioo (left a b k) (right a b k)) : nineProfile z t = z k := by
  apply nineProfile_cell z
  change upperLeft k < t ∧ t ≤ upperNode k
  have hb : t < b := ht.2.trans_le (min_le_left _ _)
  have hl : max a (upperLeft k) < t := by
    have h := ht.1
    change min b (max a (upperLeft k)) < t at h
    exact (min_lt_iff.mp h).resolve_left (not_lt.mpr hb.le)
  have ha : a < t := (le_max_left _ _).trans_lt hl
  have hu : t < max a (upperNode k) := ht.2.trans_le (min_le_right _ _)
  exact ⟨(le_max_right _ _).trans_lt hl,
    ((lt_max_iff.mp hu).resolve_left (not_lt.mpr ha.le)).le⟩

theorem integral_cell (z : Fin 9 → ℝ) (w : ℝ → ℝ) (a b : ℝ) (k : Fin 9) :
    (∫ t in left a b k..right a b k, nineProfile z t*w t) =
      z k*(∫ t in left a b k..right a b k,w t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le (cell_order a b k)] at ht
  dsimp only
  rw [cell_value z a b k ht]

/-- Exact finite expansion for every subinterval of the genuine profile support. -/
theorem integral_cells (z : Fin 9 → ℝ) {w : ℝ → ℝ} {a b : ℝ}
    (ha : 1≤a) (hab : a≤b) (hb : b≤3)
    (hi : IntervalIntegrable (fun t => nineProfile z t*w t) volume a b) :
    (∫ t in a..b,nineProfile z t*w t) =
      ∑ k : Fin 9,z k*(∫ t in left a b k..right a b k,w t) := by
  let x : ℕ → ℝ := fun n => clip a b (if n=0 then 1 else (21+(n:ℝ))/10)
  have hx (k : Fin 9) : x k.val=left a b k ∧ x (k.val+1)=right a b k := by
    constructor
    · simp only [x,left,upperLeft]
    · simp only [x,right,upperNode,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
        ↓reduceIte,Nat.cast_add,Nat.cast_one]
      congr 2
      ring
  have hic (k : ℕ) (hk : k<9) :
      IntervalIntegrable (fun t => nineProfile z t*w t) volume (x k) (x (k+1)) := by
    rw [(hx ⟨k,hk⟩).1,(hx ⟨k,hk⟩).2]
    apply hi.mono_set
    rw [uIcc_of_le (cell_order a b ⟨k,hk⟩),uIcc_of_le hab]
    exact Icc_subset_Icc (clip_bounds hab).1 (clip_bounds hab).2
  have ht := intervalIntegral.sum_integral_adjacent_intervals hic
  have h0 : x 0=a := by simp [x,clip,max_eq_left ha,min_eq_right hab]
  have h9 : x 9=b := by
    change clip a b ((21+(9:ℝ))/10)=b
    norm_num only at *
    exact min_eq_left (le_max_of_le_right hb)
  rw [h0,h9] at ht
  rw [← ht,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hx k).1,(hx k).2]
  exact integral_cell z w a b k

end
end FiniteEndpointPayment
