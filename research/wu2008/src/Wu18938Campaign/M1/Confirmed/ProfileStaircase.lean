import Wu18938Campaign.M1.Confirmed.ProfileFunctional
import NodeStaircase

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real NodeExtension Finset
open scoped Classical

def clippedHeight (x : ℝ) : ℝ := max 0 (min (1 / 16) x)

theorem clippedHeight_bounds (x : ℝ) : 0 ≤ clippedHeight x ∧ clippedHeight x ≤ 1 / 16 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

def stepProfile (z : Fin 9 → ℝ) (j : Fin 9) (v : ℝ) : ℝ :=
  if v ≤ upperNode j then clippedHeight (z j) else 0

def staircase (z : Fin 9 → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun v => max (staircase z n v)
      (if h : n < 9 then stepProfile z ⟨n,h⟩ v else 0)

theorem stepProfile_bounds (z : Fin 9 → ℝ) (j : Fin 9) (v : ℝ) :
    0 ≤ stepProfile z j v ∧ stepProfile z j v ≤ 1 / 16 := by
  unfold stepProfile
  split_ifs
  · exact clippedHeight_bounds _
  · norm_num

theorem stepProfile_antitone (z : Fin 9 → ℝ) (j : Fin 9) : Antitone (stepProfile z j) := by
  intro a b hab
  unfold stepProfile
  split_ifs with hb ha
  · rfl
  · exact False.elim (ha (hab.trans hb))
  · exact (clippedHeight_bounds _).1
  · rfl

theorem staircase_bounds (z : Fin 9 → ℝ) (n : ℕ) (v : ℝ) :
    0 ≤ staircase z n v ∧ staircase z n v ≤ 1 / 16 := by
  induction n with
  | zero => norm_num [staircase]
  | succ n ih =>
    rw [staircase]
    split_ifs
    · exact ⟨ih.1.trans (le_max_left _ _),max_le ih.2 (stepProfile_bounds _ _ _).2⟩
    · exact ⟨ih.1.trans (le_max_left _ _),max_le ih.2 (by norm_num)⟩

theorem staircase_antitone (z : Fin 9 → ℝ) (n : ℕ) : Antitone (staircase z n) := by
  induction n with
  | zero => exact fun _ _ _ => le_rfl
  | succ n ih =>
    intro a b hab
    simp only [staircase]
    split_ifs
    · exact max_le_max (ih hab) (stepProfile_antitone z _ hab)
    · exact max_le_max (ih hab) le_rfl

theorem max_upper_nodes {δ : ℝ} {H J : ℝ → ℝ}
    (hH : UpperNodes δ (fun v => 1 - H v) 3)
    (hJ : UpperNodes δ (fun v => 1 - J v) 3) :
    UpperNodes δ (fun v => 1 - max (H v) (J v)) 3 := by
  intro m η ε hη he
  obtain ⟨T0,hT04,h0⟩ := hH m η ε hη he
  obtain ⟨T1,_,h1⟩ := hJ m η ε hη he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb v hv hv3
  dsimp only
  rcases le_total (H v) (J v) with hh | hh
  · rw [max_eq_right hh]; exact h1 N (by omega) heven i Δ V hb v hv hv3
  · rw [max_eq_left hh]; exact h0 N (by omega) heven i Δ V hb v hv hv3

theorem zero_upper_nodes {δ : ℝ} (hδ : 0 < δ) : UpperNodes δ (fun _ => 1 - (0 : ℝ)) 3 := by
  intro m η ε hη he
  simpa only [sub_zero] using roughBox_upper_leaf m hη hδ he

theorem staircase_actual (z : Fin 9 → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ j : Fin 9, ∀ (m : ℕ) (η ε : ℝ), 0 < η → 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
        wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
          (1 - z j + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V))
    (n : ℕ) : UpperNodes δ (fun v => 1 - staircase z n v) 3 := by
  have hstep (j : Fin 9) : UpperNodes δ (fun v => 1 - stepProfile z j v) 3 := by
    intro m η ε hη he
    obtain ⟨T0,hT04,h0⟩ := hz j m η ε hη he
    obtain ⟨T1,_,h1⟩ := roughBox_upper_leaf m hη hδ he
    refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
    intro N hN heven i Δ V hb v hv hv3
    dsimp only
    by_cases hvj : v ≤ upperNode j
    · rw [stepProfile,if_pos hvj]
      by_cases hz0 : 0 ≤ min (1 / 16 : ℝ) (z j)
      · rw [clippedHeight,max_eq_right hz0]
        have hm := phi_mono hb (by omega) hη hδ (by linarith) hvj
        have hu := h0 N (by omega) heven i Δ V hb
        have hp := mul_le_mul_of_nonneg_right
          (show 1 - z j + ε ≤ 1 - min (1 / 16 : ℝ) (z j) + ε by linarith [min_le_right (1 / 16 : ℝ) (z j)])
          (theta_nonneg hb (by omega) hη hδ)
        exact hm.trans (hu.trans hp)
      · rw [clippedHeight,max_eq_left (le_of_not_ge hz0),sub_zero]
        exact h1 N (by omega) heven i Δ V hb v hv hv3
    · rw [stepProfile,if_neg hvj,sub_zero]
      exact h1 N (by omega) heven i Δ V hb v hv hv3
  induction n with
  | zero => exact zero_upper_nodes hδ
  | succ n ih =>
    by_cases hn : n < 9
    · simpa only [staircase,dif_pos hn] using max_upper_nodes ih (hstep ⟨n,hn⟩)
    · simpa only [staircase,dif_neg hn] using max_upper_nodes ih (zero_upper_nodes hδ)

end Wu18938Campaign.M1.Confirmed.FiniteProfile
