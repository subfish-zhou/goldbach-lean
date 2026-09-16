import Wu18938Campaign.M1.Confirmed.ProfileStaircase
import FeedbackSystem

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real NodeExtension ActualNineFeedback
open scoped Classical

def rowGain (δ : ℝ) (H : ℝ → ℝ) (j : Fin 9) : ℝ :=
  if h : j.val < 4 then secondGain (coupledRow ⟨j.val,h⟩) δ H
  else firstGain δ (firstNode ⟨j.val - 4,by omega⟩) (firstS ⟨j.val - 4,by omega⟩) H

theorem row_gain_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hHnode : UpperNodes δ (fun v => 1 - H v) 3)
    (j : Fin 9) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - rowGain δ H j + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  unfold rowGain
  split_ifs with hj
  · have hh := second_gain_actual (coupledRow ⟨j.val,hj⟩)
      (coupledRow_geometry ⟨j.val,hj⟩).1 hH hb hδ hδhi hHnode m hη he
    simpa only [coupledRow_node] using hh
  · let k : Fin 5 := ⟨j.val - 4,by omega⟩
    have hg := first_geometry k
    have heq : firstNode k = upperNode j := by
      dsimp [firstNode,upperNode,k]
      rw [Nat.cast_sub (by omega : 4 ≤ j.val)]
      norm_num
      ring
    have hh := first_gain_actual hH hb hδ hδhi hg.1 (hg.2.1.trans hg.2.2.1)
      hg.2.2.1 hg.2.2.2.1 hHnode m hη he
    change ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - firstGain δ (firstNode k) (firstS k) H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    rw [heq]
    rw [heq] at hh
    exact hh

def originalProfile (δ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun v =>
      max (originalProfile δ n v) (staircase (rowGain δ (originalProfile δ n)) 9 v)

theorem originalProfile_bounds (δ : ℝ) (n : ℕ) (v : ℝ) :
    0 ≤ originalProfile δ n v ∧ originalProfile δ n v ≤ 1 / 16 := by
  induction n with
  | zero => norm_num [originalProfile]
  | succ n ih =>
    exact ⟨ih.1.trans (le_max_left _ _),max_le ih.2 (staircase_bounds _ _ _).2⟩

theorem originalProfile_antitone (δ : ℝ) (n : ℕ) : Antitone (originalProfile δ n) := by
  induction n with
  | zero => exact fun _ _ _ => le_rfl
  | succ n ih =>
    intro a b hab
    exact max_le_max (ih hab) (staircase_antitone _ _ hab)

theorem originalProfile_step (δ : ℝ) (n : ℕ) (v : ℝ) :
    originalProfile δ n v ≤ originalProfile δ (n + 1) v := le_max_left _ _

theorem originalProfile_actual {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (n : ℕ) :
    UpperNodes δ (fun v => 1 - originalProfile δ n v) 3 := by
  induction n with
  | zero => exact zero_upper_nodes hδ
  | succ n ih =>
    have hrows := fun j m η ε hη he =>
      row_gain_actual (originalProfile_antitone δ n)
        (fun v _ => originalProfile_bounds δ n v) hδ hδhi ih j m (η := η) (ε := ε) hη he
    exact max_upper_nodes ih (staircase_actual _ hδ hrows 9)

theorem originalProfile_extensions {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (n : ℕ) :
    LowerNodes δ (lowerExtension (originalProfile δ n) (aProfile (originalProfile δ n))) ∧
      UpperNodes δ (upperExtension (originalProfile δ n) (aProfile (originalProfile δ n))) 5 :=
  full_extensions_actual (originalProfile_antitone δ n)
    (fun v _ => originalProfile_bounds δ n v) hδ (originalProfile_actual hδ hδhi n)

theorem originalProfile_rows {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (j : Fin 9) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - rowGain δ (originalProfile δ n) j + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
  row_gain_actual (originalProfile_antitone δ n) (fun v _ => originalProfile_bounds δ n v)
    hδ hδhi (originalProfile_actual hδ hδhi n) j m hη he

end Wu18938Campaign.M1.Confirmed.FiniteProfile
