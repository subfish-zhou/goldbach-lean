import Wu18938Campaign.M1.Confirmed.FullSecondFunctional
import Wu18938Campaign.M1.Confirmed.ProfileFullLower

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullProfile

open Wu2008DoubleSieve Real NodeExtension ActualNineFeedback FiniteProfile
open scoped Classical

def rowGain (δ : ℝ) (H : ℝ → ℝ) (j : Fin 9) : ℝ :=
  if h : j.val < 4 then secondGain (coupledRow ⟨j.val,h⟩) δ H
  else FiniteProfile.firstGain δ (firstNode ⟨j.val - 4,by omega⟩)
    (firstS ⟨j.val - 4,by omega⟩) H

theorem row_gain_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hn : UpperNodes δ (fun v => 1 - H v) 3)
    (j : Fin 9) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - rowGain δ H j + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  unfold rowGain
  split_ifs with hj
  · have hh := second_gain_actual ⟨j.val,hj⟩ hH hb hδ hδhi hn m hη he
    simpa only [coupledRow_node] using hh
  · let k : Fin 5 := ⟨j.val - 4,by omega⟩
    have hg := first_geometry k
    have heq : firstNode k = upperNode j := by
      dsimp [firstNode,upperNode,k]
      rw [Nat.cast_sub (by omega : 4 ≤ j.val)]
      norm_num
      ring
    have hh := FiniteProfile.first_gain_actual hH hb hδ hδhi hg.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.1 hg.2.2.2.1 hn m hη he
    change ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - FiniteProfile.firstGain δ (firstNode k) (firstS k) H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    rw [heq]
    rw [heq] at hh
    exact hh

def untruncatedProfile (δ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun v =>
      max (untruncatedProfile δ n v) (staircase (rowGain δ (untruncatedProfile δ n)) 9 v)

theorem profile_bounds (δ : ℝ) (n : ℕ) (v : ℝ) :
    0 ≤ untruncatedProfile δ n v ∧ untruncatedProfile δ n v ≤ 1 / 16 := by
  induction n with
  | zero => norm_num [untruncatedProfile]
  | succ n ih =>
    exact ⟨ih.1.trans (le_max_left _ _),max_le ih.2 (staircase_bounds _ _ _).2⟩

theorem profile_antitone (δ : ℝ) (n : ℕ) : Antitone (untruncatedProfile δ n) := by
  induction n with
  | zero => exact fun _ _ _ => le_rfl
  | succ n ih =>
    intro a b hab
    exact max_le_max (ih hab) (staircase_antitone _ _ hab)

theorem profile_actual {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (n : ℕ) :
    UpperNodes δ (fun v => 1 - untruncatedProfile δ n v) 3 := by
  induction n with
  | zero => exact zero_upper_nodes hδ
  | succ n ih =>
    have hrows := fun j m η ε hη he =>
      row_gain_actual (profile_antitone δ n)
        (fun v _ => profile_bounds δ n v) hδ hδhi ih j m (η := η) (ε := ε) hη he
    exact max_upper_nodes ih (staircase_actual _ hδ hrows 9)

theorem profile_twentyone {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (n : ℕ)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Fin 21,
      (wuLowerCoefficient (2 + ((j.val : ℝ) + 1) / 10) +
        fullLowerGain (untruncatedProfile δ n) (2 + ((j.val : ℝ) + 1) / 10) - ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) (2 + ((j.val : ℝ) + 1) / 10) := by
  obtain ⟨T,hT4,hT⟩ := fullLower_actual (profile_antitone δ n)
    (fun v _ => profile_bounds δ n v) hδ (profile_actual hδ hδhi n) m hη he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb j
  have hj : (j.val : ℝ) < 21 := by exact_mod_cast j.isLt
  exact hT N hN heven i Δ V hb _
    (by linarith [Nat.cast_nonneg (α := ℝ) j.val]) (by linarith)

end Wu18938Campaign.M1.Confirmed.FullProfile
