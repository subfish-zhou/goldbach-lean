import ShrinkGeometry

open Set QuarterTrim

namespace StaircaseShrink

/-- The original argument stays inside the actual table's right boundary. -/
theorem original_u_upper {t x y : ℝ} (h : (x,y) ∈ domain t) : u x y ≤ 41 / 10 := by
  apply (div_le_iff₀ alpha_pos).2
  have hx := h.1.1
  have hy := h.2.1
  norm_num [alpha, beta] at hx hy ⊢
  linarith

theorem table_right_endpoints : ∀ r ∈ Wu08Staircase.table,
    r.2.1 ∈ Icc (2 : ℝ) (41 / 10) := by
  intro r hr
  simp only [Wu08Staircase.table, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r; norm_num [mem_Icc]

/-- A finite right-node lower certificate transfers along the correct decreasing direction.
The hypothesis concerns h, not global monotonicity of the zero-extended staircase. -/
theorem eval_le_of_nodes (L : List (ℝ × ℝ × ℝ)) (h : ℝ → ℝ)
    (hm : AntitoneOn h (Icc 2 (41 / 10)))
    (hn : ∀ r ∈ L, r.2.1 ∈ Icc 2 (41 / 10) ∧ r.2.2 ≤ h r.2.1)
    {s v : ℝ} (hs : s ∈ Icc 2 (41 / 10)) (hsv : s ≤ v) (hs0 : 0 ≤ h s) :
    Wu08Staircase.eval L v ≤ h s := by
  induction L with
  | nil => exact hs0
  | cons r L ih =>
    rcases r with ⟨a,b,c⟩
    dsimp only [Wu08Staircase.eval]
    split
    · rename_i hv
      obtain ⟨hb,hc⟩ := hn _ (List.mem_cons_self ..)
      exact hc.trans (hm hs hb (hsv.trans hv.2))
    · exact ih (fun r hr => hn r (List.mem_cons_of_mem _ hr))

/-- Conditional only on the stated h-node facts and legal h monotonicity.
This does not certify the actual sieve h or its printed node values. -/
theorem profile_le_shifted_h (h : ℝ → ℝ)
    (hm : AntitoneOn h (Icc 2 (41 / 10)))
    (hnonneg : ∀ s ∈ Icc 2 (41 / 10), 0 ≤ h s)
    (hnodes : ∀ r ∈ Wu08Staircase.table, r.2.2 ≤ h r.2.1)
    {t delta x y : ℝ} (ht : 0 < t) (hd : 0 < delta) (hdt : delta ≤ t / 2)
    (hP : (x,y) ∈ domain t) : Wu08Staircase.profile (u x y) ≤ h (shiftedU delta x y) := by
  have hb := source_budgets ht hd hdt hP
  have hsu := hb.2.2.2.2.2.2.2
  have hs : shiftedU delta x y ∈ Icc 2 (41 / 10) :=
    ⟨hb.2.2.2.2.2.2.1, hsu.trans (original_u_upper hP)⟩
  exact eval_le_of_nodes Wu08Staircase.table h hm
    (fun r hr => ⟨table_right_endpoints r hr, hnodes r hr⟩) hs hsu (hnonneg _ hs)

end StaircaseShrink
