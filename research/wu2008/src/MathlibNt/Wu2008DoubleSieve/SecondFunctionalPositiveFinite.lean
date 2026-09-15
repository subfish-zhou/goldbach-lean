import MathlibNt.Wu2008DoubleSieve.SecondFunctionalStrictMargins

/-!
# Strict positive improvement in the original finite Wu source boxes

The depth and the sieve parameter are fixed before the threshold is chosen.
Only the original four parameters share a threshold; no compact-uniform
threshold over the whole real interval is asserted.
-/

namespace Wu2008DoubleSieve.SecondFunctionalPositiveFinite

open SecondFunctionalParameters SecondFunctionalPositive

/-- The original limiting upper improvement has the full strict margin on
`[1, 5/2]`, by the accepted fourth-row bound and the original antitonicity. -/
theorem H_strict {s : ℝ} (hs : 1 ≤ s) (hsHi : s ≤ 5/2) :
    (1/300 : ℝ) < wuImprovementLimit true (1/1000) s := by
  have hmono := wuImprovementLimit_upper_antitone_initial
    (δ := (1/1000 : ℝ)) (by norm_num) (by norm_num)
    (show s ∈ Set.Icc 1 3 from ⟨hs, by linarith only [hsHi]⟩)
    (show row4.s ∈ Set.Icc 1 3 by norm_num [row4])
    (show s ≤ row4.s by norm_num only [row4]; linarith only [hsHi])
  exact SecondFunctionalStrictMargins.row4_H_positive.trans_le hmono

/-- The actual original row parameters lie in the proved interval. -/
theorem parameters_bounds (iRow : Fin 4) :
    1 ≤ (parameters iRow).s ∧ (parameters iRow).s ≤ 5/2 := by
  revert iRow
  simp only [Fin.forall_fin_succ]
  exact ⟨by change 1 ≤ row1.s ∧ row1.s ≤ 5/2; norm_num [row1],
    by change 1 ≤ row2.s ∧ row2.s ≤ 5/2; norm_num [row2],
    by change 1 ≤ row3.s ∧ row3.s ≤ 5/2; norm_num [row3],
    by change 1 ≤ row4.s ∧ row4.s ≤ 5/2; norm_num [row4],
    fun i => Fin.elim0 i⟩

/-- All four original H values inherit the fourth-row margin; this makes
no claim about positivity of the first or second signed core. -/
theorem H_rows_strict (iRow : Fin 4) :
    (1/300 : ℝ) < wuImprovementLimit true (1/1000) (parameters iRow).s :=
  H_strict (parameters_bounds iRow).1 (parameters_bounds iRow).2

/-- Consume exactly the strict gap `H - 1/300`; no factor of two is lost. -/
theorem improvement_mem_succ (k : ℕ) {s : ℝ} (hs : 1 ≤ s) (hsHi : s ≤ 5/2) :
    (1/300 : ℝ) ∈ wuEventualImprovements true (k+1) (1/1000) s := by
  have hgap : 0 < wuImprovementLimit true (1/1000) s - 1/300 :=
    sub_pos.mpr (H_strict hs hsHi)
  have hm := wuImprovementLimit_sub_mem true k
    (δ := (1/1000 : ℝ)) (s := s)
    (ε := wuImprovementLimit true (1/1000) s - 1/300)
    (by norm_num) (by norm_num) hs (by linarith only [hsHi]) hgap
  simpa only [sub_sub_cancel] using hm

/-- The same membership at any fixed legal original depth. -/
theorem improvement_mem (k : ℕ) (hk : 1 ≤ k) {s : ℝ}
    (hs : 1 ≤ s) (hsHi : s ≤ 5/2) :
    (1/300 : ℝ) ∈ wuEventualImprovements true k (1/1000) s := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact improvement_mem_succ l hs hsHi

/-- Literal finite counting estimate: the original source, original windows,
original Phi and original Theta, with the full coefficient `A(s) - 1/300`.
The source-box indices and windows are quantified after the threshold. -/
theorem finite_source (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (hs : 1 ≤ s) (hsHi : s ≤ 5/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k (1/1000) N i Δ V →
        wuBoxPhi N (1/1000) (convolutionWuWindows N Δ V) s ≤
          (wuUpperCoefficient s - 1/300) *
            boxTheta N ((N : ℝ) ^ (1/2 - (1/1000 : ℝ)))
              (convolutionWuWindows N Δ V) := by
  obtain ⟨M, hM⟩ := improvement_mem k hk hs hsHi
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN he i Δ V hbox
  exact hM N ((le_max_right _ _).trans hN)
    ((le_max_left _ _).trans hN) he i Δ V hbox

/-- The original four rows share a finite maximum of their fixed-depth
thresholds. This is not uniformity over all real sieve parameters. -/
theorem four_rows_common_threshold (k : ℕ) (hk : 1 ≤ k) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (iRow : Fin 4) (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k (1/1000) N i Δ V →
        wuBoxPhi N (1/1000) (convolutionWuWindows N Δ V) (parameters iRow).s ≤
          (wuUpperCoefficient (parameters iRow).s - 1/300) *
            boxTheta N ((N : ℝ) ^ (1/2 - (1/1000 : ℝ)))
              (convolutionWuWindows N Δ V) := by
  classical
  have hrows := fun iRow : Fin 4 =>
    finite_source k hk (parameters iRow).s
      (parameters_bounds iRow).1 (parameters_bounds iRow).2
  choose rowT hrow4 hrow using hrows
  refine ⟨max 4 (Finset.univ.sup rowT), le_max_left _ _, ?_⟩
  intro N hN he iRow i Δ V hbox
  have hrowN : rowT iRow ≤ N :=
    (Finset.le_sup (Finset.mem_univ iRow)).trans ((le_max_right _ _).trans hN)
  exact hrow iRow N hrowN he i Δ V hbox

end Wu2008DoubleSieve.SecondFunctionalPositiveFinite
