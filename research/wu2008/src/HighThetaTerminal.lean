import HighThetaLowerSource

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- A single actual box carries all paid terminals, with one C and threshold.
No claim of a positive h gain or arbitrary-depth feedback is included. -/
def ActualTerminal {i : ℕ} (N : ℕ) (δ ε ρ C s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  RelativeRemainders N δ ε s t W ∧ MainMassPaid N δ ε s t W ∧
    PhiEndpointPaid N δ ε s W ∧ PhiEndpointPaid N δ ε t W ∧
    SwitchedUpperPaid N δ ε ρ s t W ∧
    LowerSourcePaid N δ ε C s W ∧ LowerSourcePaid N δ ε C t W

/-- Joint actual original/insertion terminal. Both epsilon and rho, then C
and T, are chosen before N, every moving box, s/t and the inserted prime. -/
theorem original_and_inserted_terminal {δ ε ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        ActualTerminal N δ ε ρ C s t (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          ActualTerminal N δ ε ρ C s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨T1,hT14,hR⟩ := original_and_inserted_relative hδ hδhi hε
  obtain ⟨T2,_,hM⟩ := original_and_inserted_main_mass hδ hδhi hε
  obtain ⟨T3,_,hP⟩ := original_and_inserted_phi_endpoint hδ hδhi hε
  obtain ⟨T4,_,hS⟩ := original_and_inserted_switched_upper hδ hδhi hε hρ
  obtain ⟨C,hC,T5,_,hL⟩ := original_and_inserted_lower_source hδ hδhi hε
  refine ⟨C,hC,max T1 (max T2 (max T3 (max T4 T5))),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_left T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4 := (le_max_left T4 T5).trans ((le_max_right T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN)))
  have hN5 := (le_max_right T4 T5).trans ((le_max_right T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN)))
  have r := hR N hN1 Δ hlo hhi V hV hrect s t hs hst ht
  have m := hM N hN2 Δ hlo hhi V hV hrect s t hs hst ht
  have ps := hP N hN3 he Δ hlo hhi V hV hrect s (by linarith) (hst.trans ht)
  have pt := hP N hN3 he Δ hlo hhi V hV hrect t (by linarith) ht
  have u := hS N hN4 he Δ hlo hhi V hV hrect s t hs hst ht
  have ls := hL N hN5 he Δ hlo hhi V hV hrect s (by linarith) (hst.trans ht)
  have lt := hL N hN5 he Δ hlo hhi V hV hrect t (by linarith) ht
  exact ⟨⟨r.1,m.1,ps.1,pt.1,u.1,ls.1,lt.1⟩,
    fun U hw => ⟨r.2 U hw,m.2 U hw,ps.2 U hw,pt.2 U hw,u.2 U hw,ls.2 U hw,lt.2 U hw⟩⟩

end
end HighTheta
