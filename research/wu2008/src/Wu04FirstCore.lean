import Wu04RemainingStrongFourRows

namespace Wu04FirstCore
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Real Set MeasureTheory
noncomputable section

/-- The literal loaded first functional, with its unchanged unbounded-phi cost. -/
theorem psi_identity (s S : ℝ) : firstFunctionalGainPsiOne s S =
    fourthRowClassicalJ s S / 2 - fourthRowClassicalL S - omega3XIntegralEnvelope s S := by
  unfold firstFunctionalGainPsiOne fourthRowClassicalJ fourthRowClassicalL
  ring

/-- Original Table 1 targets, not numerical assumptions or a replacement feedback vector. -/
def publication : Fin 5 → ℝ := ![9405211/1000000000,6558950/1000000000,
  3536751/1000000000,1056651/1000000000,0]

theorem terminal_kernel (φ : ℝ) : omega3XIntegral (firstNode 4) (firstS 4) φ=0 := by
  rw [show firstS (4:Fin 5)=3 from rfl,show firstNode (4:Fin 5)=3 by norm_num [firstNode]]
  exact omega3XIntegral_self _ _

theorem terminal_cost : omega3XIntegralEnvelope (firstNode 4) (firstS 4)=0 := by
  rw [show firstS (4:Fin 5)=3 from rfl,show firstNode (4:Fin 5)=3 by norm_num [firstNode]]
  exact omega3XIntegralEnvelope_self _

theorem terminal_psi : firstFunctionalGainPsiOne (firstNode 4) (firstS 4)=publication 4 := by
  rw [psi_identity,terminal_cost,show firstS (4:Fin 5)=3 from rfl,
    show firstNode (4:Fin 5)=3 by norm_num [firstNode],show publication (4:Fin 5)=0 from rfl]
  norm_num [fourthRowClassicalJ,fourthRowClassicalL]

/-- Equal endpoints remove only cost and classical integrals, never the actual feedback. -/
theorem terminal_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    publication 4+firstFeedback (actualNine δ) (firstNode 4) (firstS 4) ≤
      wuImprovementLimit true δ (firstNode 4) := by
  have g := first_geometry 4
  have h := first_actual hd hh g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2
  rwa [terminal_cost,terminal_psi,mul_zero,sub_zero] at h

/-- Original Psi1 gates established directly; no Psi2 row geometry is imported. -/
theorem cost_geometry (i : Fin 5) :
    1/10≤1/firstS i ∧ 1/firstS i≤1/firstNode i ∧
      (3+1/Wu04MainTail.cap)*(1/firstNode i)≤2 := by
  revert i
  simp only [firstNode,firstS,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [Wu04MainTail.cap]

/-- A fully paid whole-domain preliminary cap for every original first row. -/
theorem whole_cost (i : Fin 5) : omega3XIntegralEnvelope (firstNode i) (firstS i)≤
    Wu04MainTail.cap*SecondFunctionalGeometricMass.Elementary.elementaryMomentOne
      1 (1/firstS i) (1/firstNode i) := by
  have g := cost_geometry i
  apply csSup_le
  · exact ⟨omega3XIntegral (firstNode i) (firstS i) 2,mem_image_of_mem _ (show (2:ℝ)∈Ici 2 by simp)⟩
  · rintro y ⟨φ,hφ,rfl⟩
    exact Wu04RemainingGamma.integral_paid g.1 g.2.1 g.2.2 hφ
end
end Wu04FirstCore
