import SrcSixthGainWeights
import Wu08G6HighActual
import W15Budget

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve NodeExtension
open scoped Classical BigOperators

theorem first_rectangle_ceiling :
    (1/4 : ℝ) < 1/2-2*beta ∧ 2*beta+(1/2-2*beta) = 1/2 := by
  norm_num [beta]

theorem second_rectangle_ceiling :
    (1/4 : ℝ) < 1/2-3*alpha ∧ 2*(3*alpha/2)+(1/2-3*alpha) = 1/2 := by
  norm_num [alpha]

theorem no_prop43_ceiling_on_first :
    ¬ ∃ phi4 : ℝ, 1/2-2*beta ≤ phi4 ∧ phi4 < 1/4 := by
  rintro ⟨phi4,hlo,hhi⟩
  linarith only [first_rectangle_ceiling.1,hlo,hhi]

theorem no_prop43_ceiling_on_second :
    ¬ ∃ phi4 : ℝ, 1/2-3*alpha ≤ phi4 ∧ phi4 < 1/4 := by
  rintro ⟨phi4,hlo,hhi⟩
  linarith only [second_rectangle_ceiling.1,hlo,hhi]

theorem full_weights_same_profile_debit (w : Fin 21 → ℝ) :
    8*(∑ j : Fin 21, g6Weight j*w j)-highLoss w = Gamma w 0 := by
  rw [← published_twentyone,published_eq_legal_add_high]
  ring

theorem full_weights_capped (w : Fin 21 → ℝ) :
    8*(∑ j : Fin 21, g6Weight j*w j)-(16129:ℝ)/40000*heightCap w ≤ Gamma w 0 := by
  rw [← published_twentyone]
  exact legal_lower w

theorem high_loss_support {x y : ℝ} (h : (x,y) ∈ highDomain) :
    2 ≤ u x y ∧ u x y < 927/400 := by
  refine ⟨(HighConsumer.original_high_parameters h).1,?_⟩
  obtain ⟨hx,hy⟩ := (high_iff x y).mp h
  have ha := hx.1
  have hb := hy.1
  norm_num [u,alpha] at ha ⊢
  linarith

theorem high_basis_zero (j : Fin 21) (hj : 4 ≤ j.val) :
    highLoss (WuTarget.W03.basis j) = 0 := by
  unfold highLoss
  have he : masked highDomain (WuTarget.W03.basis j) = 0 := by
    funext v
    by_cases hv : v ∈ highDomain
    · rw [masked,if_pos hv]
      change profile (WuTarget.W03.basis j) (u v.1 v.2)/_ = 0
      rw [WuTarget.W03.profile_basis]
      have hn : ¬ WuTarget.W03.cell j (u v.1 v.2) := by
        intro hc
        have hm := rNode_mono hj
        have hs := (high_loss_support hv).2
        norm_num [rNode] at hm
        linarith [hc.1]
      rw [if_neg hn,zero_div]
    · simp [masked,hv]
  rw [he]
  simp

theorem unaffected_weight (j : Fin 21) (hj : 4 ≤ j.val) :
    8*g6Weight j = WuTarget.W03.weight j := by
  have h := published_eq_legal_add_high (WuTarget.W03.basis j)
  rw [published_basis,high_basis_zero j hj,add_zero] at h
  exact h

theorem source_high_multiple_annihilation {i k N d p : ℕ} {delta Delta : ℝ}
    {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hd : 0 ≤ delta) (hb : wuSourceBox k delta N i Delta V)
    (hp : p.Prime) (hpd : p ∣ d) (hhigh : (N : ℝ)^(1/4 : ℝ) < p) :
    convolutionCoeff (convolutionWuWindows N Delta V) d = 0 :=
  Wu08G6HighActual.quarter_high_coefficient_zero hN hd hb hp hpd hhigh

#print axioms no_prop43_ceiling_on_first
#print axioms no_prop43_ceiling_on_second
#print axioms full_weights_same_profile_debit
#print axioms unaffected_weight
#print axioms source_high_multiple_annihilation
#print Wu2008DoubleSieve.wuImprovementLimit_lower_antitone
#check Wu2008DoubleSieve.wuImprovementLimit_nonneg
#print prefix Wu2008DoubleSieve.wuImprovementLimit
end WuSource.SrcSixthGain
