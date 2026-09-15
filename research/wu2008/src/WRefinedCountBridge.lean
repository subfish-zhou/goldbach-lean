import WRefinedLossRecovered
import W02AcceptedGain
import Wu04BypassTargetBudget

noncomputable section
namespace WuTarget.RefinedExit
open Wu2008DoubleSieve Real
open MathlibNt.Wu2008DoubleSieve
open MathlibNt.SieveTheory.SwitchingPrinciple

abbrev ordinary (N : ℕ) : Finset ℕ := wuPrimeComplements N

def margin : ℝ := 4491/5000-8*log (5000/4469)

theorem margin_pos : 0 < margin :=
  sub_pos.mpr Wu04BypassBudget.target_lt_safe

/-- Recovered unconditional loss, including the exact unit correction in Wu's carrier. -/
theorem actual_refinement_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((ordinary N).card : ℝ) -
        (8*log (5000/4469)+ε)*U8CanonicalMother.M N ≤
          ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) := by
  obtain ⟨T,hT⟩ := Wu2004MeanValue.refinedGood_card_lower_add_unit
    (9469/5000) ε (by norm_num) (by norm_num) hε
  refine ⟨max 512 T,le_max_left _ _,?_⟩
  intro N hN heven
  have h := hT N ((le_max_right _ _).trans hN) heven
  have hN0 : 0 < N := by omega
  have hu : ((ordinary N).card : ℝ) = (chenGoodRepresentations N).card +
      (if (N-1).Prime then (1 : ℝ) else 0) := by
    rw [wuPrimeComplements_card_eq_release]
    split_ifs <;> push_cast <;> ring
  rw [hu, U8CanonicalMother.scale_eq_liu hN0]
  norm_num only [show (1 : ℝ)/(9469/5000-1)=5000/4469 by norm_num] at h
  convert h using 1
  ring

/-- Only the actual ordinary-count coefficient remains as a quantitative input. -/
theorem from_actual_count {c : ℝ} (hc : (4491/5000 : ℝ) ≤ c)
    (hcount : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (c-ε)*U8CanonicalMother.M N ≤ ((ordinary N).card : ℝ)) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  have hε : 0 < margin/4 := div_pos margin_pos (by norm_num)
  obtain ⟨Tc,hTc,hcN⟩ := hcount (margin/4) hε
  obtain ⟨Tl,_,hlN⟩ := actual_refinement_loss hε
  refine ⟨max Tc Tl,hTc.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN512 : 512 ≤ N := hTc.trans ((le_max_left _ _).trans hN)
  have hM := HighSixPhase6.original_scale_positive hN512
  change 0 < U8CanonicalMother.M N at hM
  have hcountN := hcN N ((le_max_left _ _).trans hN) he
  have hlossN := hlN N ((le_max_right _ _).trans hN) he
  have hscaled := mul_le_mul_of_nonneg_right hc hM.le
  have hgood : margin/2*U8CanonicalMother.M N ≤
      ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) := by
    unfold margin at *
    nlinarith only [hcountN,hlossN,hscaled]
  refine ⟨hgood,?_⟩
  have hp : 0 < ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) :=
    (mul_pos (half_pos margin_pos) hM).trans_le hgood
  have hn : 0 < (Wu2004MeanValue.refinedGood N (9469/5000)).card := by exact_mod_cast hp
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hn
  obtain ⟨hpp,r,q,hq,hr,hs,heq⟩ := Wu2004MeanValue.mem_refinedGood.mp hp
  refine ⟨p,r,q,hpp,hr,hq,hs,?_⟩
  convert heq using 1
  norm_num

/-- The current node-based finite certificate, not the old limiting table. -/
theorem finite_node_target
    (hc : (4491/5000 : ℝ) ≤ W02Accepted.paidCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply from_actual_count hc
  intro ε hε
  obtain ⟨δ,_,_,_,T,hT,h⟩ := W02Accepted.enhanced_P2_paid hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T,hT,h⟩

end WuTarget.RefinedExit
