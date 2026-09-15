import MathlibNt.Wu2008DoubleSieve.HighSixOmega1Upper
import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Endpoint
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource

namespace Wu2008DoubleSieve.HighSix
open Real

/-- The original coefficient is the literal fixed-delta gain complement. -/
theorem psi_coefficient (δ : ℝ) :
    wuUpperCoefficient S-J/2+omega3XIntegralEnvelope s S/(1-2*δ) =
      1-firstFunctionalGainPsi δ s S := by
  have hA : wuUpperCoefficient s = 1 := by
    unfold wuUpperCoefficient
    rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three
      (show s ≤ 3 by norm_num [s])]
    have hs : s ≠ 0 := by norm_num [s]
    field_simp [hs, (exp_pos eulerMascheroniConstant).ne']
  unfold firstFunctionalGainPsi
  rw [hA]
  change _ = 1-(1-wuUpperCoefficient S+(1/2)*J-omega3XIntegralEnvelope s S/(1-2*δ))
  ring

/-- The fixed-delta penalty is retained exactly. -/
theorem psi_source_penalty {δ : ℝ} (hδhi : δ ≤ 1/100) :
    firstFunctionalGainPsi δ s S = firstFunctionalGainPsiOne s S -
      (2*δ/(1-2*δ))*omega3XIntegralEnvelope s S :=
  firstFunctionalGainPsi_eq_source_sub_penalty (by linarith)
    (by norm_num [s]) (by norm_num [s]) (by norm_num [S]) (by norm_num [S])

/-- All original Omega producers are consumed with their actual carriers.
No sign of Psi or its complement is assumed. -/
theorem C6_psi_B6_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      C6 N ≤ (1-firstFunctionalGainPsi δ s S)*B6 N δ+
        ε*truncatedSixthMassScale N := by
  obtain ⟨T₁,hT₁,h₁⟩ := count_omega1_integral_paid hδ hδhi hε
  obtain ⟨T₂,_,h₂⟩ := Omega3Upper.O3_integral_paid hδ hδhi hε
  refine ⟨max T₁ T₂,hT₁.trans (le_max_left _ _),?_⟩
  intro N hN he
  have ha := h₁ N ((le_max_left _ _).trans hN) he
  have hb := h₂ N ((le_max_right _ _).trans hN) he
  rw [← psi_coefficient]
  ring_nf at ha hb ⊢
  linarith only [ha,hb]
end Wu2008DoubleSieve.HighSix
