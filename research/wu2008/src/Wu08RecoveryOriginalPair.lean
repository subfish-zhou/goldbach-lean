import Wu08RecoveryCappedNormalization

noncomputable section
open Real MeasureTheory
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.SmallBoundaryRecovery

/-- The original small/large first-prime coefficient, with the original
36/5/(1-x) weight and the original large-domain multiplier eight. -/
def originalIntegral (e : Bool) : ℝ := SmallQuadrature.I e+8*Large.I e

theorem originalIntegral_literal (e : Bool) :
    originalIntegral e =
      (∫ x in FourRoughClosedMass.alpha..(1/10 : ℝ),
        (36/5)/(1-x)*(if e then FourRoughClosedMass.regularOuter11 x else FourRoughClosedMass.regularOuter10 x))+
      8*(∫ x in (1/10 : ℝ)..FourRoughClosedMass.beta,
        if e then FourRoughClosedMass.regularOuter11 x else FourRoughClosedMass.regularOuter10 x) := by
  rw [originalIntegral,SmallQuadrature.integral_literal,Large.integral_literal]

/-- Xi is fixed first. Thereafter EVERY preassigned positive delta upper bound
admits one common actual choice, before A and N. The old raw remainder is retained
exactly once; the two original properMain terms are each replaced exactly once. -/
theorem original_pair_integral_parameters {σ ξmax : ℝ} (hσ : 0 < σ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧
      ∀ dmax : ℝ, 0 < dmax →
      ∃ δ η ρ ε : ℝ, 0 < δ ∧ δ < dmax ∧ δ < 1/4 ∧
        0 < η ∧ η < 1/8 ∧ 1 < ρ ∧ ρ ≤ 5/4 ∧
        0 < ε ∧ ε < truncatedSixthLowerAlpha ∧ ε < δ ∧
      ∀ A : ℕ, ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
        (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
          (originalIntegral false+originalIntegral true+σ)*(wuSingularSeries N*N/log N^2)+
          (N : ℝ)/log (N : ℝ)^A := by
  have hσ4 : 0 < σ/4 := by positivity
  obtain ⟨ξ,hξ,hξu,hlarge⟩ := Large.original_pair_large_prefix_paid hσ4 hmax
  refine ⟨ξ,hξ,hξu,?_⟩
  intro dmax hdmax
  obtain ⟨δ,η,ρ,hδ,hδm,hδu,hη,hηu,hρ,hρu,Ts,hTs,hs⟩ := properMain_integral_below hσ4 hdmax
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  obtain ⟨ε,hε,hεu⟩ := exists_between (lt_min ha hδ)
  have hεa := hεu.trans_le (min_le_left _ _)
  have hεδ := hεu.trans_le (min_le_right _ _)
  refine ⟨δ,η,ρ,ε,hδ,hδm,hδu,hη,hηu,hρ,hρu,hε,hεa,hεδ,?_⟩
  intro A
  obtain ⟨Tl,hl⟩ := hlarge A ρ ε δ η (σ/4) hρ hρu hε hεa hεδ
    (by linarith) hη hηu hσ4
  refine ⟨max Ts Tl,hTs.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hNs := (le_max_left _ _).trans hN
  have hp0 := hs N hNs he false ξ hξ
  have hp1 := hs N hNs he true ξ hξ
  have hraw := hl N ((le_max_right _ _).trans hN) he
  unfold originalIntegral
  ring_nf at hp0 hp1 hraw ⊢
  linarith only [hp0,hp1,hraw]

/-- Actual Q10+Q11, not a replacement finite mass or a conditional integral
hypothesis. Raw exceptional term and original singular-series normalization stay
visible. This is an upper producer, not a proof of the final 0.899/1.8938 claim. -/
theorem original_pair_integral_upper {σ : ℝ} (hσ : 0 < σ) (A : ℕ) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (originalIntegral false+originalIntegral true+σ)*(wuSingularSeries N*N/log N^2)+
        (N : ℝ)/log (N : ℝ)^A := by
  obtain ⟨_,_,_,h⟩ := original_pair_integral_parameters hσ (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hp⟩ := h (1/4) (by norm_num)
  exact hp A

#check originalIntegral
#print axioms originalIntegral
#check originalIntegral_literal
#print axioms originalIntegral_literal
#check original_pair_integral_parameters
#print axioms original_pair_integral_parameters
#check original_pair_integral_upper
#print axioms original_pair_integral_upper
end Wu08FirstPrimeFour.SmallBoundaryRecovery
