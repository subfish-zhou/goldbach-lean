import MathlibNt.Wu2008DoubleSieve.HighSixPsiCoefficient
import MathlibNt.Wu2008DoubleSieve.HighSixThetaIntegral

namespace Wu2008DoubleSieve.HighSix
open Real

/-- The original j6 finite count has the literal fixed-delta integral upper
bound. The internal B6 error is multiplied by the absolute coefficient;
no sign assumption on Psi or its complement is present. -/
theorem C6_psi_integral_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      C6 N ≤ (4*(1-firstFunctionalGainPsi δ s S)*
        (∫ t in left..right, 1/(t*(1/2-δ-t))))*truncatedSixthMassScale N+
          ε*truncatedSixthMassScale N := by
  let c := 1-firstFunctionalGainPsi δ s S
  let η := ε/(2*(|c|+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T1,hT14,hT1⟩ := C6_psi_B6_upper hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := B6_integral_error hδ hδhi hη
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hc := hT1 N (by omega) he
  have hb := hT2 N (by omega) he
  have hs : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    have := (wuSingularSeries_pos N (show 0 < N by omega)).le
    positivity
  have hpay : |c| *η ≤ ε/2 := by
    have heq : 2*(|c|+1)*η = ε := by dsimp [η]; field_simp
    nlinarith only [heq,hη.le]
  have hdiff : c*(B6 N δ-4*primeIntegral δ*truncatedSixthMassScale N) ≤
      (ε/2)*truncatedSixthMassScale N := by
    calc
      _ ≤ |c*(B6 N δ-4*primeIntegral δ*truncatedSixthMassScale N)| := le_abs_self _
      _ = |c| *|B6 N δ-4*primeIntegral δ*truncatedSixthMassScale N| := abs_mul _ _
      _ ≤ |c| *(η*truncatedSixthMassScale N) := mul_le_mul_of_nonneg_left hb (abs_nonneg c)
      _ = (|c| *η)*truncatedSixthMassScale N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpay hs
  change C6 N ≤ c*B6 N δ+(ε/2)*truncatedSixthMassScale N at hc
  change C6 N ≤ (4*c*primeIntegral δ)*truncatedSixthMassScale N+ε*truncatedSixthMassScale N
  nlinarith only [hc,hdiff]

/-- The same actual count upper bound in paper-source notation, retaining
rather than discarding the fixed-delta penalty. -/
theorem C6_source_integral_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      C6 N ≤ (4*(1-firstFunctionalGainPsiOne s S+
        (2*δ/(1-2*δ))*omega3XIntegralEnvelope s S)*
        (∫ t in left..right, 1/(t*(1/2-δ-t))))*truncatedSixthMassScale N+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT4,hT⟩ := C6_psi_integral_upper hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he
  have h := hT N hN he
  rw [psi_source_penalty hδhi] at h
  convert h using 1
  ring
end Wu2008DoubleSieve.HighSix
