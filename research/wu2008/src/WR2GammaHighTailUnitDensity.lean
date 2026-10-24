import WR2GammaHighTailUnitR1
import WR2GammaHighTailUnitR2
import WR2GammaHighTailUnitSmall
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve Real Finset
open scoped Classical

theorem family_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T, ∀ (N : ℕ) (hN : T ≤ N), Even N → ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ),
      let L := sourceFamily row (by omega : 2 ≤ N) hd hh P j b
      L.primeMass ≤ L.mass*((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := source_R1_paid hd hh he3
  obtain ⟨T2,_,h2⟩ := R2_paid hd hh he3
  obtain ⟨T3,_,h3⟩ := small_paid hd hh he3
  obtain ⟨T4,_,h4⟩ := omega3_source_rosser_density hd (by linarith : δ < 1/2) hr
  refine ⟨max T1 (max T2 (max T3 T4)),by omega,?_⟩
  intro N hN hn row n hdim P j b
  let L := sourceFamily row (by omega : 2 ≤ N) hd hh P j b
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  have hf := L.prime_upper_finite hn _ _ hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have ha := h1 N (by omega) row n hdim P j b (sqrt ((N:ℝ)^(1/2-δ)))
  have hb := h2 N (by omega) row n hdim P j b
  have hc := h3 N (by omega) row n hdim P j b
  have hm : 0 ≤ L.mass := by
    apply sum_nonneg
    intro c hc
    exact mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _)
  have hden := mul_le_mul_of_nonneg_left (h4 N (by omega) hn) hm
  change L.R1 _ _ ≤ _ at ha
  change L.R2 _ _ ≤ _ at hb
  change L.small _ ≤ _ at hc
  change L.primeMass ≤ _
  linarith only [hf,ha,hb,hc,hden]

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.family_density
