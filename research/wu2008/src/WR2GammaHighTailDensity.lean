import WR2GammaHighTailR1
import WR2GammaHighTailR2
import WR2GammaHighTailSmall
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit Real Finset
open scoped Classical

theorem restricted_prime_mass_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Bool, ∀ P : Profile → Prop,
      ((sourceFamily j N δ k).restrictLabels P).primeMass ≤
        ((sourceFamily j N δ k).restrictLabels P).mass*ordinaryRosserMainSum true N 1
          (⌊(N : ℝ)^(1/2-δ)⌋₊+1) (sqrt ((N : ℝ)^(1/2-δ)))+ε*truncatedSixthMassScale N := by
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT1,h1⟩ := restricted_R1_paid hd hh he3
  obtain ⟨T2,_,h2⟩ := R2_paid hd hh he3
  obtain ⟨T3,_,h3⟩ := small_paid hd hh he3
  refine ⟨max T1 (max T2 T3),by omega,fun N hN hEven j k P => ?_⟩
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  have hf := ((sourceFamily j N δ k).restrictLabels P).prime_upper_finite hEven _ _
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have ha := h1 N (by omega) j k P (sqrt ((N : ℝ)^(1/2-δ)))
  have hb := ((sourceFamily j N δ k).restrictLabels_R2_le P _ _).trans (h2 N (by omega) j k)
  have hc := ((sourceFamily j N δ k).restrictLabels_small_le P _).trans (h3 N (by omega) j k)
  linarith only [hf,ha,hb,hc]

theorem restricted_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ k : Bool, ∀ P : Profile → Prop,
      ((sourceFamily j N δ k).restrictLabels P).primeMass ≤ ((sourceFamily j N δ k).restrictLabels P).mass*
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
          ε*truncatedSixthMassScale N := by
  obtain ⟨T1,hT1,h1⟩ := restricted_prime_mass_paid hd hh he
  obtain ⟨T2,_,h2⟩ := omega3_source_rosser_density hd (by linarith : δ < 1/2) hr
  refine ⟨max T1 T2,by omega,fun N hN hEven j k P => ?_⟩
  have hm : 0 ≤ ((sourceFamily j N δ k).restrictLabels P).mass := by
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (((sourceFamily j N δ k).restrictLabels P).weight_nonneg x hx) (Nat.cast_nonneg _)
  exact (h1 N (by omega) hEven j k P).trans
    (add_le_add (mul_le_mul_of_nonneg_left (h2 N (by omega) hEven) hm) le_rfl)

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.restricted_density
