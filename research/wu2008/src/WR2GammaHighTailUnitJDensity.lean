import WR2GammaHighTailUnitBoxDensity
import WR2GammaHighTailUnitIntegral
import WR2GammaHighLowerTripleNormalization

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnit HighUnitSource HighUnitPrimeOutput Real
open scoped Classical

def integralJMain (row : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  let p := Wu04RemainingCore.row row
  boxedIntegral20 N δ (windows row N) (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
    boxedIntegral21 N δ (windows row N) (fun _ => 1/p.kappa3) (fun _ => 1/p.s)

theorem actual_unit_J_density {δ ρ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100)
    (hr : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ row : Fin 3,
      HighNonunit.actualUnit N δ (Wu04RemainingCore.row row) (windows row N) false +
        HighNonunit.actualUnit N δ (Wu04RemainingCore.row row) (windows row N) true ≤
      integralJMain row N δ *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N)+
        ε*truncatedSixthMassScale N := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith) (by positivity))
    (div_pos (by norm_num) (by linarith))
  obtain ⟨T1,hT1,h1⟩ := envelope_pair_density hd hh hr (half_pos he)
  obtain ⟨T2,_,h2⟩ := boxed_sigma_pair_combined hd hh (div_pos he (mul_pos (by norm_num) hA) : 0 < ε/(480*A))
  obtain ⟨T3,_,h3⟩ := LowerTriple.reciprocal_mass_scale hd hh
  refine ⟨max T1 (max T2 T3),by omega,?_⟩
  intro N hN hn row
  let p := Wu04RemainingCore.row row
  let X := boxedSigma20 N δ (windows row N) (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
    boxedSigma21 N δ (windows row N) (fun _ => 1/p.kappa3) (fun _ => 1/p.s)
  have hp := (row_analytic row).mother
  have hs := (row_analytic row).two_lt_s.le
  have hu := (mother_unit_pair_filtered row (by omega : 2 ≤ N) hd hh).trans
    (h1 N (by omega) hn row (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s))
  have hu' : HighNonunit.actualUnit N δ p (windows row N) false +
      HighNonunit.actualUnit N δ p (windows row N) true ≤
      X*(A*wuSingularSeries N/log N)+(ε/2)*truncatedSixthMassScale N := by
    simpa only [HighNonunit.actualUnit,HighNonunit.word,Bool.false_eq_true,if_false,if_true,p,X,A] using hu
  have hq := (le_abs_self _).trans ((h2 N (by omega) row _ _ _
    (fun _ _ => parameter_outer_bounds hp hs)).2.2)
  change X-integralJMain row N δ ≤ (ε/(480*A))*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows row N) at hq
  have hC : 0 ≤ wuSingularSeries N/log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hb := mul_le_mul_of_nonneg_right hq (mul_nonneg hA.le hC)
  have hc := mul_le_mul_of_nonneg_left (h3 N (by omega) hn row) (show 0 ≤ ε/480 by positivity)
  have cancel : ((ε/(480*A))*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows row N))*(A*(wuSingularSeries N/log N)) =
      (ε/480)*(wuSingularSeries N/log N*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows row N)) := by
    field_simp
  rw [sub_mul,cancel] at hb
  rw [mul_div_assoc] at hu' ⊢
  change _ ≤ integralJMain row N δ*(A*(wuSingularSeries N/log N))+_
  linarith only [hu',hb,hc]

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.actual_unit_J_density
