import WR2GammaHighCoupledKernel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

noncomputable section
namespace WuPaper.R2GammaHigh.Coupled
open Wu2008DoubleSieve HighUnitSource HighUnit Real Finset
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

theorem unitLogMass_theta_comparison {N : ℕ} {δ τ : ℝ} (row : Fin 3)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hτ : 0 ≤ τ)
    (hli : (N:ℝ) / log N ≤ (1+τ) * logarithmicIntegral N) :
    wuSingularSeries N / log N * unitLogMass N δ (windows row N) ≤
      (1+τ)/4 * boxTheta N ((N:ℝ)^(1/2-δ)) (windows row N) := by
  let W := windows row N
  let Q := (N:ℝ)^(1/2-δ)
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hli0 : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmass0 : 0 ≤ ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d)) := by
    apply sum_nonneg
    intro d hd
    have hR := (LowerTriple.phi_bounds row (by omega) hδ hδhi hd).2.1
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (log_pos hR).le)
  have hsum : wuSingularSeries N *
      (∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) ≤
      ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
          ((Nat.totient d : ℝ) * log (Q/d)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hs := LowerTriple.phi_bounds row (by omega) hδ hδhi hd
    have hd0 := boxConvolutionSupport_pos (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
    have hd0' : (0:ℝ) < d := by exact_mod_cast hd0
    have ht0 : (0:ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl : 0 < log (Q/d) := log_pos hs.2.1
    have hC := wuSingularSeries_le_mul (N := N) (by omega) hd0
    have hCd0 := hC0.trans hC
    calc
      _ = (convolutionCoeff W d : ℝ) * wuSingularSeries N /
          ((d:ℝ)*log (Q/d)) := by ring
      _ ≤ _ := by gcongr
  calc
    _ = ((N:ℝ) / log N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) := by
      unfold unitLogMass
      dsimp only [W, Q]
      ring
    _ ≤ ((1+τ)*logarithmicIntegral N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ) * log (Q/d))) :=
      mul_le_mul_of_nonneg_right hli (mul_nonneg hC0 hmass0)
    _ ≤ ((1+τ)*logarithmicIntegral N) *
        (∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ) * log (Q/d))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hli0)
    _ = _ := by unfold boxTheta; dsimp only [W, Q]; ring

end WuPaper.R2GammaHigh.Coupled
#print axioms WuPaper.R2GammaHigh.Coupled.unitLogMass_theta_comparison
