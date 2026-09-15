import HighO3Quadrature
import HighO3Buchstab

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

theorem theta_singular {i N : ℕ} {δ η : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) :
    2*wuSingularSeries N*N/log N^2*boxConvolutionReciprocalMass W ≤
      boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  apply boxTheta_lower_singular_of_support W hN (fun d hd => (hw d hd).1)
  intro d hd
  have hg := phi_bounds (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2
  refine ⟨hg.2.1,?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (hw d hd).1
  exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans (by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (show 1/2-δ ≤ 1 by linarith))

theorem scaled_error {i N : ℕ} {δ η ε K : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    (ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass W)*(K*wuSingularSeries N/log N) ≤
      (ε*K/2)*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  calc
    _ = (ε*K/2)*(2*wuSingularSeries N*N/log N^2*boxConvolutionReciprocalMass W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (theta_singular W hN hδ hδhi hη hw) (by positivity)

/-- Physical raw X to actual original triple integral with relative Theta error. -/
theorem X_integral_scaled {δ η K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveX N δ s t W*(K*wuSingularSeries N/log N) ≤
        omega3XIntegralMain N δ s t W*(K*wuSingularSeries N/log N)+
          ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  obtain ⟨T1,hT14,hT1⟩ := X_buchstab hδ hδhi hη (div_pos hε hK)
  obtain ⟨T2,_,hT2⟩ := buchstab_integral hδ hδhi hη (div_pos hε hK)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN i W hw s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN4 := hT14.trans hN1
  have h1 := hT1 N hN1 i W hw s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) i W hw s t hs hst ht
  have hC := wuSingularSeries_pos N (show 0 < N by omega)
  have hl := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hf : 0 ≤ K*wuSingularSeries N/log N := by positivity
  have hraw : omega3SieveX N δ s t W ≤ omega3XIntegralMain N δ s t W+
      (2*ε/K)*((N : ℝ)/log N)*boxConvolutionReciprocalMass W := by
    calc
      _ ≤ (omega3XIntegralMain N δ s t W+ε/K*((N : ℝ)/log N)*boxConvolutionReciprocalMass W)+
          ε/K*((N : ℝ)/log N)*boxConvolutionReciprocalMass W := h1.trans (add_le_add h2 le_rfl)
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_right hraw hf
  have hp := scaled_error W hN4 hδ hδhi hη hw (show 0 ≤ 2*ε/K by positivity) hK.le
  have heq : (2*ε/K)*K/2 = ε := by field_simp
  rw [heq] at hp
  rw [add_mul] at hmul
  exact hmul.trans (add_le_add le_rfl hp)

/-- Exact original quotient logarithms and full singular series are retained. -/
theorem integral_envelope_scaled {i N : ℕ} {δ η s t K τ : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hw : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hK : 0 ≤ K)
    (hli : (N : ℝ)/log N ≤ (1+τ)*logarithmicIntegral N) :
    omega3XIntegralMain N δ s t W*(K*wuSingularSeries N/log N) ≤
      ((1+τ)*K/4*omega3XIntegralEnvelope s t)*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  let Q := (N : ℝ)^(1/2-δ)
  let E := omega3XIntegralEnvelope s t
  let A := ∑ d ∈ boxConvolutionSupport W,(convolutionCoeff W d : ℝ)/((d : ℝ)*log (Q/d))
  let U := ∑ d ∈ boxConvolutionSupport W,(convolutionCoeff W d : ℝ)*wuSingularSeries (d*N)/
    ((Nat.totient d : ℝ)*log (Q/d))
  have hN0 : 0 < N := by omega
  have hC0 := wuSingularSeries_pos N hN0
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hE : 0 ≤ E := (omega3XIntegralEnvelope_bounds hs hst ht).1
  have hA : 0 ≤ A := sum_nonneg fun d hd => by
    have hl := log_pos (phi_bounds (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2).2.1
    dsimp [Q]; positivity
  have hS : wuSingularSeries N*A ≤ U := by
    dsimp [A,U]
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := (hw d hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have htpos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have htot : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl := log_pos (phi_bounds (by omega) hd0 hδ hδhi hη (hw d hd).2).2.1
    have hC := wuSingularSeries_le_mul hN0 hd0
    have hCd := hC0.trans_le hC
    calc
      _ = (convolutionCoeff W d : ℝ)*wuSingularSeries N/((d : ℝ)*log (Q/d)) := by ring
      _ ≤ _ := by dsimp [Q]; gcongr
  have hU : 0 ≤ U := (mul_nonneg hC0.le hA).trans hS
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N/(2*log N) by positivity).trans (box_trueLi_lower hN)
  have he : omega3XIntegralMain N δ s t W ≤ (N : ℝ)*E*A := by
    unfold omega3XIntegralMain
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    dsimp [A]
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hg := phi_bounds (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2
    have hl := log_pos hg.2.1
    have hφ : 2 ≤ omega3XPhi N d δ := by
      have : 0 < 2*δ/(1/2-δ) := by positivity
      linarith [hg.2.2.1]
    have he := omega3XIntegral_le_envelope hs hst ht hφ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
      (show 0 ≤ (convolutionCoeff W d : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)) by positivity)
  calc
    _ ≤ ((N : ℝ)*E*A)*(K*wuSingularSeries N/log N) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = (E*K)*((N : ℝ)/log N)*(wuSingularSeries N*A) := by ring
    _ ≤ (E*K)*((N : ℝ)/log N)*U := mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (E*K)*((1+τ)*logarithmicIntegral N)*U := by gcongr
    _ = _ := by dsimp [boxTheta,E,U,Q]; ring

end
end HighO3
