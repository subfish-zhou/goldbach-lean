import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSourceKMasses
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real HighNonunitLegal
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- A universal error cap, never a replacement for the paired K payload. -/
def sourceKCap : ℝ := 10 * (4^5 + 4^6)

theorem sourceKCap_pos : 0 < sourceKCap := by unfold sourceKCap; positivity

/-- Both legal masses use the very same phi. -/
theorem sourceLegalK_pair_bounds (N d : ℕ) (δ : ℝ)
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ sourceLegalK N d δ p false + sourceLegalK N d δ p true ∧
      sourceLegalK N d δ p false + sourceLegalK N d δ p true ≤ sourceKCap := by
  obtain ⟨ha, haa, _, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have h20 := K20_bounds (a3 := 1/p.kappa3) ha hb (omega3XPhi N d δ)
  have h21 := K21_bounds (ha.trans haa) hb (omega3XPhi N d δ)
  simp only [sourceLegalK, Bool.false_eq_true, ↓reduceIte]
  constructor
  · exact add_nonneg h20.1 h21.1
  · unfold sourceKCap
    nlinarith only [h20.2, h21.2]

/-- Nonnegative original Theta weight at every supported d. -/
theorem sourceKTheta_weight_nonneg {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      wuSingularSeries (d*N) / ((Nat.totient d : ℝ) * log ((N:ℝ)^(1/2-δ)/d)) := by
  have hd0 := (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  have hl := log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (wuSingularSeries_pos (d*N) (Nat.mul_pos hd0 (by omega))).le)
    (mul_nonneg (Nat.cast_nonneg _) hl.le)

/-- The cap multiplies the original Theta, without dividing by any box mass. -/
theorem sourceKTheta_bounds {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ sourceKTheta N δ Δ V p ∧ sourceKTheta N δ Δ V p ≤
      sourceKCap * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  constructor
  · unfold sourceKTheta
    apply mul_nonneg (mul_nonneg (by norm_num) hli)
    exact sum_nonneg fun d hd => mul_nonneg
      (sourceKTheta_weight_nonneg hN hδ hδhi hb hd)
      (sourceLegalK_pair_bounds N d δ hp hs).1
  · unfold sourceKTheta boxTheta
    rw [mul_left_comm sourceKCap (4 * logarithmicIntegral N)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hli)
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    rw [mul_comm sourceKCap]
    exact mul_le_mul_of_nonneg_left (sourceLegalK_pair_bounds N d δ hp hs).2
      (sourceKTheta_weight_nonneg hN hδ hδhi hb hd)

/-- Pointwise C(N) and totient comparison with the original coefficient and K pair. -/
theorem sourceLegalKMass_theta_comparison {i k N : ℕ} {δ Δ τ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (hτ : 0 ≤ τ)
    (hli : (N:ℝ)/log N ≤ (1+τ)*logarithmicIntegral N) :
    wuSingularSeries N / log N *
      (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true) ≤
      (1+τ)/4 * sourceKTheta N δ Δ V p := by
  let W := convolutionWuWindows N Δ V
  let Q := (N:ℝ)^(1/2-δ)
  let K := fun d => sourceLegalK N d δ p false + sourceLegalK N d δ p true
  have hK : ∀ d, 0 ≤ K d := fun d => (sourceLegalK_pair_bounds N d δ hp hs).1
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hli0 : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmass0 : 0 ≤ ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * K d := by
    apply sum_nonneg
    intro d hd
    have hR := (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hR).le)) (hK d)
  have hsum : wuSingularSeries N *
      (∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * K d) ≤
      ∑ d ∈ boxConvolutionSupport W,
        ((convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
          ((Nat.totient d : ℝ)*log (Q/d))) * K d := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hR := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
    have hd0 := (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
    have hd0' : (0:ℝ) < d := by exact_mod_cast hd0
    have ht0 : (0:ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl : 0 < log (Q/d) := log_pos hR.2.1
    have hC := wuSingularSeries_le_mul (N := N) (by omega) hd0
    have hCd0 := hC0.trans hC
    calc
      _ = ((convolutionCoeff W d : ℝ)*wuSingularSeries N /
          ((d:ℝ)*log (Q/d))) * K d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by gcongr) (hK d)
  have heq : sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true =
      (N:ℝ) * ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * K d := by
    unfold sourceLegalKMass
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro d _
    dsimp only [K, Q]
    ring
  calc
    _ = ((N:ℝ)/log N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * K d) := by rw [heq]; ring
    _ ≤ ((1+τ)*logarithmicIntegral N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * K d) :=
      mul_le_mul_of_nonneg_right hli (mul_nonneg hC0 hmass0)
    _ ≤ ((1+τ)*logarithmicIntegral N) *
        (∑ d ∈ boxConvolutionSupport W,
          ((convolutionCoeff W d : ℝ)*wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ)*log (Q/d))) * K d) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hli0)
    _ = _ := by unfold sourceKTheta; dsimp only [W, Q, K]; ring

/-- True-li quarter normalization; its threshold is uniform in all original boxes and p. -/
theorem sourceLegalKMass_theta_quarter (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      wuSingularSeries N / log N *
        (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true) ≤
        sourceKTheta N δ Δ V p / 4 +
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hB := sourceKCap_pos
  obtain ⟨T, hT4, hT⟩ := HighUnitSource.trueLi_near_one
    (show 0 < 4*epsilon/sourceKCap by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have hc := sourceKTheta_bounds (hT4.trans hN) hδ hδhi hb hp hs
  have hm := sourceLegalKMass_theta_comparison (hT4.trans hN) hδ hδhi hb hp hs
    (show 0 ≤ 4*epsilon/sourceKCap by positivity) (hT N hN)
  have hpay := mul_le_mul_of_nonneg_left hc.2
    (show 0 ≤ epsilon/sourceKCap by positivity)
  have hcancel : epsilon/sourceKCap * (sourceKCap *
      boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) =
      epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    field_simp
  rw [hcancel] at hpay
  have hexpand : (1+4*epsilon/sourceKCap)/4 * sourceKTheta N δ Δ V p =
      sourceKTheta N δ Δ V p / 4 + epsilon/sourceKCap * sourceKTheta N δ Δ V p := by ring
  rw [hexpand] at hm
  linarith only [hm, hpay]

/-- Small positive rho pays both density factors and the true-li slack together. -/
theorem sourceK_positive_slack {D epsilon E : ℝ}
    (hD : 0 < D) (he : 0 < epsilon) (hE : 0 ≤ E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ((1+ρ)*(1+ρ*E)*(8/D))*((1+ρ)/4) ≤ 2/D + epsilon/sourceKCap := by
  have hB := sourceKCap_pos
  have hL : 0 < 3+4*E := by positivity
  let η := epsilon*D/(2*sourceKCap)
  have hη : 0 < η := by dsimp [η]; positivity
  let ρ := min 1 (η/(3+4*E))
  have hr : 0 < ρ := lt_min (by norm_num) (div_pos hη hL)
  have hr1 : ρ ≤ 1 := min_le_left _ _
  have hrη : ρ*(3+4*E) ≤ η :=
    (le_div_iff₀ hL).mp (min_le_right _ _)
  have hsq : (1+ρ)^2 ≤ 1+3*ρ := by nlinarith only [hr.le, hr1]
  have hsq4 : (1+ρ)^2 ≤ 4 := by nlinarith only [hsq, hr1]
  have hprod : (1+ρ)*(1+ρ*E)*(1+ρ) ≤ 1+η := by
    have hm := mul_le_mul_of_nonneg_right hsq4 (mul_nonneg hr.le hE)
    nlinarith only [hm, hsq, hrη]
  refine ⟨ρ, hr, ?_⟩
  calc
    _ = (2/D)*((1+ρ)*(1+ρ*E)*(1+ρ)) := by ring
    _ ≤ (2/D)*(1+η) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by dsimp only [η]; field_simp

/-- Positive rho is chosen before the threshold and before N, boxes, and parameters.
The fixed delta loss remains in the leading coefficient; the universal cap only pays epsilon. -/
theorem sourceLegalKMass_theta_density_slack (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
        (wuSingularSeries N/log N) *
        (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true) ≤
      (2/(1-2*δ))*sourceKTheta N δ Δ V p +
        epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hD : 0 < 1-2*δ := by linarith
  have hB := sourceKCap_pos
  obtain ⟨ρ, hr, hcoef⟩ := sourceK_positive_slack hD he (exp_pos (-eulerMascheroniConstant)).le
  obtain ⟨T, hT4, hT⟩ := HighUnitSource.trueLi_near_one hr
  refine ⟨ρ, hr, T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc := sourceKTheta_bounds (hT4.trans hN) hδ hδhi hb hp hs
  have hm := sourceLegalKMass_theta_comparison (hT4.trans hN) hδ hδhi hb hp hs
    hr.le (hT N hN)
  have hpay := mul_le_mul_of_nonneg_left hc.2
    (show 0 ≤ epsilon/sourceKCap by positivity)
  have hcancel : epsilon/sourceKCap * (sourceKCap *
      boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) =
      epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by field_simp
  rw [hcancel] at hpay
  calc
    _ = A * (wuSingularSeries N/log N *
        (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true)) := by ring
    _ ≤ A * ((1+ρ)/4 * sourceKTheta N δ Δ V p) := mul_le_mul_of_nonneg_left hm hA
    _ = (A*((1+ρ)/4))*sourceKTheta N δ Δ V p := by ring
    _ ≤ (2/(1-2*δ)+epsilon/sourceKCap)*sourceKTheta N δ Δ V p :=
      mul_le_mul_of_nonneg_right hcoef hc.1
    _ ≤ _ := by rw [add_mul]; exact add_le_add_right hpay _

end Wu2008DoubleSieve.HighNonunit
