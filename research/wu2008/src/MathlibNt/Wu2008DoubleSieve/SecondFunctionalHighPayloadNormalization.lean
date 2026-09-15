import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighKernelPayloads

namespace Wu2008DoubleSieve.HighSourcePayload
open Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- Nonnegativity needs the payload only on the original convolution support. -/
theorem mass_nonneg {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d) :
    0 ≤ mass N δ Δ V f := by
  unfold mass
  apply sum_nonneg
  intro d hd
  have hl := log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hl.le)) (hf d hd)

/-- The genuine original Theta is nonnegative, also for an empty or zero-mass box. -/
theorem originalTheta_nonneg {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    0 ≤ boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  unfold boxTheta
  exact mul_nonneg (mul_nonneg (by norm_num) hli)
    (sum_nonneg fun d hd => HighNonunit.sourceKTheta_weight_nonneg hN hδ hδhi hb hd)

/-- A nonnegative cap pays only against the unchanged Theta; no box mass is divided out. -/
theorem theta_bounds {i k N : ℕ} {δ Δ B : ℝ} {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      0 ≤ f d ∧ f d ≤ B) :
    0 ≤ theta N δ Δ V f ∧ theta N δ Δ V f ≤
      B * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  constructor
  · unfold theta
    apply mul_nonneg (mul_nonneg (by norm_num) hli)
    exact sum_nonneg fun d hd => mul_nonneg
      (HighNonunit.sourceKTheta_weight_nonneg hN hδ hδhi hb hd) (hf d hd).1
  · unfold theta boxTheta
    rw [mul_left_comm B (4 * logarithmicIntegral N)]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hli)
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf d hd).2
      (HighNonunit.sourceKTheta_weight_nonneg hN hδ hδhi hb hd)

/-- Termwise comparison retains the original coefficient, supported d, and logarithm.
The singular series is C(N) <= C(d*N); the totient is not replaced by equality. -/
theorem mass_theta_term_comparison {i k N d : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (hf : 0 ≤ f d) :
    wuSingularSeries N *
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) /
        ((d:ℝ)*log ((N:ℝ)^(1/2-δ)/d)) * f d) ≤
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        wuSingularSeries (d*N) /
        ((Nat.totient d : ℝ)*log ((N:ℝ)^(1/2-δ)/d))) * f d := by
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hd0 := (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  have hd0' : (0:ℝ) < d := by exact_mod_cast hd0
  have ht0 : (0:ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
  have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hl : 0 < log ((N:ℝ)^(1/2-δ)/d) :=
    log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  have hC := wuSingularSeries_le_mul (N := N) (by omega) hd0
  have hCd0 := hC0.trans hC
  calc
    _ = ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ)*wuSingularSeries N /
        ((d:ℝ)*log ((N:ℝ)^(1/2-δ)/d))) * f d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by gcongr) hf

/-- Conditional scalar comparison, consumed below by the actual true-li producer. -/
theorem mass_theta_comparison {i k N : ℕ} {δ Δ τ : ℝ}
    {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d)
    (hτ : 0 ≤ τ) (hli : (N:ℝ)/log N ≤ (1+τ)*logarithmicIntegral N) :
    wuSingularSeries N / log N * mass N δ Δ V f ≤ (1+τ)/4 * theta N δ Δ V f := by
  let W := convolutionWuWindows N Δ V
  let Q := (N:ℝ)^(1/2-δ)
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hli0 : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmass0 : 0 ≤ ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * f d := by
    apply sum_nonneg
    intro d hd
    have hR := (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hR).le)) (hf d hd)
  have hsum : wuSingularSeries N *
      (∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * f d) ≤
      ∑ d ∈ boxConvolutionSupport W,
        ((convolutionCoeff W d : ℝ) * wuSingularSeries (d*N) /
          ((Nat.totient d : ℝ)*log (Q/d))) * f d := by
    rw [mul_sum]
    exact sum_le_sum fun d hd => mass_theta_term_comparison hN hδ hδhi hb hd (hf d hd)
  have heq : mass N δ Δ V f = (N:ℝ) * ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * f d := by
    unfold mass
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    dsimp only [Q, W]
    ring
  calc
    _ = ((N:ℝ)/log N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * f d) := by rw [heq]; ring
    _ ≤ ((1+τ)*logarithmicIntegral N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) / ((d:ℝ)*log (Q/d)) * f d) :=
      mul_le_mul_of_nonneg_right hli (mul_nonneg hC0 hmass0)
    _ ≤ ((1+τ)*logarithmicIntegral N) *
        (∑ d ∈ boxConvolutionSupport W,
          ((convolutionCoeff W d : ℝ)*wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ)*log (Q/d))) * f d) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hli0)
    _ = _ := by unfold theta; dsimp only [W, Q]; ring

/-- The source mass also has a support-only cap, including B = 0. -/
theorem mass_bounds {i k N : ℕ} {δ Δ B : ℝ} {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      0 ≤ f d ∧ f d ≤ B) :
    0 ≤ mass N δ Δ V f ∧ mass N δ Δ V f ≤ B * mass N δ Δ V (fun _ => 1) := by
  refine ⟨mass_nonneg hN hδ hδhi hb (fun d hd => (hf d hd).1), ?_⟩
  unfold mass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hl := log_pos (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).2.1
  have hw : 0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) :=
    mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hl.le)
  simpa only [mul_one, mul_comm B] using mul_le_mul_of_nonneg_left (hf d hd).2 hw

/-- A B+1 budget is valid for every nonnegative cap, without division by B or Theta. -/
theorem theta_cap_payment {i k N : ℕ} {δ Δ B epsilon : ℝ}
    {V : Fin i → ℝ} {f : ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hB : 0 ≤ B) (he : 0 ≤ epsilon)
    (hb : wuSourceBox k δ N i Δ V)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      0 ≤ f d ∧ f d ≤ B) :
    epsilon/(B+1) * theta N δ Δ V f ≤
      epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hBp : 0 < B+1 := by positivity
  have hbox := originalTheta_nonneg hN hδ hδhi hb
  have hc := (theta_bounds hN hδ hδhi hb hf).2
  have hcplus : theta N δ Δ V f ≤
      (B+1) * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
    hc.trans (mul_le_mul_of_nonneg_right (by linarith) hbox)
  calc
    _ ≤ epsilon/(B+1) * ((B+1) *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) :=
      mul_le_mul_of_nonneg_left hcplus (div_nonneg he hBp.le)
    _ = _ := by field_simp

/-- The true logarithmic integral produces the near-quarter factor uniformly before f. -/
theorem mass_theta_near_one (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ f : ℕ → ℝ,
        (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d) →
      wuSingularSeries N/log N * mass N δ Δ V f ≤ (1+τ)/4 * theta N δ Δ V f := by
  obtain ⟨T, hT4, hT⟩ := HighUnitSource.trueLi_near_one hτ
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb f hf
  exact mass_theta_comparison (hT4.trans hN) hδ hδhi hb hf hτ.le (hT N hN)

/-- True-li quarter normalization for arbitrary support-bounded, N/box-dependent payloads. -/
theorem mass_theta_quarter (k : ℕ) {δ B epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ f : ℕ → ℝ,
        (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          0 ≤ f d ∧ f d ≤ B) →
      wuSingularSeries N/log N * mass N δ Δ V f ≤ theta N δ Δ V f/4 +
        epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := mass_theta_near_one k hδ hδhi
    (show 0 < 4*epsilon/(B+1) by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb f hf
  have hm := hT N hN i Δ V hb f (fun d hd => (hf d hd).1)
  have hpay := theta_cap_payment (hT4.trans hN) hδ hδhi hB he.le hb hf
  have hexpand : (1+4*epsilon/(B+1))/4 * theta N δ Δ V f =
      theta N δ Δ V f/4 + epsilon/(B+1) * theta N δ Δ V f := by ring
  rw [hexpand] at hm
  linarith only [hm, hpay]

/-- Positive rho precedes T, N, all original boxes and the arbitrary payload.
The original varying C(N) and the fixed delta loss are retained literally. -/
theorem mass_theta_density_slack (k : ℕ) {δ B epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hB : 0 ≤ B) (he : 0 < epsilon) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ f : ℕ → ℝ,
        (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          0 ≤ f d ∧ f d ≤ B) →
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
        (wuSingularSeries N/log N) * mass N δ Δ V f ≤
      (2/(1-2*δ))*theta N δ Δ V f +
        epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hD : 0 < 1-2*δ := by linarith
  have hcap := HighNonunit.sourceKCap_pos
  have hBp : 0 < B+1 := by positivity
  obtain ⟨ρ, hr, hcoef⟩ := HighNonunit.sourceK_positive_slack hD
    (show 0 < epsilon*HighNonunit.sourceKCap/(B+1) by positivity)
    (exp_pos (-eulerMascheroniConstant)).le
  have hcancel : (epsilon*HighNonunit.sourceKCap/(B+1))/HighNonunit.sourceKCap =
      epsilon/(B+1) := by field_simp
  rw [hcancel] at hcoef
  obtain ⟨T, hT4, hT⟩ := mass_theta_near_one k hδ hδhi hr
  refine ⟨ρ, hr, T, hT4, ?_⟩
  intro N hN i Δ V hb f hf
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc := theta_bounds (hT4.trans hN) hδ hδhi hb hf
  have hm := hT N hN i Δ V hb f (fun d hd => (hf d hd).1)
  have hpay := theta_cap_payment (hT4.trans hN) hδ hδhi hB he.le hb hf
  calc
    _ = A * (wuSingularSeries N/log N * mass N δ Δ V f) := by ring
    _ ≤ A * ((1+ρ)/4 * theta N δ Δ V f) := mul_le_mul_of_nonneg_left hm hA
    _ = (A*((1+ρ)/4))*theta N δ Δ V f := by ring
    _ ≤ (2/(1-2*δ)+epsilon/(B+1))*theta N δ Δ V f :=
      mul_le_mul_of_nonneg_right hcoef hc.1
    _ ≤ _ := by rw [add_mul]; exact add_le_add_right hpay _

end Wu2008DoubleSieve.HighSourcePayload
