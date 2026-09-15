import Wu18938Campaign.M1.Confirmed.NonunitIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighPayloadNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighSourcePayload Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

theorem roughBox_theta_weight {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
  have hl := (roughBox_log_geometry hb (by omega) hη hδ hd).1
  have hC := wuSingularSeries_pos (d * N) (Nat.mul_pos (hb.support_pos hd) (by omega))
  positivity

theorem roughBox_payload_theta_bounds {m i N : ℕ} {η δ Δ B : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (f : ℕ → ℝ)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d ∧ f d ≤ B) :
    0 ≤ theta N δ Δ V f ∧ theta N δ Δ V f ≤
      B * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  constructor
  · unfold theta
    exact mul_nonneg (by positivity) (sum_nonneg (fun d hd =>
      mul_nonneg (roughBox_theta_weight hb hN hη hδ hd) (hf d hd).1))
  · unfold theta boxTheta
    rw [mul_left_comm B (4 * logarithmicIntegral N)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_sum]
    exact sum_le_sum (fun d hd => by
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left (hf d hd).2 (roughBox_theta_weight hb hN hη hδ hd))

theorem roughBox_mass_theta_comparison {m i N : ℕ} {η δ Δ τ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (f : ℕ → ℝ)
    (hf : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d)
    (hτ : 0 ≤ τ) (hli : (N : ℝ) / log N ≤ (1 + τ) * logarithmicIntegral N) :
    wuSingularSeries N / log N * mass N δ Δ V f ≤ (1 + τ) / 4 * theta N δ Δ V f := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  have hC0 := (wuSingularSeries_pos N (by omega)).le
  have hli0 : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hmass0 : 0 ≤ ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d : ℝ) * log (Q / d)) * f d := by
    apply sum_nonneg
    intro d hd
    have hl := (roughBox_log_geometry hb (by omega) hη hδ hd).1
    exact mul_nonneg (by positivity) (hf d hd)
  have hsum : wuSingularSeries N *
      (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) /
        ((d : ℝ) * log (Q / d)) * f d) ≤
      ∑ d ∈ boxConvolutionSupport W, ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log (Q / d))) * f d := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := hb.support_pos hd
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have htot : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have htotle : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl := (roughBox_log_geometry hb (by omega) hη hδ hd).1
    have hC := wuSingularSeries_le_mul (N := N) (by omega) hd0
    have hCd := hC0.trans hC
    calc
      _ = ((convolutionCoeff W d : ℝ) * wuSingularSeries N /
          ((d : ℝ) * log (Q / d))) * f d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by gcongr) (hf d hd)
  have heq : mass N δ Δ V f = (N : ℝ) * ∑ d ∈ boxConvolutionSupport W,
      (convolutionCoeff W d : ℝ) / ((d : ℝ) * log (Q / d)) * f d := by
    unfold mass
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by dsimp only [Q, W]; ring)
  calc
    _ = ((N : ℝ) / log N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) /
          ((d : ℝ) * log (Q / d)) * f d) := by rw [heq]; ring
    _ ≤ ((1 + τ) * logarithmicIntegral N) * (wuSingularSeries N *
        ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) /
          ((d : ℝ) * log (Q / d)) * f d) :=
      mul_le_mul_of_nonneg_right hli (mul_nonneg hC0 hmass0)
    _ ≤ ((1 + τ) * logarithmicIntegral N) *
        (∑ d ∈ boxConvolutionSupport W, ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
          ((Nat.totient d : ℝ) * log (Q / d))) * f d) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by unfold theta; dsimp only [W, Q]; ring

theorem roughBox_payload_density_slack (m : ℕ) {η δ B ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hB : 0 ≤ B) (he : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 ≤ f d ∧ f d ≤ B) →
      ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
        (wuSingularSeries N / log N) * mass N δ Δ V f ≤
        (2 / (1 - 2 * δ)) * theta N δ Δ V f +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hD : 0 < 1 - 2 * δ := by linarith
  have hcap := HighNonunit.sourceKCap_pos
  have hBp : 0 < B + 1 := by positivity
  obtain ⟨ρ, hr, hcoef⟩ := HighNonunit.sourceK_positive_slack hD
    (show 0 < ε * HighNonunit.sourceKCap / (B + 1) by positivity)
    (exp_pos (-eulerMascheroniConstant)).le
  have hcancel : (ε * HighNonunit.sourceKCap / (B + 1)) / HighNonunit.sourceKCap =
      ε / (B + 1) := by field_simp
  rw [hcancel] at hcoef
  obtain ⟨T, hT4, hT⟩ := HighUnitSource.trueLi_near_one hr
  refine ⟨ρ, hr, T, hT4, ?_⟩
  intro N hN i Δ V hb f hf
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc := roughBox_payload_theta_bounds hb (hT4.trans hN) hη hδ f hf
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    have ht := roughBox_reciprocal_theta hb (hT4.trans hN) hη hδ
    have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    have hm : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
      sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hC := wuSingularSeries_pos N (by omega)
    have hx : 0 ≤ wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by positivity
    linarith only [ht, hx]
  have hm := roughBox_mass_theta_comparison hb (hT4.trans hN) hη hδ f
    (fun d hd => (hf d hd).1) hr.le (hT N hN)
  have hcap' : theta N δ Δ V f ≤
      (B + 1) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    hc.2.trans (mul_le_mul_of_nonneg_right (by linarith) hθ)
  have hpay := mul_le_mul_of_nonneg_left hcap' (show 0 ≤ ε / (B + 1) by positivity)
  have heq : ε / (B + 1) * ((B + 1) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) =
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by field_simp
  rw [heq] at hpay
  calc
    _ = A * (wuSingularSeries N / log N * mass N δ Δ V f) := by ring
    _ ≤ A * ((1 + ρ) / 4 * theta N δ Δ V f) := mul_le_mul_of_nonneg_left hm hA
    _ = (A * ((1 + ρ) / 4)) * theta N δ Δ V f := by ring
    _ ≤ (2 / (1 - 2 * δ) + ε / (B + 1)) * theta N δ Δ V f :=
      mul_le_mul_of_nonneg_right hcoef hc.1
    _ ≤ _ := by rw [add_mul]; exact add_le_add le_rfl hpay

end Wu18938Campaign.M1.Confirmed
