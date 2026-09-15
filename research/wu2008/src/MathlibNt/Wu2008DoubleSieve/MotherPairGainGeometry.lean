import MathlibNt.Wu2008DoubleSieve.MotherPairGainComparison
import MathlibNt.Wu2008DoubleSieve.Gamma5GainGeometry

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

/-- A right-endpoint sample tolerates a small downward shift in both coordinates. -/
theorem ratio_margin (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) :
    ∃ e : ℝ, 0 < e ∧ ∀ t u : ℝ, r.A-e ≤ t → r.C-e ≤ u →
      Hratio p j t u ≤ r.sample := by
  have hS : 0 < p.S := by linarith [h.three_le_S]
  have hA : 0 < r.A := (one_div_pos.mpr hS).trans r.lowerP_lt_A
  have hs : 0 < r.sample := by linarith [r.sample_lower]
  have hf {A C s : ℝ} (hg : p.S*(1-A-C) < s) :
      ∃ e : ℝ, 0 < e ∧ ∀ t u : ℝ, A-e ≤ t → C-e ≤ u → p.S*(1-t-u) ≤ s := by
    let e := (s-p.S*(1-A-C))/(2*p.S)
    have he : 0 < e := div_pos (sub_pos.mpr hg) (by positivity)
    have heq : e*(2*p.S) = s-p.S*(1-A-C) := div_mul_cancel₀ _ (by positivity)
    refine ⟨e,he,?_⟩
    intro t u ht hu
    nlinarith [mul_le_mul_of_nonneg_left ht hS.le,
      mul_le_mul_of_nonneg_left hu hS.le]
  have hv {A C s : ℝ} (hA : 0 < A) (hs : 0 < s) (hg : (1-A-C)/A < s) :
      ∃ e : ℝ, 0 < e ∧ ∀ t u : ℝ, A-e ≤ t → C-e ≤ u → (1-t-u)/t ≤ s := by
    have hg' := (div_lt_iff₀ hA).mp hg
    let e := min (A/2) ((s*A-(1-A-C))/(s+2))
    have he : 0 < e := lt_min (half_pos hA) (div_pos (by linarith) (by linarith))
    have heA : e ≤ A/2 := min_le_left _ _
    have heg : e*(s+2) ≤ s*A-(1-A-C) :=
      (le_div_iff₀ (by linarith : 0 < s+2)).mp (min_le_right _ _)
    refine ⟨e,he,?_⟩
    intro t u ht hu
    have ht0 : 0 < t := by linarith
    apply (div_le_iff₀ ht0).mpr
    nlinarith [mul_le_mul_of_nonneg_left ht hs.le]
  cases j with
  | gammaFive => exact hf r.ratio_lt_sample
  | gammaSix => exact hf r.ratio_lt_sample
  | gammaSeven => exact hv hA hs r.ratio_lt_sample
  | gammaEight => exact hv hA hs r.ratio_lt_sample

/-- Endpoint coordinates are recovered from the actual real endpoints. -/
theorem endpoint_coordinates {R P A B : ℝ} (hR : 1 < R)
    (hP : R^A ≤ P) (hPB : P ≤ R^B) :
    0 < P ∧ A ≤ log P/log R ∧ log P/log R ≤ B ∧ R^(log P/log R) = P := by
  have hR0 : 0 < R := by linarith
  have hp : 0 < P := (rpow_pos_of_pos hR0 _).trans_le hP
  refine ⟨hp,?_,?_,?_⟩
  · apply (le_div_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using log_le_log (rpow_pos_of_pos hR0 _) hP
  · apply (div_le_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using log_le_log hp hPB
  · rw [rpow_def_of_pos hR0]
    rw [mul_div_cancel₀ _ (log_pos hR).ne', exp_log hp]

/-- Both sorted slots, in the genuine Q-then-P order. -/
theorem rectangle_sorted_slots (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) {R P Q : ℝ} (hR : 1 < R)
    (hPA : R^r.A ≤ P) (hPB : P ≤ R^r.B) (hQC : R^r.C ≤ Q) (hQD : Q ≤ R^r.D) :
    R^(1/10:ℝ) ≤ Q ∧ Q ≤ R^(1/2:ℝ) ∧
      (R/Q)^(1/10:ℝ) ≤ P ∧ P ≤ (R/Q)^(1/2:ℝ) := by
  obtain ⟨_,htA,htB,heP⟩ := endpoint_coordinates hR hPA hPB
  obtain ⟨_,huC,huD,heQ⟩ := endpoint_coordinates hR hQC hQD
  have hz := sorted_rpow_admission hR (by linarith [h.three_le_S] : 0 < p.S)
    h.S_le_five (r.lowerP_lt_A.le.trans htA)
    (htB.trans (r.B_lt_C.le.trans huC))
    (by linarith [r.twiceD_lt_one] : 2*(log Q/log R) ≤ 1)
    (by linarith [r.D_twiceB_lt_one] : log Q/log R+2*(log P/log R) ≤ 1)
  simpa only [heP,heQ] using hz

/-- Half-open micro-windows include the actual Delta shift. -/
theorem micro_coordinate {N a : ℕ} {R Δ P A B : ℝ}
    (hR : 1 < R) (hΔ : 0 < Δ) (hPA : R^A ≤ P) (hPB : P ≤ R^B)
    (ha : a ∈ primeWindow N (P/Δ) P) :
    A-log Δ/log R ≤ gamma5MassCoordinate R a ∧ gamma5MassCoordinate R a < B := by
  have hp := (rpow_pos_of_pos (by linarith : 0 < R) A).trans_le hPA
  have ha' := mem_primeWindow.mp ha
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha'.1.pos
  have hlo := log_le_log (div_pos hp hΔ) ha'.2.2.1
  rw [log_div hp.ne' hΔ.ne'] at hlo
  have he := endpoint_coordinates hR hPA hPB
  constructor
  · have hdiv := div_le_div_of_nonneg_right hlo (log_pos hR).le
    dsimp [gamma5MassCoordinate]
    rw [sub_div] at hdiv
    linarith [he.2.1]
  · apply (div_lt_iff₀ (log_pos hR)).mpr
    have hh := log_lt_log ha0 (ha'.2.2.2.trans_le hPB)
    simpa only [log_rpow (by linarith : 0 < R)] using hh

/-- Uniform whole-source drift, not an identification of the two levels. -/
theorem micro_source_coordinate {i k N a : ℕ} {δ Δ P A B : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hb : wuSourceBox k δ N i Δ V) (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (hB : B ≤ 1) (hPA : (gamma5GainScale N δ V)^A ≤ P)
    (hPB : P ≤ (gamma5GainScale N δ V)^B)
    {d : ℕ} (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (ha : a ∈ primeWindow N (P/Δ) P) :
    A-(((k:ℝ)+1)*log Δ/log (gamma5GainScale N δ V)) ≤
      gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/d) a ∧
      gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/d) a < B := by
  have hm := micro_coordinate hR (by linarith : 0 < Δ) hPA hPB ha
  have hV : ∀ b, 0 < V b := fun b =>
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _).trans_le (hb.2.2.2.2.1 b)
  have hlev := (reboxing_support_level_bounds (Q := (N:ℝ)^(1/2-δ))
    (rpow_nonneg (Nat.cast_nonneg N) _) (by linarith : 0 < Δ) hV hd).1
  have ha' := mem_primeWindow.mp ha
  have haR : (a:ℝ) ≤ (N:ℝ)^(1/2-δ)/d := by
    apply ((ha'.2.2.2.le.trans hPB).trans ?_).trans hlev
    simpa only [rpow_one, gamma5GainScale] using rpow_le_rpow_of_exponent_le hR.le hB
  have hdri := gamma5Gain_coordinate_drift hN hδ hδhi hb hd ha'.1.one_le haR
  have hik : (i:ℝ) ≤ k := by exact_mod_cast hb.1
  have hmul := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hik (log_pos hΔ).le) (log_pos hR).le
  have he : ((k:ℝ)+1)*log Δ/log (gamma5GainScale N δ V) =
      (k:ℝ)*log Δ/log (gamma5GainScale N δ V)+log Δ/log (gamma5GainScale N δ V) := by ring
  constructor <;> linarith

end Wu2008DoubleSieve.MotherPair
