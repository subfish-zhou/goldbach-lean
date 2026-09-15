import MathlibNt.Wu2008DoubleSieve.Omega3SourceBounds

/-!
# Relative payment of switching exceptions

The prime output is not counted just once: the bounds here retain a
per-output label bound C and the complete convolution mass. The saving
in d <= Q suffices even for the elementary square-root divisor bound.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

noncomputable def omega3ExceptionalOutputs (N : ℕ) (δ : ℝ) : Finset ℕ :=
  range ⌈sqrt ((N : ℝ) ^ (1 / 2 - δ))⌉₊ ∪ N.primeFactors

theorem mem_omega3ExceptionalOutputs {N l : ℕ} {δ : ℝ}
    (hN : N ≠ 0) (hl : l.Prime)
    (hbad : (l : ℝ) < sqrt ((N : ℝ) ^ (1 / 2 - δ)) ∨ l ∣ N) :
    l ∈ omega3ExceptionalOutputs N δ := by
  rcases hbad with hs | hd
  · exact mem_union_left _ (mem_range.mpr (Nat.lt_ceil.mpr hs))
  · exact mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hl, hd, hN⟩)

theorem omega3ExceptionalOutputs_card_le {N : ℕ} {δ : ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) :
    ((omega3ExceptionalOutputs N δ).card : ℝ) ≤ 4 * sqrt N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hNr (show 1 / 2 - δ ≤ 1 by linarith)
  have hroot := sqrt_le_sqrt hQ
  have hroot1 : 1 ≤ sqrt (N : ℝ) := by
    simpa only [sqrt_one] using sqrt_le_sqrt hNr
  have hc := Nat.ceil_lt_add_one (sqrt_nonneg ((N : ℝ) ^ (1 / 2 - δ)))
  have hp := primeFactors_card_le_sqrt_add_one N
  have hu : ((omega3ExceptionalOutputs N δ).card : ℝ) ≤
      (⌈sqrt ((N : ℝ) ^ (1 / 2 - δ))⌉₊ : ℝ) + (N.primeFactors.card : ℝ) := by
    have hh := card_union_le (range ⌈sqrt ((N : ℝ) ^ (1 / 2 - δ))⌉₊) N.primeFactors
    rw [card_range] at hh
    exact_mod_cast hh
  linarith

/-- Weighting the finite exceptional output set by every source coefficient
still saves delta relative to N. C is a per-output label multiplicity. -/
theorem omega3_exceptional_weight_le {i k N : ℕ} {δ Δ C : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hC : 0 ≤ C) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        (C * ((omega3ExceptionalOutputs N δ).card : ℝ))) ≤
      (4 * C * ((N : ℝ) / (N : ℝ) ^ δ)) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass :
      (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ)) ≤
      (N : ℝ) ^ (1 / 2 - δ) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd' := omega3_source_support_le_Q hN hδ hδhi hb hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd'.1
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hd0).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd'.2
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
  have hrec : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hpow : sqrt (N : ℝ) * (N : ℝ) ^ (1 / 2 - δ) =
      (N : ℝ) / (N : ℝ) ^ δ := by
    rw [sqrt_eq_rpow, ← rpow_add hNr]
    calc
      _ = (N : ℝ) ^ (1 - δ) := by congr 1; ring
      _ = _ := by rw [rpow_sub hNr, rpow_one]
  calc
    _ = (C * ((omega3ExceptionalOutputs N δ).card : ℝ)) *
        ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (C * (4 * sqrt (N : ℝ))) *
        ((N : ℝ) ^ (1 / 2 - δ) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (omega3ExceptionalOutputs_card_le (by omega) hδ.le) hC) hmass
        (sum_nonneg fun d _ => Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← hpow]; ring

/-- One threshold pays a fixed power saving against the original Theta
for every source box. It does not assume any estimate of a count. -/
theorem omega3_power_mass_relative (k : ℕ) {δ ε C ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε)
    (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (C * ((N : ℝ) / (N : ℝ) ^ ρ)) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 2
      (show 0 < C / (2 * ε * liuUniversalProduct) by positivity) hρ)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hpay := hT N ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoef : C * ((N : ℝ) / (N : ℝ) ^ ρ) ≤
      ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) := by
    calc
      _ ≤ C * ((N : ℝ) /
          ((C / (2 * ε * liuUniversalProduct)) * log (N : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hpay) hC.le
      _ = _ := by field_simp
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  calc
    _ ≤ (ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2)) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
      mul_le_mul_of_nonneg_right hcoef hmass
    _ = ε * ((2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (omega3_source_theta_lower hN4 hδ hδhi hb) hε.le

theorem omega3_exceptional_weight_relative (k : ℕ) {δ ε C : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) (hC : 0 < C) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
            (C * ((omega3ExceptionalOutputs N δ).card : ℝ))) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := omega3_power_mass_relative k hδ hδhi hε
    (show 0 < 4 * C by positivity) hδ
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  exact (omega3_exceptional_weight_le (show 2 ≤ N by omega) hδ hδhi hb hC.le).trans
    (hT N hN i Δ V hb)

end Wu2008DoubleSieve
