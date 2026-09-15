import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2Atom
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summing all actual R2 blocks before normalization

Wu04 (3.19), source lines 1128--1149. Exact half-open partition removes
the moving block count. An elementary harmonic majorant then suffices
for an `O(log(N)^(-2))*Theta` payment (we do not claim the sharper printed
`O(log(N)^(-3))` rate). Every original convolution multiplicity remains.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

theorem reboxing_prime_mass_le_harmonic (N : ℕ) {Y Z : ℝ} (hZ : Z ≤ N) :
    (∑ p ∈ primeWindow N Y Z, (1 : ℝ) / p) ≤ 1 + log (N : ℝ) := by
  have hsub : primeWindow N Y Z ⊆ Icc 1 N := by
    intro p hp
    have hh := mem_primeWindow.mp hp
    exact mem_Icc.mpr ⟨hh.1.pos, by exact_mod_cast hh.2.2.2.le.trans hZ⟩
  calc
    _ ≤ ∑ p ∈ Icc 1 N, (1 : ℝ) / p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = harmonic N := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log N

noncomputable def reboxingR2 {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ p ∈ primeWindow N
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j)
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)),
      ((sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ) -
        (sourceSieveCount N (d * p) ((d * p) * N)
          (wuLocalCutoff N δ (d * p)
            (reboxingS1 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1))) : ℝ))

/-- Genuine aggregate R2 payment, uniformly before all legal boxes,
outer parameters and terminal indices. Only the upper terminal bound
is needed; a zero terminal index is included. -/
theorem reboxingR2_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      0 ≤ reboxingR2 N δ Δ V t r ∧ reboxingR2 N δ Δ V t r ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨B, hB, T1, hT1⟩ := reboxingR2_atom_bound k hδ hδhi
  have hU := liuUniversalProduct_pos
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbudget : ∀ᶠ N : ℕ in atTop,
      B / (liuUniversalProduct * ε) ≤ log (N : ℝ) ^ (2 : ℕ) :=
    ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hlogt).eventually (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T1, eventually_ge_atTop (4 : ℕ), hbudget,
    hlogt.eventually (eventually_ge_atTop 1)] with N hN1 hN4 hbud hL1
  intro he i Δ V hb s t hs hst ht r hr
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let W := convolutionWuWindows N Δ V
  let q := Q / (∏ l, V l)
  let L := log (N : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos hL (-4 : ℝ)
    dsimp [L] at hh
    linarith [hb.2.1]
  have hq : 1 < q := (one_lt_rpow hNreal (pow_pos hδ _)).trans_le
    (reboxing_box_level_ge_lower (by omega) hδ hδhi hb)
  have hq0 : 0 < q := by linarith
  have hQ : 1 < Q := one_lt_rpow hNreal (by linarith)
  have hQN : Q ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNreal.le
      (show 1 / 2 - δ ≤ 1 by linarith)
  have hw1 : 1 < (N : ℝ) ^ (δ ^ (k + 1)) := one_lt_rpow hNreal (pow_pos hδ _)
  have hsupport := fun d hd => boxSquaredPrefixes_support hw1 hQ hQN hb.2.2.2.2.1
    hb.2.2.2.2.2 (Δ := Δ) (d := d) hd
  have hatom := hT1 N hN1 he i Δ V hb s t hs hst ht r hr
  have hnon : 0 ≤ reboxingR2 N δ Δ V t r := by
    unfold reboxingR2
    apply sum_nonneg
    intro j hj
    apply sum_nonneg
    intro d hd
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro p hp
    have hjr := mem_range.mp hj
    have hh := hatom (j + 1) (by omega) (by omega) d hd p
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hh
    exact (hh hp).1
  have haggregate : reboxingR2 N δ Δ V t r ≤
      (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p := by
    calc
      _ ≤ ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) := by
        unfold reboxingR2
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro p hp
        have hjr := mem_range.mp hj
        have hh := hatom (j + 1) (by omega) (by omega) d hd p
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hh
        exact (hh hp).2
      _ = ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) :=
        (reboxingAlpha_convolution_sum_partition hq0 hΔ N r W _).symm
      _ = _ := by
        unfold boxConvolutionReciprocalMass
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro p _
        ring
  have hprod1 : 1 ≤ ∏ l, V l :=
    one_le_prod (fun l _ => hw1.le.trans (hb.2.2.2.2.1 l))
  have hqN : q ≤ N := (div_le_self (by linarith : 0 ≤ Q) hprod1).trans hQN
  have hZ : reboxingAlpha q Δ t r ≤ N := by
    calc
      _ ≤ q ^ (1 / s) := hr
      _ ≤ q ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hq.le
        ((one_div_le_one_div_of_le (by norm_num) (by linarith : 1 ≤ s)).trans_eq (by norm_num))
      _ = q := rpow_one q
      _ ≤ N := hqN
  have hprime :
      (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p) ≤
        2 * L := (reboxing_prime_mass_le_harmonic N hZ).trans (by dsimp [L]; linarith)
  have hmass : 0 ≤ boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    exact sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hTheta := boxTheta_lower_of_support W hN4 (fun d hd => (hsupport d hd).1)
    (fun d hd => (hsupport d hd).2)
  have hθ : 0 ≤ boxTheta N Q W := (by positivity :
    0 ≤ 2 * liuUniversalProduct * (N : ℝ) / log (N : ℝ) ^ (2 : ℕ) *
      boxConvolutionReciprocalMass W).trans hTheta
  have hpay : B / liuUniversalProduct / L ^ (2 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := (div_le_iff₀ (mul_pos hU hε)).1 hbud
    apply (div_le_iff₀ hU).2
    dsimp [L]
    nlinarith
  refine ⟨hnon, ?_⟩
  calc
    _ ≤ (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p :=
      haggregate
    _ ≤ (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W * (2 * L) :=
      mul_le_mul_of_nonneg_left hprime (by positivity)
    _ = (B / liuUniversalProduct / L ^ (2 : ℕ)) *
        (2 * liuUniversalProduct * (N : ℝ) / log (N : ℝ) ^ (2 : ℕ) *
          boxConvolutionReciprocalMass W) := by dsimp [L]; field_simp
    _ ≤ (B / liuUniversalProduct / L ^ (2 : ℕ)) * boxTheta N Q W :=
      mul_le_mul_of_nonneg_left hTheta (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay hθ

end Wu2008DoubleSieve
