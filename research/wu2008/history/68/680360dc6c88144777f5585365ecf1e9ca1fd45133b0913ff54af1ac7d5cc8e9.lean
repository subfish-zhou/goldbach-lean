import MathlibNt.Wu2008DoubleSieve.Gamma5MassMain

/-!
# Bilateral arithmetic atoms for arbitrary actual label masks

This finite comparison does not assume the mask is rectangular. It retains
the complete original convolution coefficient and the true logarithmic
integral. Rectangular quadrature is supplied separately.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def gamma5MassReciprocalMask {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) : ℝ :=
  4 * logarithmicIntegral N * ∑ x ∈ X,
    (convolutionCoeff W x.1 : ℝ) *
      gamma5MassOldWeight N x.1 ((N : ℝ) ^ (1 / 2 - δ)) *
      (gamma5MassH
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) /
          ((x.2.1 : ℝ) * x.2.2))

theorem gamma5Mass_actual_label_identity (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V),
        wuSingularSeries (gamma5ClassicalProduct x * N) /
          ((Nat.totient (gamma5ClassicalProduct x) : ℝ) * log (gamma5ClassicalLevel N δ x)) =
        gamma5MassOldWeight N x.1 ((N : ℝ) ^ (1 / 2 - δ)) *
          (gamma5MassAtom x.1 x.2.1 * gamma5MassAtom (x.1 * x.2.1) x.2.2 *
            gamma5MassH
              (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
              (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2)) := by
  filter_upwards [gamma5Mass_label_eventually k hδ hδhi, eventually_ge_atTop (2 : ℕ)]
    with N hlabels hN
  intro i Δ V hb x hx
  have hg := hlabels i Δ V hb x hx
  obtain ⟨hd, hp, hq, hpN, hqN, _hz, _hpq, _hqu⟩ :=
    (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp hx
  have hbase := gamma5Mass_support_geometry hN hδ hδhi hb hd
  have hrect : x ∈ gamma5MassRectLabels N δ (convolutionWuWindows N Δ V)
      gamma5MassA gamma5ClassicalB gamma5MassA gamma5ClassicalB := by
    rwa [gamma5Mass_full_labels_eq hN hδ hδhi hb]
  have hc := (mem_filter.mp hrect).2
  have hid := gamma5Mass_two_insertions (by omega : 0 < N) hbase.1 hp hq hg.1 hg.2.1
    hpN hqN hbase.2.2.1
  simp only [gamma5ClassicalLevel, gamma5ClassicalProduct, Nat.cast_mul]
  rw [hid, gamma5Mass_H_eq hc.2.1 hc.2.2.2]
  ring

theorem gamma5Mass_actual_mask_bilateral (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
      X ⊆ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) →
      gamma5MassReciprocalMask N δ (convolutionWuWindows N Δ V) X ≤
        gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X ∧
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X ≤
        (1 + 4 / (N : ℝ) ^ gamma5ClassicalAlpha k δ) ^ 2 *
          gamma5MassReciprocalMask N δ (convolutionWuWindows N Δ V) X := by
  have hα := (gamma5Classical_exponents_pos k hδ hδhi).1
  filter_upwards [gamma5Mass_actual_label_identity k hδ hδhi,
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop (2 : ℕ)]
      with N hid hfour hN
  intro i Δ V hb X hX
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
      0 (by norm_num) (by exact_mod_cast hN))
  have hpoint (x : Gamma5ClassicalLabel) (hx : x ∈ X) :
      let R := (N : ℝ) ^ (1 / 2 - δ) / x.1
      let H := gamma5MassH (gamma5MassCoordinate R x.2.1) (gamma5MassCoordinate R x.2.2)
      let w := (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        gamma5MassOldWeight N x.1 ((N : ℝ) ^ (1 / 2 - δ))
      w * (H / ((x.2.1 : ℝ) * x.2.2)) ≤
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          wuSingularSeries (gamma5ClassicalProduct x * N) /
            ((Nat.totient (gamma5ClassicalProduct x) : ℝ) * log (gamma5ClassicalLevel N δ x)) ∧
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          wuSingularSeries (gamma5ClassicalProduct x * N) /
            ((Nat.totient (gamma5ClassicalProduct x) : ℝ) * log (gamma5ClassicalLevel N δ x)) ≤
        (1 + 4 / (N : ℝ) ^ gamma5ClassicalAlpha k δ) ^ 2 *
          (w * (H / ((x.2.1 : ℝ) * x.2.2))) := by
    dsimp only
    have hg := gamma5Classical_label_geometry hN hδ hδhi hb (hX hx)
    obtain ⟨ha, _hp, _hq, _hpN, _hqN, _hz, hpq, _hqu⟩ := mem_filter.mp (hX hx)
    have hw := mul_nonneg (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) x.1))
      (gamma5Mass_support_geometry hN hδ hδhi hb (mem_product.mp ha).1).2.2.2.le
    have hat := gamma5Mass_atoms_bilateral (d := x.1) hfour hg.prime_lower
      (hg.prime_lower.trans (by exact_mod_cast hpq.le))
    have hH := (gamma5Mass_H_bounds
      (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
      (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2)).1.le
    rw [mul_div_assoc, hid i Δ V hb x (hX hx)]
    constructor
    · have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hat.1 hH) hw
      convert h using 1 <;> first | rfl | ring
    · have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hat.2 hH) hw
      convert h using 1 <;> first | rfl | ring
  constructor
  · apply mul_le_mul_of_nonneg_left _ hli
    exact sum_le_sum (fun x hx => (hpoint x hx).1)
  · have hs := sum_le_sum (fun x hx => (hpoint x hx).2)
    rw [← mul_sum] at hs
    have h := mul_le_mul_of_nonneg_left hs hli
    unfold gamma5ClassicalMainMass gamma5MassReciprocalMask
    exact h.trans_eq (mul_left_comm _ _ _)

end Wu2008DoubleSieve
