import MathlibNt.Wu2008DoubleSieve.Gamma5MassLabels

/-!
# Uniform bilateral Gamma5 arithmetic mass on the old Theta scale

The per-product discrepancy is uniform before all source boxes and rectangle
endpoints. It is multiplied by the nonnegative original arithmetic weight,
then summed exactly. No division by the old convolution mass is used.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem gamma5Mass_theta_eq {i : ℕ} (N : ℕ) (Q : ℝ) (W : Fin i → Finset ℕ) :
    boxTheta N Q W = 4 * logarithmicIntegral N *
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * gamma5MassOldWeight N d Q := by
  simp only [boxTheta, gamma5MassOldWeight, mul_div_assoc]

theorem gamma5Mass_theta_nonneg {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN)
  rw [gamma5Mass_theta_eq]
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro d hd
  exact mul_nonneg (Nat.cast_nonneg _) (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.2.le

theorem gamma5Mass_main_rect_identity_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → D ≤ gamma5ClassicalB →
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D) =
      4 * logarithmicIntegral N *
        ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
            gamma5MassOldWeight N d ((N : ℝ) ^ (1 / 2 - δ)) *
            gamma5MassArithmeticPairs N d ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D := by
  filter_upwards [gamma5Mass_label_eventually k hδ hδhi, eventually_ge_atTop (2 : ℕ)]
    with N hlabels hN
  intro i Δ V hb A B C D hA hB hC hD
  unfold gamma5ClassicalMainMass
  rw [gamma5Mass_sum_rect hN hδ hδhi hb hA hB hC hD]
  congr 1
  apply sum_congr rfl
  intro d hd
  rw [gamma5MassArithmeticPairs, mul_sum]
  apply sum_congr rfl
  intro pq hpq
  have hx := (gamma5Mass_rect_mem_iff hN hδ hδhi hb hA hB hC hD (d, pq)).mpr ⟨hd, hpq⟩
  have hxlabels := (mem_filter.mp hx).1
  have hgood := hlabels i Δ V hb (d, pq) hxlabels
  have hbase := gamma5Mass_support_geometry hN hδ hδhi hb hd
  obtain ⟨hpairs, _hpq, _hqu, hpN, hqN⟩ := mem_filter.mp hpq
  obtain ⟨hp, hq⟩ := mem_product.mp hpairs
  have hpc := (gamma5Mass_coordinate_mem_iff hbase.2.2.1 pq.1).mp hp
  have hqc := (gamma5Mass_coordinate_mem_iff hbase.2.2.1 pq.2).mp hq
  have hid := gamma5Mass_two_insertions (by omega : 0 < N) hbase.1
    hpc.1 hqc.1 hgood.1 hgood.2.1 hpN hqN hbase.2.2.1
  have hH := gamma5Mass_H_eq (hpc.2.2.trans hB) (hqc.2.2.trans hD)
  dsimp only [gamma5ClassicalProduct]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc, hid, hH]
  ring

/-- Uniform bilateral mass for every closed rectangle intersected with the
original strict source triangle. Evenness is unnecessary for this mass theorem. -/
theorem gamma5Mass_rectangle_mass (k : ℕ) (_hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → C ≤ D → D ≤ gamma5ClassicalB →
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D) -
        gamma5MassRectangleIntegral A B C D *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hα := (gamma5Classical_exponents_pos k hδ hδhalf).1
  have hβ := wuLocalExponent_pos k hδ hδhalf
  have hαβ : gamma5ClassicalAlpha k δ ≤ wuLocalExponent k δ * gamma5MassA := by
    norm_num [gamma5ClassicalAlpha, gamma5MassA, gamma5ClassicalS]
    linarith
  obtain ⟨T1, hmass⟩ := eventually_atTop.mp
    (gamma5Mass_arithmetic_pair_uniform hα hβ hαβ hε)
  obtain ⟨T2, hid⟩ := eventually_atTop.mp (gamma5Mass_main_rect_identity_eventually k hδ hδhalf)
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hNT i Δ V hb A B C D hA hAB hB hC hCD hD
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNT
  have hN : 2 ≤ N := by omega
  have hT1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hT2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let w := fun d => (convolutionCoeff W d : ℝ) * gamma5MassOldWeight N d Q
  let J := gamma5MassRectangleIntegral A B C D
  let P := fun d => gamma5MassArithmeticPairs N d (Q / d) A B C D
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hd
    exact mul_nonneg (Nat.cast_nonneg _) (gamma5Mass_support_geometry hN hδ hδhalf hb hd).2.2.2.le
  have hp : ∀ d ∈ boxConvolutionSupport W, |P d - J| ≤ ε := by
    intro d hd
    exact (hmass N hT1 (Q / d) (gamma5Mass_support_geometry hN hδ hδhalf hb hd).2.1
      d A B C D hA hAB hB hC hCD hD).le
  have hsum :
      |(∑ d ∈ boxConvolutionSupport W, w d * P d) - J * ∑ d ∈ boxConvolutionSupport W, w d| ≤
        ε * ∑ d ∈ boxConvolutionSupport W, w d := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [show w d * P d - J * w d = w d * (P d - J) by ring,
      abs_mul, abs_of_nonneg (hw d hd)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp d hd) (hw d hd)
  have hli : 0 ≤ 4 * logarithmicIntegral N := by
    have h := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN : (2 : ℝ) ≤ N)
    change 0 ≤ 4 * logarithmicIntegral N
    exact mul_nonneg (by norm_num) h
  rw [hid N hT2 i Δ V hb A B C D hA hB hC hD, gamma5Mass_theta_eq]
  change |4 * logarithmicIntegral N * (∑ d ∈ boxConvolutionSupport W, w d * P d) -
    J * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)
  have hh := mul_le_mul_of_nonneg_left hsum hli
  rw [← abs_of_nonneg hli, ← abs_mul] at hh
  rw [abs_of_nonneg hli] at hh
  calc
    _ = |4 * logarithmicIntegral N *
        ((∑ d ∈ boxConvolutionSupport W, w d * P d) -
          J * ∑ d ∈ boxConvolutionSupport W, w d)| := by
      congr 1
      ring
    _ ≤ 4 * logarithmicIntegral N * (ε * ∑ d ∈ boxConvolutionSupport W, w d) := hh
    _ = _ := mul_left_comm _ _ _

/-- Bilateral full-triangle arithmetic mass at the literal C5 integral. -/
theorem gamma5Mass_full_mass (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) -
        gamma5MassC5 * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, h⟩ := gamma5Mass_rectangle_mass k hk hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  have hh := h N hN i Δ V hb gamma5MassA gamma5ClassicalB gamma5MassA gamma5ClassicalB
    le_rfl gamma5Mass_constants.2.1.le le_rfl le_rfl gamma5Mass_constants.2.1.le le_rfl
  rw [gamma5Mass_full_labels_eq (by omega) hδ (by linarith) hb, gamma5Mass_full_integral_eq] at hh
  exact hh

end Wu2008DoubleSieve
