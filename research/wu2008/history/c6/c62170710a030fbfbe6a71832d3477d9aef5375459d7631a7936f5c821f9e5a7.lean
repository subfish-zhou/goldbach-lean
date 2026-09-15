import MathlibNt.Wu2008DoubleSieve.Gamma6BaseLabels

/-!
# Uniform actual Gamma6 arithmetic mass

Exact two-insertion transport retains every old convolution multiplicity and
shared prime factor. The true logarithmic integral is unchanged.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gamma6Base_main_rect_identity_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → B ≤ gamma6BaseB →
      gamma6BaseC ≤ C → D ≤ gamma6BaseF →
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D) =
      4 * logarithmicIntegral N *
        ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
            gamma5MassOldWeight N d ((N : ℝ) ^ (1 / 2 - δ)) *
            gamma6BaseArithmeticPairs N d ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D := by
  filter_upwards [gamma6Base_label_eventually k hδ hδhi, eventually_ge_atTop (2 : ℕ)]
    with N hlabels hN
  intro i Δ V hb A B C D hA hB hC hD
  unfold gamma5ClassicalMainMass
  rw [gamma6Base_sum_rect hN hδ hδhi hb hA hB hC hD]
  congr 1
  apply sum_congr rfl
  intro d hd
  rw [gamma6BaseArithmeticPairs, mul_sum]
  apply sum_congr rfl
  intro pq hpq
  have hx := (gamma6Base_rect_mem_iff hN hδ hδhi hb hA hB hC hD (d, pq)).mpr ⟨hd, hpq⟩
  have hxlabels := (mem_filter.mp hx).1
  have hgood := hlabels i Δ V hb (d, pq) hxlabels
  have hbase := gamma5Mass_support_geometry hN hδ hδhi hb hd
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  have hpN := (mem_filter.mp hp).2
  have hqN := (mem_filter.mp hq).2
  have hpc := (gamma5Mass_coordinate_mem_iff hbase.2.2.1 pq.1).mp
    (mem_filter.mp (mem_filter.mp hp).1).1
  have hqc := (gamma5Mass_coordinate_mem_iff hbase.2.2.1 pq.2).mp
    (mem_filter.mp (mem_filter.mp hq).1).1
  have hid := gamma5Mass_two_insertions (by omega : 0 < N) hbase.1
    hpc.1 hqc.1 hgood.1 hgood.2 hpN hqN hbase.2.2.1
  have hH := gamma6Base_H_eq (hpc.2.2.trans hB) (hqc.2.2.trans hD)
  dsimp only [gamma5ClassicalProduct]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc, hid, hH]
  ring

/-- Threshold before all source boxes and all four closed rectangle sides.
No parity condition is needed for arithmetic mass. -/
theorem gamma6Base_rectangle_mass (k : ℕ) (_hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma6BaseB →
      gamma6BaseC ≤ C → C ≤ D → D ≤ gamma6BaseF →
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D) -
        gamma6BaseIntegral A B C D *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hα := (gamma5Classical_exponents_pos k hδ hδhalf).1
  have hβ := wuLocalExponent_pos k hδ hδhalf
  have hαβ : gamma5ClassicalAlpha k δ ≤ wuLocalExponent k δ * gamma5MassA := by
    norm_num [gamma5ClassicalAlpha, gamma5MassA, gamma5ClassicalS]
    linarith
  obtain ⟨T1, hmass⟩ := eventually_atTop.mp
    (gamma6Base_arithmetic_pair_uniform hα hβ hαβ hε)
  obtain ⟨T2, hid⟩ := eventually_atTop.mp (gamma6Base_main_rect_identity_eventually k hδ hδhalf)
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hNT i Δ V hb A B C D hA hAB hB hC hCD hD
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNT
  have hN : 2 ≤ N := by omega
  have hT1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hT2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let w := fun d => (convolutionCoeff W d : ℝ) * gamma5MassOldWeight N d Q
  let J := gamma6BaseIntegral A B C D
  let P := fun d => gamma6BaseArithmeticPairs N d (Q / d) A B C D
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

theorem gamma6Base_full_mass (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) -
        gamma6BaseC6 * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, h⟩ := gamma6Base_rectangle_mass k hk hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  have hh := h N hN i Δ V hb gamma5MassA gamma6BaseB gamma6BaseC gamma6BaseF
    le_rfl gamma6Base_constants.2.1.le le_rfl le_rfl gamma6Base_constants.2.2.2.1.le le_rfl
  rw [gamma6Base_full_labels_eq (by omega) hδ (by linarith) hb] at hh
  exact hh

end Wu2008DoubleSieve
