import MathlibNt.Wu2008DoubleSieve.Gamma5MassCount
import MathlibNt.Wu2008DoubleSieve.Gamma5MassIntegrability

/-!
# Actual separated Gamma6 labels

The count and arithmetic main mass are the existing Gamma5Classical
functionals on new labels; no source count or arithmetic weight is redefined.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma6BaseB : ℝ := 25 / 89
noncomputable def gamma6BaseC : ℝ := 100 / 291
noncomputable def gamma6BaseF : ℝ := 2 / 5

noncomputable def gamma6BaseLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  (boxConvolutionSupport W ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    (fun x => x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
      wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) ∧
      (x.2.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ∧
      ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseC ≤ (x.2.2 : ℝ) ∧
      (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseF)

noncomputable def gamma6BaseRectLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (A B C D : ℝ) : Finset Gamma5ClassicalLabel :=
  (gamma6BaseLabels N δ W).filter (fun x =>
    A ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ∧
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ≤ B ∧
    C ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ∧
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ≤ D)

theorem gamma6Base_constants :
    1 / 10 ≤ gamma5MassA ∧ gamma5MassA < gamma6BaseB ∧
    gamma6BaseB < gamma6BaseC ∧ gamma6BaseC < gamma6BaseF ∧
    gamma6BaseF ≤ 1 / 2 ∧ 1 / 4 ≤ 1 - gamma6BaseB - gamma6BaseF ∧
    gamma5ClassicalS * (1 - gamma6BaseB - gamma6BaseF) = 14626 / 11125 ∧
    gamma5ClassicalS * (1 - gamma5MassA - gamma6BaseC) = 12398 / 7275 ∧
    1 < gamma5ClassicalS * (1 - gamma6BaseB - gamma6BaseF) ∧
    gamma5ClassicalS * (1 - gamma5MassA - gamma6BaseC) < 2 := by
  norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB, gamma6BaseC, gamma6BaseF]

theorem gamma6Base_prime_order {R p q : ℝ} (hR : 1 < R)
    (hp : p < R ^ gamma6BaseB) (hq : R ^ gamma6BaseC ≤ q) : p < q :=
  hp.trans_le ((rpow_le_rpow_of_exponent_le hR.le gamma6Base_constants.2.2.1.le).trans hq)

theorem gamma6Base_mem_labels_iff {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (x : Gamma5ClassicalLabel) :
    x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) ↔
      x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
      wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) ∧
      (x.2.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ∧
      ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseC ≤ (x.2.2 : ℝ) ∧
      (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseF := by
  constructor
  · intro hx
    exact ⟨(mem_product.mp (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩
  · rintro ⟨hd, hp⟩
    have hg := gamma5Mass_support_geometry hN hδ hδhi hb hd
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hd1 : (1 : ℝ) ≤ x.1 := by exact_mod_cast hg.1
    have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1
        (show 1 / 2 - δ ≤ 1 by linarith)
    have hRN : (N : ℝ) ^ (1 / 2 - δ) / x.1 ≤ N := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < x.1)).mpr
      nlinarith
    have hq : (x.2.2 : ℝ) ≤ N := hp.2.2.2.2.2.2.2.le.trans
      ((by simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hg.2.2.1.le
        (show gamma6BaseF ≤ 1 by norm_num [gamma6BaseF])).trans hRN)
    have hpq := gamma6Base_prime_order hg.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1
    have hpNat : x.2.1 ≤ N := by exact_mod_cast hpq.le.trans hq
    have hqNat : x.2.2 ≤ N := by exact_mod_cast hq
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hd, mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩⟩, hp⟩

theorem gamma6Base_pair_coordinates {R p q : ℝ}
    (hR : 1 < R) (hp0 : 0 < p) (hq0 : 0 < q)
    (hpa : R ^ gamma5MassA ≤ p) (hpb : p ≤ R ^ gamma6BaseB)
    (hqc : R ^ gamma6BaseC ≤ q) (hqf : q ≤ R ^ gamma6BaseF) :
    gamma5MassA ≤ log p / log R ∧ log p / log R ≤ gamma6BaseB ∧
    gamma6BaseC ≤ log q / log R ∧ log q / log R ≤ gamma6BaseF := by
  have hR0 : 0 < R := by linarith
  have ha := log_le_log (rpow_pos_of_pos hR0 _) hpa
  have hb := log_le_log hp0 hpb
  have hc := log_le_log (rpow_pos_of_pos hR0 _) hqc
  have hf := log_le_log hq0 hqf
  rw [log_rpow hR0] at ha hb hc hf
  exact ⟨(le_div_iff₀ (log_pos hR)).mpr ha, (div_le_iff₀ (log_pos hR)).mpr hb,
    (le_div_iff₀ (log_pos hR)).mpr hc, (div_le_iff₀ (log_pos hR)).mpr hf⟩

theorem gamma6Base_count_eq_nat {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (X : Finset Gamma5ClassicalLabel) :
    gamma5ClassicalCount N δ W X =
      ((∑ x ∈ X, convolutionCoeff W x.1 *
        (sourceSieveCarrier N (gamma5ClassicalProduct x) (x.1 * N)
          (wuLocalCutoff N δ x.1 gamma5ClassicalS)).card : ℕ) : ℝ) :=
  gamma5ClassicalCount_eq_nat_count N δ W X

end Wu2008DoubleSieve
