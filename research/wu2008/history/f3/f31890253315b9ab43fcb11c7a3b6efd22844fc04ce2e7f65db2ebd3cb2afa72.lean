import MathlibNt.Wu2008DoubleSieve.Gamma6BaseFinite

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def gamma6BaseZeta (k : ℕ) (δ : ℝ) : ℝ :=
  wuLocalExponent k δ * min gamma5MassA ((1 - gamma6BaseB - gamma6BaseF) / 2)

theorem gamma6Base_zeta_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 < gamma6BaseZeta k δ := by
  have h := wuLocalExponent_pos k hδ hδhi
  norm_num [gamma6BaseZeta, gamma5MassA, gamma5ClassicalS, gamma6BaseB, gamma6BaseF]
  exact h

structure Gamma6BaseGeometry (k N : ℕ) (δ : ℝ) (x : Gamma5ClassicalLabel) : Prop where
  product_pos : 0 < gamma5ClassicalProduct x
  product_le : (gamma5ClassicalProduct x : ℝ) ≤ N
  level_gt_one : 1 < gamma5ClassicalLevel N δ x
  cutoff_gt_one : 1 < gamma5ClassicalCutoff N δ x
  cutoff_le_level : gamma5ClassicalCutoff N δ x ≤ gamma5ClassicalLevel N δ x
  cutoff_lower : (N : ℝ) ^ (gamma6BaseZeta k δ) ≤ gamma5ClassicalCutoff N δ x
  prime_lower : (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (x.2.1 : ℝ)
  prime_order : x.2.1 < x.2.2
  ratio_eq : log (gamma5ClassicalLevel N δ x) / log (gamma5ClassicalCutoff N δ x) = 2
  original_ratio_lower : 14626 / 11125 ≤
    log (gamma5ClassicalLevel N δ x) / log (wuLocalCutoff N δ x.1 gamma5ClassicalS)
  original_ratio_upper : log (gamma5ClassicalLevel N δ x) /
    log (wuLocalCutoff N δ x.1 gamma5ClassicalS) ≤ 12398 / 7275

theorem gamma6Base_label_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) :
    Gamma6BaseGeometry k N δ x := by
  obtain ⟨hd, hp, hq, _hpN, _hqN, hpa, hpb, hqc, hqf⟩ :=
    (gamma6Base_mem_labels_iff hN hδ hδhi hbox x).mp hx
  have hb := gamma5Mass_support_geometry hN hδ hδhi hbox hd
  let R : ℝ := (N : ℝ) ^ (1 / 2 - δ) / x.1
  let L := gamma5ClassicalLevel N δ x
  let z := wuLocalCutoff N δ x.1 gamma5ClassicalS
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ := wuLocalExponent_pos k hδ hδhi
  have hR : 1 < R := hb.2.2.1
  have hR0 : 0 < R := by linarith
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  have hcoord := gamma6Base_pair_coordinates hR hp0 hq0 hpa hpb.le hqc hqf.le
  have hLdef : L = R / ((x.2.1 : ℝ) * x.2.2) := by
    dsimp [L, R, gamma5ClassicalLevel, gamma5ClassicalProduct]
    push_cast
    ring
  have hlog : log L = log R - log (x.2.1 : ℝ) - log (x.2.2 : ℝ) := by
    rw [hLdef, log_div hR0.ne' (mul_pos hp0 hq0).ne', log_mul hp0.ne' hq0.ne']
    ring
  have hpair : R ^ (1 - gamma6BaseB - gamma6BaseF) ≤ L := by
    apply (log_le_log_iff (rpow_pos_of_pos hR0 _)
      (by rw [hLdef]; exact div_pos hR0 (mul_pos hp0 hq0))).mp
    rw [log_rpow hR0, hlog]
    have ht := (div_le_iff₀ (log_pos hR)).mp hcoord.2.1
    have hu := (div_le_iff₀ (log_pos hR)).mp hcoord.2.2.2
    nlinarith
  have hratio : 14626 / 11125 ≤ log L / log z ∧ log L / log z ≤ 12398 / 7275 := by
    change 14626 / 11125 ≤ log L / log (R ^ (1 / gamma5ClassicalS)) ∧
      log L / log (R ^ (1 / gamma5ClassicalS)) ≤ 12398 / 7275
    rw [hLdef, gamma5Classical_ratio_coordinates hR hp0 hq0]
    norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB, gamma6BaseC, gamma6BaseF] at hcoord ⊢
    constructor <;> linarith [hcoord.1, hcoord.2.1, hcoord.2.2.1, hcoord.2.2.2]
  have hL : 1 < L := (one_lt_rpow hR (by norm_num [gamma6BaseB, gamma6BaseF])).trans_le hpair
  have hz : 1 < z := one_lt_rpow hR (by norm_num [gamma5ClassicalS])
  have hbridge := gamma5Classical_ratio2_cutoff_bridge hL hz
    (hratio.2.trans (by norm_num [gamma5ClassicalS]))
  have hM : 0 < gamma5ClassicalProduct x := Nat.mul_pos (Nat.mul_pos hb.1 hp.pos) hq.pos
  have hM0 : (0 : ℝ) < gamma5ClassicalProduct x := by exact_mod_cast hM
  have hMN : (gamma5ClassicalProduct x : ℝ) ≤ N := by
    have hMQ : (gamma5ClassicalProduct x : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
      have hh := (lt_div_iff₀ hM0).mp hL
      linarith
    exact hMQ.trans (by simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hN1.le (show 1 / 2 - δ ≤ 1 by linarith))
  have hpow (e : ℝ) (he : 0 ≤ e) :
      (N : ℝ) ^ (wuLocalExponent k δ * e) ≤ R ^ e := by
    rw [rpow_mul hN0.le]
    exact rpow_le_rpow (rpow_nonneg hN0.le _) hb.2.1 he
  have hprime : (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (x.2.1 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * gamma5MassA) := by
        apply rpow_le_rpow_of_exponent_le hN1.le
        norm_num [gamma5ClassicalAlpha, gamma5ClassicalS, gamma5MassA]
        linarith
      _ ≤ R ^ gamma5MassA := hpow _ (by norm_num [gamma5MassA, gamma5ClassicalS])
      _ ≤ _ := hpa
  have hcut : (N : ℝ) ^ (gamma6BaseZeta k δ) ≤ min z (sqrt L) := by
    apply le_min
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * gamma5MassA) :=
          rpow_le_rpow_of_exponent_le hN1.le (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ.le)
        _ ≤ z := hpow _ (by norm_num [gamma5MassA, gamma5ClassicalS])
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * ((1 - gamma6BaseB - gamma6BaseF) / 2)) :=
          rpow_le_rpow_of_exponent_le hN1.le (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le)
        _ ≤ R ^ ((1 - gamma6BaseB - gamma6BaseF) / 2) :=
          hpow _ (by norm_num [gamma6BaseB, gamma6BaseF])
        _ = sqrt (R ^ (1 - gamma6BaseB - gamma6BaseF)) := by
          rw [sqrt_eq_rpow, ← rpow_mul hR0.le]
          congr 1
          ring
        _ ≤ sqrt L := sqrt_le_sqrt hpair
  refine ⟨hM, hMN, hL, hbridge.1, hbridge.2.1, hcut, hprime, ?_, ?_, hratio.1, hratio.2⟩
  · exact_mod_cast gamma6Base_prime_order hR hpb hqc
  · change log L / log (min z (sqrt L)) = 2
    rw [hbridge.2.2.1, max_eq_right (hratio.2.trans (by norm_num))]

theorem gamma6Base_polynomial_envelope {k N : ℕ} {δ : ℝ} {x : Gamma5ClassicalLabel}
    (hζ : 0 < gamma6BaseZeta k δ) (hg : Gamma6BaseGeometry k N δ x) :
    ((gamma5ClassicalProduct x * N : ℕ) : ℝ) ≤
      gamma5ClassicalCutoff N δ x ^ (2 / gamma6BaseZeta k δ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc
    _ ≤ (N : ℝ) ^ (2 : ℝ) := by
      rw [Nat.cast_mul, rpow_two]
      nlinarith [mul_le_mul_of_nonneg_right hg.product_le hN0]
    _ = ((N : ℝ) ^ gamma6BaseZeta k δ) ^ (2 / gamma6BaseZeta k δ) := by
      rw [← rpow_mul hN0]
      congr 1
      field_simp
    _ ≤ _ := rpow_le_rpow (rpow_nonneg hN0 _) hg.cutoff_lower (by positivity)

end Wu2008DoubleSieve
