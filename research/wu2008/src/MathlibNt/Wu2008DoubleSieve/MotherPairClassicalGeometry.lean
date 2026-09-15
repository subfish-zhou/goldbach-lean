import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairData
import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalGeometry

/-! Variable-cap classical geometry. The same original local level is used
throughout; the minimum cutoff has ratio in the closed interval [2,3],
including when the unmodified ratio is below one. -/
namespace Wu2008DoubleSieve.MotherPair
open Finset Real Filter
open scoped Classical Topology

noncomputable def classicalAlpha (S : ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  wuLocalExponent k δ / (2 * S)

noncomputable def classicalZeta (S U : ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  wuLocalExponent k δ * min (1 / S) ((1 - 2 * U) / 2)

noncomputable def classicalCutoff (S : ℝ) (N : ℕ) (δ : ℝ)
    (x : Gamma5ClassicalLabel) : ℝ :=
  min (wuLocalCutoff N δ x.1 S)
    (sqrt (gamma5ClassicalLevel N δ x))

theorem classical_exponents_pos {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 < classicalAlpha S k δ ∧ 0 < classicalZeta S U k δ := by
  have h := wuLocalExponent_pos k hδ hδhi
  have hS : 0 < S := by linarith [hcap.three_le_S]
  have hU : 0 < (1 - 2 * U) / 2 := by linarith [hcap.cap_lt_half]
  exact ⟨div_pos h (mul_pos (by norm_num) hS),
    mul_pos h (lt_min (one_div_pos.mpr hS) hU)⟩

theorem classical_pair_geometry {S U R p q : ℝ} (hcap : CapAdmissible S U)
    (hR : 1 < R) (hp0 : 0 < p) (hq0 : 0 < q)
    (hp : R ^ (1 / S) ≤ p) (hpq : p ≤ q)
    (hq : q ≤ R ^ U) :
    R ^ (1 - 2 * U) ≤ R / (p * q) ∧
      S * (1 - 2 * U) ≤
        log (R / (p * q)) / log (R ^ (1 / S)) ∧
      log (R / (p * q)) / log (R ^ (1 / S)) ≤
        S - 2 := by
  have hS : 0 < S := by linarith [hcap.three_le_S]
  have hR0 : 0 < R := by linarith
  have hlR : 0 < log R := log_pos hR
  have hlp := log_le_log (rpow_pos_of_pos hR0 _) hp
  have hlq := log_le_log hq0 hq
  have hlpq := log_le_log hp0 hpq
  rw [log_rpow hR0] at hlp hlq
  have he : log (R / (p * q)) = log R - log p - log q := by
    rw [log_div hR0.ne' (mul_pos hp0 hq0).ne', log_mul hp0.ne' hq0.ne']
    ring
  have hlz : 0 < log (R ^ (1 / S)) := by
    rw [log_rpow hR0]
    positivity
  constructor
  · apply (log_le_log_iff (rpow_pos_of_pos hR0 _) (div_pos hR0 (mul_pos hp0 hq0))).mp
    rw [log_rpow hR0, he]
    nlinarith
  constructor
  · apply (le_div_iff₀ hlz).mpr
    rw [he, log_rpow hR0]
    field_simp
    nlinarith
  · apply (div_le_iff₀ hlz).mpr
    rw [he, log_rpow hR0]
    have hinv : S * (1 / S) = 1 := mul_one_div_cancel hS.ne'
    nlinarith

theorem classical_ratio2_cutoff_bridge {L z : ℝ}
    (hL : 1 < L) (hz : 1 < z)
    (hv : log L / log z ≤ 3) :
    1 < min z (sqrt L) ∧ min z (sqrt L) ≤ L ∧
      log L / log (min z (sqrt L)) = max (log L / log z) 2 ∧
      2 ≤ log L / log (min z (sqrt L)) ∧
      log L / log (min z (sqrt L)) ≤ 3 := by
  have hL0 : 0 < L := by linarith
  have hlL : 0 < log L := log_pos hL
  have hlz : 0 < log z := log_pos hz
  have hsqrt : 1 < sqrt L := by
    rw [sqrt_eq_rpow]
    exact one_lt_rpow hL (by norm_num)
  have hsqrtL : sqrt L ≤ L := by
    rw [sqrt_eq_rpow]
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hL.le (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hlogsqrt : log (sqrt L) = log L / 2 := by
    rw [sqrt_eq_rpow, log_rpow hL0]
    ring
  have hratio : log L / log (sqrt L) = 2 := by
    rw [hlogsqrt]
    field_simp
  have heq : log L / log (min z (sqrt L)) = max (log L / log z) 2 := by
    by_cases h : z ≤ sqrt L
    · rw [min_eq_left h, max_eq_left]
      apply (le_div_iff₀ hlz).mpr
      have hh := log_le_log (by linarith : 0 < z) h
      rw [hlogsqrt] at hh
      linarith
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h', hratio, max_eq_right]
      apply (div_le_iff₀ hlz).mpr
      have hh := log_le_log (by linarith : 0 < sqrt L) h'
      rw [hlogsqrt] at hh
      linarith
  refine ⟨lt_min hz hsqrt, (min_le_right _ _).trans hsqrtL, heq, ?_, ?_⟩
  · rw [heq]
    exact le_max_right _ _
  · rw [heq]
    exact max_le hv (by norm_num)

structure ClassicalGeometry (S U : ℝ) (k N : ℕ) (δ : ℝ) (x : Gamma5ClassicalLabel) : Prop where
  product_pos : 0 < gamma5ClassicalProduct x
  product_le : (gamma5ClassicalProduct x : ℝ) ≤ N
  level_gt_one : 1 < gamma5ClassicalLevel N δ x
  cutoff_gt_one : 1 < classicalCutoff S N δ x
  cutoff_le_level : classicalCutoff S N δ x ≤ gamma5ClassicalLevel N δ x
  cutoff_lower : (N : ℝ) ^ (classicalZeta S U k δ) ≤ classicalCutoff S N δ x
  prime_lower : (N : ℝ) ^ (classicalAlpha S k δ) ≤ (x.2.1 : ℝ)
  ratio_eq : log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x) =
    max (log (gamma5ClassicalLevel N δ x) /
      log (wuLocalCutoff N δ x.1 S)) 2
  ratio_lower : 2 ≤ log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x)
  ratio_upper : log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x) ≤ 3
  original_ratio_lower : S * (1 - 2 * U) ≤
    log (gamma5ClassicalLevel N δ x) / log (wuLocalCutoff N δ x.1 S)
  original_ratio_upper : log (gamma5ClassicalLevel N δ x) /
    log (wuLocalCutoff N δ x.1 S) ≤ S - 2

theorem classical_ratio_mul_log {S U : ℝ} {k N : ℕ} {δ : ℝ}
    {x : Gamma5ClassicalLabel} (hg : ClassicalGeometry S U k N δ x) :
    (log (gamma5ClassicalLevel N δ x) / log (classicalCutoff S N δ x)) *
      log (classicalCutoff S N δ x) = log (gamma5ClassicalLevel N δ x) :=
  div_mul_cancel₀ _ (log_pos hg.cutoff_gt_one).ne'

theorem classical_label_geometry {S U : ℝ} (hcap : CapAdmissible S U) {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ capLabels S U N δ (convolutionWuWindows N Δ V)) :
    ClassicalGeometry S U k N δ x := by
  have hS : 0 < S := by linarith [hcap.three_le_S]
  have hU : 0 < 1 - 2 * U := by linarith [hcap.cap_lt_half]
  obtain ⟨hxambient, hp, hq, _hpN, _hqN, hzp, hpq, hqu⟩ := mem_filter.mp hx
  have hd := (mem_product.mp hxambient).1
  have hb := wuLocal_support_bounds (by omega) hδ hδhi hbox.2.2.2.2.1
    ((boxSquaredPrefixes_iff _ _).mp hbox.2.2.2.2.2) hd
  let R : ℝ := (N : ℝ) ^ (1 / 2 - δ) / x.1
  let L : ℝ := gamma5ClassicalLevel N δ x
  let z : ℝ := wuLocalCutoff N δ x.1 S
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ := wuLocalExponent_pos k hδ hδhi
  have hR : 1 < R := (one_lt_rpow hN1 hβ).trans_le hb.2.2
  have hR0 : 0 < R := by linarith
  have hd0 : (0 : ℝ) < x.1 := by exact_mod_cast hb.1
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  have hpq' : (x.2.1 : ℝ) ≤ x.2.2 := by exact_mod_cast hpq.le
  have hLdef : L = R / ((x.2.1 : ℝ) * x.2.2) := by
    dsimp [L, R, gamma5ClassicalLevel, gamma5ClassicalProduct]
    push_cast
    ring
  have hpair := classical_pair_geometry hcap hR hp0 hq0 hzp hpq' hqu.le
  rw [← hLdef] at hpair
  have hL : 1 < L := (one_lt_rpow hR (by positivity)).trans_le hpair.1
  have hz : 1 < z := one_lt_rpow hR (by positivity)
  have hbridge := classical_ratio2_cutoff_bridge hL hz (hpair.2.2.trans (by linarith [hcap.S_le_five]))
  have hM : 0 < gamma5ClassicalProduct x := Nat.mul_pos (Nat.mul_pos hb.1 hp.pos) hq.pos
  have hM0 : (0 : ℝ) < gamma5ClassicalProduct x := by exact_mod_cast hM
  have hMN : (gamma5ClassicalProduct x : ℝ) ≤ N := by
    have hMQ : (gamma5ClassicalProduct x : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
      have hh := (lt_div_iff₀ hM0).mp hL
      linarith
    exact hMQ.trans (by
      simpa only [rpow_one] using
        rpow_le_rpow_of_exponent_le hN1.le (show 1 / 2 - δ ≤ 1 by linarith))
  have hpow (e : ℝ) (he : 0 ≤ e) :
      (N : ℝ) ^ (wuLocalExponent k δ * e) ≤ R ^ e := by
    rw [rpow_mul hN0.le]
    exact rpow_le_rpow (rpow_nonneg hN0.le _) hb.2.2 he
  have hprime : (N : ℝ) ^ (classicalAlpha S k δ) ≤ (x.2.1 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * (1 / S)) := by
        apply rpow_le_rpow_of_exponent_le hN1.le
        unfold classicalAlpha
        apply (div_le_iff₀ (mul_pos (by norm_num) hS)).mpr
        have he : wuLocalExponent k δ * (1 / S) * (2 * S) =
            2 * wuLocalExponent k δ := by field_simp
        rw [he]
        linarith
      _ ≤ R ^ (1 / S) := hpow _ (by positivity)
      _ ≤ _ := hzp
  have hcut : (N : ℝ) ^ (classicalZeta S U k δ) ≤ min z (sqrt L) := by
    apply le_min
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * (1 / S)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ.le)
        _ ≤ z := hpow _ (by positivity)
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * ((1 - 2 * U) / 2)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le)
        _ ≤ R ^ ((1 - 2 * U) / 2) :=
          hpow _ (by positivity)
        _ = sqrt (R ^ (1 - 2 * U)) := by
          rw [sqrt_eq_rpow, ← rpow_mul hR0.le]
          congr 1
          ring
        _ ≤ sqrt L := sqrt_le_sqrt hpair.1
  exact ⟨hM, hMN, hL, hbridge.1, hbridge.2.1, hcut, hprime,
    hbridge.2.2.1, hbridge.2.2.2.1, hbridge.2.2.2.2, hpair.2.1, hpair.2.2⟩

/-- The moving even integer has a fixed polynomial envelope in the lowered
cutoff, without requiring the enlarged product to form a source box. -/
theorem classical_polynomial_envelope {S U : ℝ} {k N : ℕ} {δ : ℝ}
    {x : Gamma5ClassicalLabel}
    (hζ : 0 < classicalZeta S U k δ) (hg : ClassicalGeometry S U k N δ x) :
    ((gamma5ClassicalProduct x * N : ℕ) : ℝ) ≤
      classicalCutoff S N δ x ^ (2 / classicalZeta S U k δ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc
    _ ≤ (N : ℝ) ^ (2 : ℝ) := by
      rw [Nat.cast_mul, rpow_two]
      nlinarith [mul_le_mul_of_nonneg_right hg.product_le hN0]
    _ = ((N : ℝ) ^ (classicalZeta S U k δ)) ^ (2 / classicalZeta S U k δ) := by
      rw [← rpow_mul hN0]
      congr 1
      field_simp
    _ ≤ _ := rpow_le_rpow (rpow_nonneg hN0 _) hg.cutoff_lower (by positivity)

end Wu2008DoubleSieve.MotherPair
