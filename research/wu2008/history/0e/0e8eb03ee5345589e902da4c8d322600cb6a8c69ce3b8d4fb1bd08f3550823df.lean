import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalFinite

/-!
# Gamma5: positive local levels and the minimum-cutoff bridge

The original ratio can be below `3/2`. Taking the minimum with the square
root of the same local level gives ratio `max v 2`, without changing that
level or its logarithm.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def gamma5ClassicalAlpha (k : ℕ) (δ : ℝ) : ℝ :=
  wuLocalExponent k δ / (2 * gamma5ClassicalS)

noncomputable def gamma5ClassicalZeta (k : ℕ) (δ : ℝ) : ℝ :=
  wuLocalExponent k δ * min (1 / gamma5ClassicalS) ((1 - 2 * gamma5ClassicalB) / 2)

noncomputable def gamma5ClassicalLevel (N : ℕ) (δ : ℝ)
    (x : Gamma5ClassicalLabel) : ℝ :=
  (N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x

noncomputable def gamma5ClassicalCutoff (N : ℕ) (δ : ℝ)
    (x : Gamma5ClassicalLabel) : ℝ :=
  min (wuLocalCutoff N δ x.1 gamma5ClassicalS)
    (sqrt (gamma5ClassicalLevel N δ x))

theorem gamma5Classical_exponents_pos (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 < gamma5ClassicalAlpha k δ ∧ 0 < gamma5ClassicalZeta k δ := by
  have h := wuLocalExponent_pos k hδ hδhi
  norm_num [gamma5ClassicalAlpha, gamma5ClassicalZeta,
    gamma5ClassicalS, gamma5ClassicalB]
  exact h

theorem gamma5Classical_pair_geometry {R p q : ℝ}
    (hR : 1 < R) (hp0 : 0 < p) (hq0 : 0 < q)
    (hp : R ^ (1 / gamma5ClassicalS) ≤ p) (hpq : p ≤ q)
    (hq : q ≤ R ^ gamma5ClassicalB) :
    R ^ (1 - 2 * gamma5ClassicalB) ≤ R / (p * q) ∧
      gamma5ClassicalS * (1 - 2 * gamma5ClassicalB) ≤
        log (R / (p * q)) / log (R ^ (1 / gamma5ClassicalS)) ∧
      log (R / (p * q)) / log (R ^ (1 / gamma5ClassicalS)) ≤
        gamma5ClassicalS - 2 := by
  have hR0 : 0 < R := by linarith
  have hlR : 0 < log R := log_pos hR
  have hlp := log_le_log (rpow_pos_of_pos hR0 _) hp
  have hlq := log_le_log hq0 hq
  have hlpq := log_le_log hp0 hpq
  rw [log_rpow hR0] at hlp hlq
  have he : log (R / (p * q)) = log R - log p - log q := by
    rw [log_div hR0.ne' (mul_pos hp0 hq0).ne', log_mul hp0.ne' hq0.ne']
    ring
  have hlz : 0 < log (R ^ (1 / gamma5ClassicalS)) := by
    rw [log_rpow hR0]
    unfold gamma5ClassicalS
    positivity
  constructor
  · apply (log_le_log_iff (rpow_pos_of_pos hR0 _) (div_pos hR0 (mul_pos hp0 hq0))).mp
    rw [log_rpow hR0, he]
    nlinarith
  constructor
  · apply (le_div_iff₀ hlz).mpr
    rw [he, log_rpow hR0]
    norm_num [gamma5ClassicalS, gamma5ClassicalB] at *
    linarith
  · apply (div_le_iff₀ hlz).mpr
    rw [he, log_rpow hR0]
    norm_num [gamma5ClassicalS, gamma5ClassicalB] at *
    linarith

theorem gamma5Classical_ratio2_cutoff_bridge {L z : ℝ}
    (hL : 1 < L) (hz : 1 < z)
    (hv : log L / log z ≤ gamma5ClassicalS - 2) :
    1 < min z (sqrt L) ∧ min z (sqrt L) ≤ L ∧
      log L / log (min z (sqrt L)) = max (log L / log z) 2 ∧
      2 ≤ log L / log (min z (sqrt L)) ∧
      log L / log (min z (sqrt L)) ≤ gamma5ClassicalS - 2 := by
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
    exact max_le hv (by norm_num [gamma5ClassicalS])

structure Gamma5ClassicalGeometry (k N : ℕ) (δ : ℝ) (x : Gamma5ClassicalLabel) : Prop where
  product_pos : 0 < gamma5ClassicalProduct x
  product_le : (gamma5ClassicalProduct x : ℝ) ≤ N
  level_gt_one : 1 < gamma5ClassicalLevel N δ x
  cutoff_gt_one : 1 < gamma5ClassicalCutoff N δ x
  cutoff_le_level : gamma5ClassicalCutoff N δ x ≤ gamma5ClassicalLevel N δ x
  cutoff_lower : (N : ℝ) ^ (gamma5ClassicalZeta k δ) ≤ gamma5ClassicalCutoff N δ x
  prime_lower : (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (x.2.1 : ℝ)
  ratio_eq : log (gamma5ClassicalLevel N δ x) / log (gamma5ClassicalCutoff N δ x) =
    max (log (gamma5ClassicalLevel N δ x) /
      log (wuLocalCutoff N δ x.1 gamma5ClassicalS)) 2
  ratio_lower : 2 ≤ log (gamma5ClassicalLevel N δ x) / log (gamma5ClassicalCutoff N δ x)
  ratio_upper : log (gamma5ClassicalLevel N δ x) / log (gamma5ClassicalCutoff N δ x) ≤
    gamma5ClassicalS - 2
  original_ratio_lower : gamma5ClassicalS * (1 - 2 * gamma5ClassicalB) ≤
    log (gamma5ClassicalLevel N δ x) / log (wuLocalCutoff N δ x.1 gamma5ClassicalS)
  original_ratio_upper : log (gamma5ClassicalLevel N δ x) /
    log (wuLocalCutoff N δ x.1 gamma5ClassicalS) ≤ gamma5ClassicalS - 2

theorem gamma5Classical_label_geometry {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) :
    Gamma5ClassicalGeometry k N δ x := by
  obtain ⟨hxambient, hp, hq, _hpN, _hqN, hzp, hpq, hqu⟩ := mem_filter.mp hx
  have hd := (mem_product.mp hxambient).1
  have hb := wuLocal_support_bounds (by omega) hδ hδhi hbox.2.2.2.2.1
    ((boxSquaredPrefixes_iff _ _).mp hbox.2.2.2.2.2) hd
  let R : ℝ := (N : ℝ) ^ (1 / 2 - δ) / x.1
  let L : ℝ := gamma5ClassicalLevel N δ x
  let z : ℝ := wuLocalCutoff N δ x.1 gamma5ClassicalS
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
  have hpair := gamma5Classical_pair_geometry hR hp0 hq0 hzp hpq' hqu.le
  rw [← hLdef] at hpair
  have hL : 1 < L := (one_lt_rpow hR (by norm_num [gamma5ClassicalB])).trans_le hpair.1
  have hz : 1 < z := one_lt_rpow hR (by norm_num [gamma5ClassicalS])
  have hbridge := gamma5Classical_ratio2_cutoff_bridge hL hz hpair.2.2
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
  have hprime : (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (x.2.1 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * (1 / gamma5ClassicalS)) := by
        apply rpow_le_rpow_of_exponent_le hN1.le
        norm_num [gamma5ClassicalAlpha, gamma5ClassicalS]
        linarith
      _ ≤ R ^ (1 / gamma5ClassicalS) := hpow _ (by norm_num [gamma5ClassicalS])
      _ ≤ _ := hzp
  have hcut : (N : ℝ) ^ (gamma5ClassicalZeta k δ) ≤ min z (sqrt L) := by
    apply le_min
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * (1 / gamma5ClassicalS)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ.le)
        _ ≤ z := hpow _ (by norm_num [gamma5ClassicalS])
    · calc
        _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * ((1 - 2 * gamma5ClassicalB) / 2)) :=
          rpow_le_rpow_of_exponent_le hN1.le
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le)
        _ ≤ R ^ ((1 - 2 * gamma5ClassicalB) / 2) :=
          hpow _ (by norm_num [gamma5ClassicalB])
        _ = sqrt (R ^ (1 - 2 * gamma5ClassicalB)) := by
          rw [sqrt_eq_rpow, ← rpow_mul hR0.le]
          congr 1
          ring
        _ ≤ sqrt L := sqrt_le_sqrt hpair.1
  exact ⟨hM, hMN, hL, hbridge.1, hbridge.2.1, hcut, hprime,
    hbridge.2.2.1, hbridge.2.2.2.1, hbridge.2.2.2.2, hpair.2.1, hpair.2.2⟩

/-- The moving even integer has a fixed polynomial envelope in the lowered
cutoff, without requiring the enlarged product to form a source box. -/
theorem gamma5Classical_polynomial_envelope {k N : ℕ} {δ : ℝ}
    {x : Gamma5ClassicalLabel}
    (hζ : 0 < gamma5ClassicalZeta k δ) (hg : Gamma5ClassicalGeometry k N δ x) :
    ((gamma5ClassicalProduct x * N : ℕ) : ℝ) ≤
      gamma5ClassicalCutoff N δ x ^ (2 / gamma5ClassicalZeta k δ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc
    _ ≤ (N : ℝ) ^ (2 : ℝ) := by
      rw [Nat.cast_mul, rpow_two]
      nlinarith [mul_le_mul_of_nonneg_right hg.product_le hN0]
    _ = ((N : ℝ) ^ (gamma5ClassicalZeta k δ)) ^ (2 / gamma5ClassicalZeta k δ) := by
      rw [← rpow_mul hN0]
      congr 1
      field_simp
    _ ≤ _ := rpow_le_rpow (rpow_nonneg hN0 _) hg.cutoff_lower (by positivity)

/-- The finite ambient ranges exclude no actual prime labels. In fact this
already holds at `N >= 2`, hence in particular at the final threshold. -/
theorem gamma5Classical_mem_labels_iff {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) (x : Gamma5ClassicalLabel) :
    x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) ↔
      x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
      wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) ∧ x.2.1 < x.2.2 ∧
      (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma5ClassicalB := by
  constructor
  · intro hx
    obtain ⟨ha, hp⟩ := mem_filter.mp hx
    exact ⟨(mem_product.mp ha).1, hp⟩
  · rintro ⟨hd, hp⟩
    have hb := wuLocal_support_bounds (by omega) hδ hδhi hbox.2.2.2.2.1
      ((boxSquaredPrefixes_iff _ _).mp hbox.2.2.2.2.2) hd
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / x.1 :=
      (one_lt_rpow hN1 (wuLocalExponent_pos k hδ hδhi)).trans_le hb.2.2
    have hd1 : (1 : ℝ) ≤ x.1 := by exact_mod_cast hb.1
    have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
      simpa only [rpow_one] using
        rpow_le_rpow_of_exponent_le hN1.le (show 1 / 2 - δ ≤ 1 by linarith)
    have hRN : (N : ℝ) ^ (1 / 2 - δ) / x.1 ≤ N := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < x.1)).mpr
      nlinarith
    have hqN : (x.2.2 : ℝ) ≤ N := by
      apply hp.2.2.2.2.2.2.le.trans
      apply le_trans _ hRN
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hR.le
        (show gamma5ClassicalB ≤ 1 by norm_num [gamma5ClassicalB])
    have hqNat : x.2.2 ≤ N := by exact_mod_cast hqN
    have hpNat : x.2.1 ≤ N := hp.2.2.2.2.2.1.le.trans hqNat
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hd, mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩⟩, hp⟩

end Wu2008DoubleSieve
