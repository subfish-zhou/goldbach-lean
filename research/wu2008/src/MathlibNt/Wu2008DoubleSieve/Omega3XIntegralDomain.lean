import MathlibNt.Wu2008DoubleSieve.Omega3XGeometryCompact

/-!
# Continuous exponent geometry of the X integral

Wu04, arXiv TeX lines 2240–2259. The source squared-prefix inequalities,
not a bound on the square of the supported product, control `R = Q / d`.
The entire closed ordered exponent region is covered, including its boundary.
-/

namespace Wu2008DoubleSieve

open Real

noncomputable def omega3XPhi (N d : ℕ) (δ : ℝ) : ℝ :=
  log ((N : ℝ) / d) / log ((N : ℝ) ^ (1 / 2 - δ) / d)

def omega3XExponentRegion (s t : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 1 / t ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ 1 / s}

/-- The actual supported quotient and source phi occupy fixed logarithmic ranges. -/
theorem omega3XPhi_source_bounds {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (N : ℝ) ^ (wuLocalExponent k δ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d ∧
    1 < (N : ℝ) ^ (1 / 2 - δ) / d ∧
    2 + 2 * δ / (1 / 2 - δ) ≤ omega3XPhi N d δ ∧
    omega3XPhi N d δ ≤ 1 / wuLocalExponent k δ := by
  obtain ⟨hd0, _, hR⟩ := wuLocal_support_bounds (show 1 ≤ N by omega) hδ hδhi
    hb.2.2.2.2.1 ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hdpos : (0 : ℝ) < d := by linarith
  have hη := wuLocalExponent_pos k hδ hδhi
  have hc : 0 < 1 / 2 - δ := by linarith
  have hR1 := (one_lt_rpow hN1 hη).trans_le hR
  have hL : 0 < log ((N : ℝ) ^ (1 / 2 - δ) / d) := log_pos hR1
  have hlogR :
      log ((N : ℝ) ^ (1 / 2 - δ) / d) =
        (1 / 2 - δ) * log N - log d := by
    rw [log_div (rpow_pos_of_pos hN0 _).ne' hdpos.ne', log_rpow hN0]
  have hlogNd : log ((N : ℝ) / d) = log N - log d :=
    log_div hN0.ne' hdpos.ne'
  have hlogd : 0 ≤ log (d : ℝ) := log_nonneg hd1
  have hloglower := log_le_log (rpow_pos_of_pos hN0 _) hR
  rw [log_rpow hN0] at hloglower
  refine ⟨hR, hR1, ?_, ?_⟩
  · have heq : 2 + 2 * δ / (1 / 2 - δ) = 1 / (1 / 2 - δ) := by
      apply (eq_div_iff hc.ne').mpr
      rw [add_mul, div_mul_cancel₀ _ hc.ne']
      ring
    rw [heq, omega3XPhi, le_div_iff₀ hL, one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ hc).mpr
    rw [hlogR, hlogNd]
    nlinarith
  · rw [omega3XPhi, div_le_iff₀ hL, one_div, ← div_eq_inv_mul]
    apply (le_div_iff₀ hη).mpr
    rw [hlogNd]
    nlinarith

/-- All coordinates in the closed source region lie in `[1/10,1/2]`. -/
theorem omega3XExponentRegion_bounds {s t : ℝ} {p : ℝ × ℝ × ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hp : p ∈ omega3XExponentRegion s t) :
    p.1 ∈ Set.Icc (1 / 10) (1 / 2) ∧
    p.2.1 ∈ Set.Icc (1 / 10) (1 / 2) ∧
    p.2.2 ∈ Set.Icc (1 / 10) (1 / 2) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hlo := one_div_le_one_div_of_le ht0 ht
  have hhi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  obtain ⟨ha, hab, hbc, hc⟩ := hp
  exact ⟨⟨hlo.trans ha, (hab.trans (hbc.trans hc)).trans hhi⟩,
    ⟨(hlo.trans ha).trans hab, (hbc.trans hc).trans hhi⟩,
    ⟨((hlo.trans ha).trans hab).trans hbc, hc.trans hhi⟩⟩

/-- At phi=2 the closed boundary may have Buchstab argument exactly one. -/
theorem omega3X_argument_bounds {φ a b c : ℝ}
    (hφ : 2 ≤ φ) (ha : a ∈ Set.Icc (1 / 10) (1 / 2))
    (hb : b ∈ Set.Icc (1 / 10) (1 / 2))
    (hc : c ∈ Set.Icc (1 / 10) (1 / 2)) :
    2 * φ - 3 ≤ (φ - a - b - c) / b ∧
    (φ - a - b - c) / b ≤ 10 * φ ∧
    1 ≤ (φ - a - b - c) / b := by
  have hb0 : 0 < b := by linarith [hb.1]
  have hlo : 2 * φ - 3 ≤ (φ - a - b - c) / b := by
    apply (le_div_iff₀ hb0).mpr
    nlinarith [ha.2, hb.2, hc.2]
  refine ⟨hlo, ?_, by linarith⟩
  apply (div_le_iff₀ hb0).mpr
  nlinarith [ha.1, hb.1, hc.1]


end Wu2008DoubleSieve
