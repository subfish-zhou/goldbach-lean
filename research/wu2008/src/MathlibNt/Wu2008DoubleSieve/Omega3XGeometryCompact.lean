import MathlibNt.Wu2008DoubleSieve.Omega3XGeometry

/-!
# A fixed compact parameter interval before N

The source parameters `k` and `δ` determine both the positive power and the
compact interval. No universal cap independent of the depth is asserted.
-/

namespace Wu2008DoubleSieve

open Real

/-- Choose the analytic compact domain before N and all actual source labels.
The growth exponent is the existing `wuLocalExponent k δ / 10`, with δ fixed. -/
theorem omega3X_fixed_compact_geometry (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ (u0 : ℝ) (M : ℕ),
      u0 = 1 + 2 * δ / (1 / 2 - δ) ∧
      1 < u0 ∧
      0 < wuLocalExponent k δ / 10 ∧
      1 / (wuLocalExponent k δ / 10) < M ∧
      u0 < M ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        ∀ p ∈ omega3XPrimes N δ s t d,
          let x := omega3XScale N d p.1 p.2.1 p.2.2
          let y := (p.2.1 : ℝ)
          let u := log x / log y
          0 < x ∧ 2 ≤ y ∧ y ≤ x ∧
          (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ y ∧
          (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ x ∧
          x ≤ N ∧
          1 + 4 * δ / (1 / 2 - δ) < u ∧
          u ≤ 1 / (wuLocalExponent k δ / 10) ∧
          u ∈ Set.Icc u0 (M : ℝ) := by
  let u0 : ℝ := 1 + 2 * δ / (1 / 2 - δ)
  obtain ⟨M, hM⟩ := exists_nat_gt (max (1 / (wuLocalExponent k δ / 10)) u0)
  have hcap : 1 / (wuLocalExponent k δ / 10) < (M : ℝ) :=
    (le_max_left _ _).trans_lt hM
  have hu0M : u0 < (M : ℝ) := (le_max_right _ _).trans_lt hM
  have hc : 0 < 1 / 2 - δ := by linarith
  have hu0 : 1 < u0 := by
    have hh : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    dsimp [u0]
    linarith
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  refine ⟨u0, M, rfl, hu0, hη, hcap, hu0M, ?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht p hp
  obtain ⟨hx, hy, hxy, hyg, hxg, hxN, hgap, hu⟩ :=
    omega3X_prime_triple_geometry hN hδ hδhi hb hs hst ht hd hp
  have hlow : u0 ≤ 1 + 4 * δ / (1 / 2 - δ) := by
    dsimp [u0]
    linarith [div_le_div_of_nonneg_right (by linarith : 2 * δ ≤ 4 * δ) hc.le]
  exact ⟨hx, hy, hxy.le, hyg, hxg, hxN, hgap, hu,
    ⟨hlow.trans hgap.le, hu.trans hcap.le⟩⟩

end Wu2008DoubleSieve
