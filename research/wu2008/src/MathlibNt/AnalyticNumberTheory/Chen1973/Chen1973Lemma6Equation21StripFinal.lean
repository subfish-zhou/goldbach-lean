import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21HorizontalDecay
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21LogDerivativeFinal

noncomputable section
open Filter Complex
open scoped Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Any fixed logarithmic growth degree is paid by the source smoothing order. -/
theorem chen1973Lemma6_eq21_order_eventually (r : ℕ) :
    ∀ᶠ x : ℕ in atTop, r + 1 ≤ chen1973PerronOrder (x : ℝ) + 1 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (r : ℝ)] with x hx
  have hfloor : r ≤ ⌊Real.log (x : ℝ)⌋₊ := Nat.le_floor hx
  simpa only [chen1973PerronOrder] using Nat.add_le_add_right hfloor 1

/-- Conditional source-level equation (21), with all integral payments internal.
The pointwise quantitative hypothesis is on the entire source strip, which is
stronger than a left-line bound. Neither it nor full-height zero-freeness is
asserted unconditionally by this theorem. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_strip_logDerivative
    {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (r : ℕ) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ s : ℂ,
          chen1973Lemma6Eq21Sigma x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x →
          ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤
            M * (1 + Real.log ((d : ℝ) * (1 + |s.im|))) ^ r) →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₁, hfinal⟩ :=
    chen1973Lemma6_equation21_levelZero_eventually_of_logDerivative_and_horizontal hM hc r
  obtain ⟨x₂, horder⟩ := Filter.eventually_atTop.mp (chen1973Lemma6_eq21_order_eventually r)
  refine ⟨max x₁ x₂, ?_⟩
  intro x hx L B k m l₂ P hzero H
  apply hfinal x ((le_max_left _ _).trans hx) L B k m l₂ P hzero
  · intro d hd χ t
    have hsa := chen1973Lemma6_eq21_sigma_le_alpha P.hx
    have h := H d hd χ (chen1973Lemma6Eq21Line x t) (by
      simpa [chen1973Lemma6Eq21Line] using
        And.intro (le_refl (chen1973Lemma6Eq21Sigma x)) hsa)
    simpa only [chen1973Lemma6Eq21Line, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using h
  · intro d hd χ pp hpp
    have hregion := chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp
    have hy := (chen1973Lemma6_eq21_primeRegion_log_y P.hx hregion).1
    exact chen1973Lemma6_eq21_horizontal_decay_of_strip_logDerivative
      P.hx (chen1973Lemma6_eq21_one_lt_conductor hd) χ hy hM r
      (horder x ((le_max_right _ _).trans hx)) (H d hd χ)

end AnalyticNumberTheory.LargeSieve
