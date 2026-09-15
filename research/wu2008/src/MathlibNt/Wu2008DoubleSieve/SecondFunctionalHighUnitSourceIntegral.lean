import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceWeighted
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitBoxedSigma

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open HighUnit

/-- The existing original unit source, evaluated at the actual local level. -/
noncomputable def unit20 {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (a0 a1 a2 a3 b : ℕ → ℝ) : ℝ :=
  let R := fun d : ℕ => (N : ℝ) ^ (1 / 2 - δ) / d
  FourPrimeUnit.source N W (fun d => R d ^ a0 d) (fun d => R d ^ a1 d)
    (fun d => R d ^ a2 d) (fun d => R d ^ a3 d) (fun d => R d ^ b d) word20

noncomputable def unit21 {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (a0 a1 a2 a3 b : ℕ → ℝ) : ℝ :=
  let R := fun d : ℕ => (N : ℝ) ^ (1 / 2 - δ) / d
  FourPrimeUnit.source N W (fun d => R d ^ a0 d) (fun d => R d ^ a1 d)
    (fun d => R d ^ a2 d) (fun d => R d ^ a3 d) (fun d => R d ^ b d) word21

/-- Actual source-box geometry supplies every premise of the finite source inclusion. -/
theorem source_pair_le_boxed {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (a0 a1 a2 a3 b : ℕ → ℝ)
    (hw : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) :
    let W := convolutionWuWindows N Δ V
    unit20 N δ W a0 a1 a2 a3 b ≤ boxedSigma20 N δ W a2 a3 b ∧
    unit21 N δ W a0 a1 a2 a3 b ≤ boxedSigma21 N δ W a3 b := by
  have hdpos : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 < d :=
    fun _ hd => boxConvolutionSupport_pos
      (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  have hR : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    fun _ hd => (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  constructor
  · simpa only [unit20, boxedSigma20, boxed20] using
      (source_le20 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b := b)
        hdpos hR (fun d hd => (hw d hd).1) (fun d hd => (hw d hd).2.2))
  · simpa only [unit21, boxedSigma21, boxed21] using
      (source_le21 (N := N) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b := b)
        hdpos hR (fun d hd => (hw d hd).2.1) (fun d hd => (hw d hd).2.2))

/-- Original unit sources reach the actual J main sums on one source-family threshold.
The comparison is one-sided; the error is on N/log N reciprocal mass, not Theta. -/
theorem source_pair_integral (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ a0 a1 a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        1/10 ≤ a2 d ∧ 1/10 ≤ a3 d ∧ b d ≤ 1/2) →
      let W := convolutionWuWindows N Δ V
      (unit20 N δ W a0 a1 a2 a3 b ≤ boxedIntegral20 N δ W a2 a3 b +
        (epsilon / 2) * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) ∧
      (unit21 N δ W a0 a1 a2 a3 b ≤ boxedIntegral21 N δ W a3 b +
        (epsilon / 2) * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) ∧
      (unit20 N δ W a0 a1 a2 a3 b + unit21 N δ W a0 a1 a2 a3 b ≤
        boxedIntegral20 N δ W a2 a3 b + boxedIntegral21 N δ W a3 b +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W) := by
  obtain ⟨T, hT4, hT⟩ := boxed_sigma_pair_combined k hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb a0 a1 a2 a3 b hw
  obtain ⟨hs20, hs21⟩ := source_pair_le_boxed (by omega) hδ hδhi hb a0 a1 a2 a3 b hw
  obtain ⟨h20, h21, hsum⟩ := hT N hN i Δ V hb a2 a3 b hw
  dsimp only at hs20 hs21 h20 h21 hsum ⊢
  have he20 := (le_abs_self _).trans h20
  have he21 := (le_abs_self _).trans h21
  have hesum := (le_abs_self _).trans hsum
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The actual five-parameter mother hypotheses supply the analytic outer bounds. -/
theorem parameter_outer_bounds {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    1/10 ≤ 1/p.kappa2 ∧ 1/10 ≤ 1/p.kappa3 ∧ 1/p.s ≤ 1/2 := by
  have hk3 : 0 < p.kappa3 := by linarith [hp.s_le_kappa3]
  have hk2 : 0 < p.kappa2 := hk3.trans hp.kappa3_lt_kappa2
  have h2 : p.kappa2 ≤ 10 :=
    hp.kappa2_lt_kappa1.le.trans (hp.kappa1_le_S.trans hp.S_le_ten)
  have h3 : p.kappa3 ≤ 10 := hp.kappa3_lt_kappa2.le.trans h2
  exact ⟨one_div_le_one_div_of_le hk2 h2, one_div_le_one_div_of_le hk3 h3,
    one_div_le_one_div_of_le (by norm_num) hs⟩

/-- The literal local-cutoff unit sources for every admissible mother parameter tuple. -/
theorem mother_unit_pair_integral (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let a := fun d => wuLocalCutoff N δ d p.S
      let c1 := fun d => wuLocalCutoff N δ d p.kappa1
      let c2 := fun d => wuLocalCutoff N δ d p.kappa2
      let c3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a c1 c2 c3 b word20 +
        FourPrimeUnit.source N W a c1 c2 c3 b word21 ≤
      boxedIntegral20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
        boxedIntegral21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hT⟩ := source_pair_integral k hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have h := hT N hN i Δ V hb (fun _ => 1/p.S) (fun _ => 1/p.kappa1)
    (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s)
    (fun _ _ => parameter_outer_bounds hp hs)
  simpa only [unit20, unit21, wuLocalCutoff] using h.2.2

end Wu2008DoubleSieve.HighUnitSource
