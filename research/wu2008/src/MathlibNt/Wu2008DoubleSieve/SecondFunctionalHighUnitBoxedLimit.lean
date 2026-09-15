import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitLimit
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureSource

open scoped BigOperators Classical Topology
namespace Wu2008DoubleSieve.HighUnit
open Real Filter SecondFunctionalUnitPrimeFibre

/-- Literal physical envelope at X=N/d, with the closed last-prime cap. -/
noncomputable def boxed20 (N d : ℕ) (δ a2 a3 b : ℝ) : ℝ :=
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  ∑ f ∈ primePrefix20 R a2 a3 b,
    ((physical (prefixProduct f) ((N : ℝ) / d) (f (Fin.last 3)).val (R^b)).card : ℝ)

/-- The five-coordinate labelled envelope; no source inclusion is asserted. -/
noncomputable def boxed21 (N d : ℕ) (δ a3 b : ℝ) : ℝ :=
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  ∑ f ∈ primePrefix21 R a3 b,
    ((physical (prefixProduct f) ((N : ℝ) / d) (f (Fin.last 4)).val (R^b)).card : ℝ)

/-- The actual source phi gives the physical scale, not the sieve level. -/
theorem boxed_scale_identity {N d : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d)
    (hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d) :
    ((N : ℝ) ^ (1 / 2 - δ) / d) ^ omega3XPhi N d δ = (N : ℝ) / d := by
  have hX : 0 < (N : ℝ) / d := div_pos (by exact_mod_cast hN) (by exact_mod_cast hd)
  rw [omega3XPhi, rpow_def_of_pos (lt_trans zero_lt_one hR)]
  rw [mul_div_cancel₀ _ (log_pos hR).ne', exp_log hX]

/-- One threshold precedes every source box, supported divisor, and moving window.
Each component has error epsilon; this is not a combined epsilon claim. -/
theorem boxed_pair_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → 1/10 ≤ a3 → b ≤ 1/2 →
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        (|log R / ((N : ℝ) / d) * boxed20 N d δ a2 a3 b -
          J20 a2 a3 b (omega3XPhi N d δ)| < epsilon) ∧
        (|log R / ((N : ℝ) / d) * boxed21 N d δ a3 b -
          J21 a3 b (omega3XPhi N d δ)| < epsilon) := by
  obtain ⟨R0, _, hp⟩ := physical_pair_uniform epsilon he
  have hη := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd a2 a3 b ha2 ha3 hb'
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hd0 := boxConvolutionSupport_pos
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  have hs := boxed_scale_identity (by omega : 0 < N) hd0 hg.2.1
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  have h := hp _ hlarge a2 a3 b (omega3XPhi N d δ) ha2 ha3 hb'
  simpa only [hs, boxed20, boxed21] using h

/-- Elementary removal of the positive normalizing factor. -/
theorem unnormalize {N d : ℕ} {R E J epsilon : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < R)
    (h : |log R / ((N : ℝ) / d) * E - J| < epsilon) :
    |E - (N : ℝ) / ((d : ℝ) * log R) * J| <
      (N : ℝ) / ((d : ℝ) * log R) * epsilon := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl := log_pos hR
  have hc : 0 < (N : ℝ) / ((d : ℝ) * log R) := by positivity
  have heq : E - (N : ℝ) / ((d : ℝ) * log R) * J =
      (N : ℝ) / ((d : ℝ) * log R) * (log R / ((N : ℝ) / d) * E - J) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hc]
  exact mul_lt_mul_of_pos_left h hc

/-- Actual unnormalized per-divisor two-sided comparisons on the same threshold. -/
theorem boxed_pair_unnormalized (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → 1/10 ≤ a3 → b ≤ 1/2 →
        let R := (N : ℝ) ^ (1 / 2 - δ) / d
        (|boxed20 N d δ a2 a3 b - (N : ℝ) / ((d : ℝ) * log R) *
          J20 a2 a3 b (omega3XPhi N d δ)| <
            (N : ℝ) / ((d : ℝ) * log R) * epsilon) ∧
        (|boxed21 N d δ a3 b - (N : ℝ) / ((d : ℝ) * log R) *
          J21 a3 b (omega3XPhi N d δ)| <
            (N : ℝ) / ((d : ℝ) * log R) * epsilon) := by
  obtain ⟨T, hT4, hT⟩ := boxed_pair_uniform k hδ hδhi he
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb d hd a2 a3 b ha2 ha3 hb'
  have hN4 : 4 ≤ N := hT4.trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hd0 := boxConvolutionSupport_pos
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  obtain ⟨h20, h21⟩ := hT N hN i Δ V hb d hd a2 a3 b ha2 ha3 hb'
  exact ⟨unnormalize (by omega) hd0 hg.2.1 h20,
    unnormalize (by omega) hd0 hg.2.1 h21⟩

end Wu2008DoubleSieve.HighUnit
