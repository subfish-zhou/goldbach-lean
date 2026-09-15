import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveInstance

/-! Actual dependent source families consume complete cofactor layers and balanced distribution. -/
namespace Wu2008DoubleSieve.HighUnitSieve
open Finset Real Filter SecondFunctionalUnitPrimeFibre
open scoped Classical Topology

/-- One fixed constant works for every slab family with at most five free coordinates.
The original sigma multiplicity and positive integer coefficient are proved internally. -/
theorem source_R1_log_saving (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∃ hT : 4 ≤ T,
      ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ)^(1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ) (Z : ℝ),
      (sourceFamily (by omega : 2 ≤ N) hδ hδhi hb P j b).R1
        (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N / log (N : ℝ)^A := by
  have hη := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num : (0 : ℝ) < 10)
  let F : ℝ := (max 1 (1/(wuLocalExponent k δ / 10)))^(k+5)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨C, hC, T1, hT1, hd⟩ :=
    LabelledPhysical.Family.R1_log_saving A (wuLocalExponent k δ / 10) F hA hη hF hδ
  obtain ⟨T2, _, hs⟩ := source_fibres k hδ hδhi
  refine ⟨C, hC, max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb n hn P j b Z
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT1.trans hN1
  obtain ⟨_, hG⟩ := hs N hN2 i Δ V hb
  have hg := hG n P j b
  apply hd N hN1 _ (sourceFamily (by omega) hδ hδhi hb P j b) _ _ _ Z
  · intro c hc
    exact ⟨(hg.1 c hc).1.power_lower, (hg.1 c hc).1.power_upper⟩
  · intro c hc
    change (1 : ℝ) ≤ (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)
    exact_mod_cast coefficient_pos hc
  · intro e
    exact (hg.2 e).trans (pow_le_pow_right₀ (le_max_left 1 _) (Nat.add_le_add_left hn k))

/-- Both literal mother families, with all four and five coordinates, at one threshold.
No mother parameter, support, endpoint, or sieve cutoff enters the choice of C or T. -/
theorem mother_R1_log_saving (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∃ hT : 4 ≤ T,
      ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ (p : SecondFunctionalParameters) (Z : ℝ),
      let R := fun d : ℕ => (N : ℝ)^(1/2-δ)/d
      let b := fun _ : ℕ => 1/p.s
      let L20 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix20 (R d) (1/p.kappa2) (1/p.kappa3) (1/p.s)) (Fin.last 3) b
      let L21 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix21 (R d) (1/p.kappa3) (1/p.s)) (Fin.last 4) b
      L20.R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z + L21.R1 (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤
        C*N / log (N : ℝ)^A := by
  obtain ⟨C, hC, T, hT, hd⟩ := source_R1_log_saving k hδ hδhi hA
  refine ⟨2*C, by positivity, T, hT, ?_⟩
  intro N hN i Δ V hb p Z
  dsimp only
  have h20 := hd N hN i Δ V hb 4 (by omega)
    (fun d => HighUnit.primePrefix20 _ (1/p.kappa2) (1/p.kappa3) (1/p.s))
    (Fin.last 3) (fun _ => 1/p.s) Z
  have h21 := hd N hN i Δ V hb 5 (by omega)
    (fun d => HighUnit.primePrefix21 _ (1/p.kappa3) (1/p.s))
    (Fin.last 4) (fun _ => 1/p.s) Z
  exact (add_le_add h20 h21).trans_eq (by ring)

/-- Relative payment of the two actual R1 terms, uniformly even in Z.
Specializing Z to sqrt Q gives the physical sieve endpoint including q = floor Q. -/
theorem mother_R1_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T, ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ (p : SecondFunctionalParameters) (Z : ℝ),
      let Q := (N : ℝ)^(1/2-δ)
      let R := fun d : ℕ => Q/d
      let b := fun _ : ℕ => 1/p.s
      let L20 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix20 (R d) (1/p.kappa2) (1/p.kappa3) (1/p.s)) (Fin.last 3) b
      let L21 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix21 (R d) (1/p.kappa3) (1/p.s)) (Fin.last 4) b
      L20.R1 (⌊Q⌋₊+1) Z + L21.R1 (⌊Q⌋₊+1) Z ≤
        ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hT1, hd⟩ := mother_R1_log_saving k hδ hδhi
    (show (0 : ℝ) < (5*k+3 : ℕ) by positivity)
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨T3, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C/(ε*c))))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p Z
  dsimp only
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog := log_pos (by exact_mod_cast (show 1 < N by have := hT1.trans hN1; omega) : (1 : ℝ) < N)
  have hr := hd N hN1 i Δ V hb p Z
  dsimp only at hr
  rw [rpow_natCast] at hr
  have htheta := hTheta N hN2 i hb.1 Δ hb.2.1 hb.2.2.1 V
    hb.2.2.2.2.1 hb.2.2.2.2.2
  have hbudget : C / log (N : ℝ) ≤ ε*c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hlogT N hN3)
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C*N / log (N : ℝ)^(5*k+3) := hr
    _ = (C/log (N : ℝ))*((N : ℝ)/log (N : ℝ)^(5*k+2)) := by
      rw [show 5*k+3 = (5*k+2)+1 by omega, pow_succ]
      ring
    _ ≤ (ε*c)*((N : ℝ)/log (N : ℝ)^(5*k+2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε*(c*(N : ℝ)/log (N : ℝ)^(5*k+2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

/-- The literal physical sieve specialization, with D = floor Q + 1 and Z = sqrt Q. -/
theorem mother_R1_sieve_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T, ∀ (N : ℕ) (hN : T ≤ N),
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : wuSourceBox k δ N i Δ V),
      ∀ p : SecondFunctionalParameters,
      let Q := (N : ℝ)^(1/2-δ)
      let R := fun d : ℕ => Q/d
      let b := fun _ : ℕ => 1/p.s
      let L20 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix20 (R d) (1/p.kappa2) (1/p.kappa3) (1/p.s)) (Fin.last 3) b
      let L21 := sourceFamily (by omega : 2 ≤ N) hδ hδhi hb
        (fun d => HighUnit.primePrefix21 (R d) (1/p.kappa3) (1/p.s)) (Fin.last 4) b
      L20.R1 (⌊Q⌋₊+1) (sqrt Q) + L21.R1 (⌊Q⌋₊+1) (sqrt Q) ≤
        ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, hd⟩ := mother_R1_relative k hδ hδhi hε
  exact ⟨T, hT, fun N hN i Δ V hb p => hd N hN i Δ V hb p _⟩

end Wu2008DoubleSieve.HighUnitSieve
