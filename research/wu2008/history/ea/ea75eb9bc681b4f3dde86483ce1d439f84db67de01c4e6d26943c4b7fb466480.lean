import MathlibNt.Wu2008DoubleSieve.Omega3LayerSieve

/-!
# The actual switched AP residual on common bounded profile layers

The interval error remains prime-count centered. Its absolute value is
taken only after summing all cofactors in a layer. No distribution estimate
or logarithmic-integral replacement is assumed.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3ProfilePrimes (N : ℕ) (a b : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)

noncomputable def omega3ProfileError (N q e : ℕ) (a b : ℝ) : ℝ :=
  (((omega3ProfilePrimes N a b).filter (fun p => Nat.ModEq q (e * p) N)).card : ℝ) -
    (omega3ProfilePrimes N a b).card / (Nat.totient q : ℝ)

theorem omega3Layer_prime_fibre_eq_profile {N : ℕ} {δ s : ℝ}
    {L : Finset Omega3CofactorIndex} {j e : ℕ}
    (he : e ∈ omega3LayerSupport L j) (hepos : 0 < e) :
    omega3CofactorPrimeFibreLE N δ s (omega3LayerLabel L j e) =
      omega3ProfilePrimes N (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e) := by
  ext p
  constructor
  · intro hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (omega3Layer_prime_fibre_iff he hepos).mp hp⟩
  · intro hp
    exact (omega3Layer_prime_fibre_iff he hepos).mpr (mem_filter.mp hp).2

theorem omega3Layer_prime_error_eq_profile {N q : ℕ} {δ s : ℝ}
    {L : Finset Omega3CofactorIndex} {j e : ℕ}
    (he : e ∈ omega3LayerSupport L j) (hepos : 0 < e) :
    (omega3SieveAPCount N δ s (omega3LayerLabel L j e) q : ℝ) -
        (omega3CofactorPrimeFibreLE N δ s (omega3LayerLabel L j e)).card / (Nat.totient q : ℝ) =
      omega3ProfileError N q e (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e) := by
  unfold omega3SieveAPCount omega3ProfileError
  rw [omega3Layer_prime_fibre_eq_profile he hepos, (omega3LayerLabel_mem he).2]

theorem omega3SieveAPResidual_eq_layers {i N B q : ℕ} {δ s t : ℝ}
    (W : Fin i → Finset ℕ)
    (hB : ∀ e, (omega3LayerFibre (omega3CofactorLabels N δ s t W) e).card ≤ B)
    (hpos : ∀ c ∈ omega3CofactorLabels N δ s t W, 0 < omega3CofactorValue c) :
    let L := omega3CofactorLabels N δ s t W
    omega3SieveAPResidual N δ s t W q =
      ∑ j ∈ range B, ∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
        omega3LayerCoefficient W L j e *
          omega3ProfileError N q e (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e) := by
  dsimp only
  rw [omega3SieveAPResidual_eq_common_layers N δ s t W B hB q]
  apply sum_congr rfl
  intro j _
  unfold omega3LayerAPResidual
  apply sum_congr rfl
  intro e he
  have he' := (mem_filter.mp he).1
  have hlabel := omega3LayerLabel_mem he'
  rw [omega3Layer_prime_error_eq_profile he' (hlabel.2 ▸ hpos _ hlabel.1)]

theorem omega3SieveR1_le_layers {i N D B : ℕ} {δ s t Z : ℝ}
    (W : Fin i → Finset ℕ)
    (hB : ∀ e, (omega3LayerFibre (omega3CofactorLabels N δ s t W) e).card ≤ B)
    (hpos : ∀ c ∈ omega3CofactorLabels N δ s t W, 0 < omega3CofactorValue c) :
    let L := omega3CofactorLabels N δ s t W
    omega3SieveR1 N D δ s t Z W ≤
      ∑ j ∈ range B, ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          omega3LayerCoefficient W L j e *
            omega3ProfileError N q e (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e)| := by
  dsimp only
  refine (omega3SieveR1_le_common_layers N D δ s t Z W B hB).trans_eq ?_
  apply sum_congr rfl
  intro j _
  unfold omega3LayerR1
  apply sum_congr rfl
  intro q _
  congr 2
  unfold omega3LayerAPResidual
  apply sum_congr rfl
  intro e he
  have he' := (mem_filter.mp he).1
  have hlabel := omega3LayerLabel_mem he'
  rw [omega3Layer_prime_error_eq_profile he' (hlabel.2 ▸ hpos _ hlabel.1)]

/-- One threshold constructs the same at-most-ceil(C) layers for every
modulus and both endpoints before the actual residual norm is bounded. -/
theorem omega3_source_R1_le_common_profiles (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ D : ℕ, ∀ Z : ℝ,
        let W := convolutionWuWindows N Δ V
        let L := omega3CofactorLabels N δ s t W
        omega3SieveR1 N D δ s t Z W ≤
          ∑ j ∈ range (omega3LayerCount k δ), ∑ q ∈ omega3SieveModuli N D Z,
            (3 : ℝ) ^ q.primeFactors.card *
              |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
                omega3LayerCoefficient W L j e *
                  omega3ProfileError N q e (omega3LayerLower L j e)
                    (omega3LayerUpper N δ s L j e)| := by
  obtain ⟨T, hT4, hT⟩ := omega3_cofactor_layers_bounded k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht D Z
  have hcard := (hT N hN i Δ V hb s t hs hst ht).1
  apply omega3SieveR1_le_layers _ hcard
  intro c hc
  rcases c with ⟨d, p2, p1, n⟩
  obtain ⟨hd, h2, h1, _, hn, _, _⟩ := mem_omega3CofactorLabels.mp hc
  have hdpos := (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos hn)
    (mem_primeWindow.mp h1).1.pos) (mem_primeWindow.mp h2).1.pos

end Wu2008DoubleSieve
