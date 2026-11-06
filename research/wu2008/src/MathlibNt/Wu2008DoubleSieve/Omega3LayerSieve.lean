import MathlibNt.Wu2008DoubleSieve.Omega3LayerActual
import MathlibNt.Wu2008DoubleSieve.Omega3SieveDefinitions

/-!
# The literal finite-sieve R1 on bounded common layers

This specializes the exact arbitrary-test identity to the actual closed
prime fibres and their actual AP counts. The result is a finite regrouping,
not an analytic payment of R1.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3LayerAPResidual {i : ℕ} (N : ℕ) (δ s : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (j q : ℕ) : ℝ :=
  ∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
    omega3LayerCoefficient W L j e *
      ((omega3SieveAPCount N δ s (omega3LayerLabel L j e) q : ℝ) -
        (omega3CofactorPrimeFibreLE N δ s (omega3LayerLabel L j e)).card /
          (Nat.totient q : ℝ))

noncomputable def omega3LayerR1 {i : ℕ} (N D : ℕ) (δ s Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) (j : ℕ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    (3 : ℝ) ^ q.primeFactors.card * |omega3LayerAPResidual N δ s W L j q|

/-- Exact equality for the whole signed actual AP residual, before any
absolute value. The selected label and its two endpoints are unchanged. -/
theorem omega3SieveAPResidual_eq_common_layers {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre (omega3CofactorLabels N δ s t W) e).card ≤ B)
    (q : ℕ) :
    omega3SieveAPResidual N δ s t W q =
      ∑ j ∈ range B,
        omega3LayerAPResidual N δ s W (omega3CofactorLabels N δ s t W) j q :=
  omega3Layer_coprime_weighted_sum W (omega3CofactorLabels N δ s t W) B hB q
    (fun c => (omega3SieveAPCount N δ s c q : ℝ) -
      (omega3CofactorPrimeFibreLE N δ s c).card / (Nat.totient q : ℝ))

theorem omega3SieveR1_le_common_layers {i : ℕ} (N D : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre (omega3CofactorLabels N δ s t W) e).card ≤ B) :
    omega3SieveR1 N D δ s t Z W ≤
      ∑ j ∈ range B,
        omega3LayerR1 N D δ s Z W (omega3CofactorLabels N δ s t W) j :=
  omega3Layer_modulus_sum_le W (omega3CofactorLabels N δ s t W) B hB
    (omega3SieveModuli N D Z) (fun q => (3 : ℝ) ^ q.primeFactors.card)
    (fun _ _ => by positivity)
    (fun q c => (omega3SieveAPCount N δ s c q : ℝ) -
      (omega3CofactorPrimeFibreLE N δ s c).card / (Nat.totient q : ℝ))


end Wu2008DoubleSieve
