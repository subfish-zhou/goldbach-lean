import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative
import MathlibNt.Wu2008DoubleSieve.Omega3SourceSieveFactor
import MathlibNt.Wu2008DoubleSieve.Omega3SieveDefinitions

/-!
# The actual switched R2 is paid at the actual source level

The natural level floor(Q)+1 retains the possible boundary modulus q=Q.
This explicitly enlarged residual is the one used by the finite consumer.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_source_moduli_exact (N q : ℕ) (δ : ℝ) :
    q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ↔
      q ∈ (ordinarySievePrimeProduct N (sqrt ((N : ℝ) ^ (1 / 2 - δ)))).divisors ∧
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
  rw [omega3SieveModuli, mem_filter, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]

theorem omega3_sieve_R2_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let Q := (N : ℝ) ^ (1 / 2 - δ)
        omega3SieveR2 N (⌊Q⌋₊ + 1) δ s t (sqrt Q) W ≤ ε * boxTheta N Q W := by
  obtain ⟨T, hT4, hT⟩ := omega3_non_coprime_relative k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN4 := hT4.trans hN
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  have hm : ∀ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
      (sqrt ((N : ℝ) ^ (1 / 2 - δ))), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    omega
  exact hT N hN i Δ V hb s t hs hst ht _ hg.2.2.2.1 _
    (filter_subset _ _) hm

end Wu2008DoubleSieve
