import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization
import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies
import MathlibNt.Wu2008DoubleSieve.CanonicalBoundedDensity

/-!
# Gamma5: literal labels and the finite signed remainder

The mask and the cutoff are functions of the complete label, not of its
product. Only after taking a positive AP majorant do we regroup products.
Neither disjoint windows nor coprimality with the old product is imposed.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

abbrev Gamma5ClassicalLabel := ℕ × ℕ × ℕ

noncomputable def gamma5ClassicalS : ℝ := 103 / 25

noncomputable def gamma5ClassicalB : ℝ := 100 / 291

def gamma5ClassicalProduct (x : Gamma5ClassicalLabel) : ℕ :=
  x.1 * x.2.1 * x.2.2

noncomputable def gamma5ClassicalLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  ((boxConvolutionSupport W) ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    (fun x => x.2.1.Prime ∧ x.2.2.Prime ∧
      x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
      wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) ∧
      x.2.1 < x.2.2 ∧
      (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma5ClassicalB)

noncomputable def gamma5ClassicalCount {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) : ℝ :=
  ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N)
      (wuLocalCutoff N δ x.1 gamma5ClassicalS) : ℝ)

noncomputable def gamma5ClassicalMainMass {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
      wuSingularSeries (gamma5ClassicalProduct x * N) /
        ((Nat.totient (gamma5ClassicalProduct x) : ℝ) *
          log ((N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x))

noncomputable def gamma5ClassicalRemainder {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel)
    (z : Gamma5ClassicalLabel → ℝ) : ℝ :=
  ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
    ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
      (wuVariableRosserLevel N δ (gamma5ClassicalProduct x)) (z x)

/-- Casting the literal natural count preserves every convolution multiplicity. -/
theorem gamma5ClassicalCount_eq_nat_count {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) :
    gamma5ClassicalCount N δ W X =
      ((∑ x ∈ X, convolutionCoeff W x.1 *
        (sourceSieveCarrier N (gamma5ClassicalProduct x) (x.1 * N)
          (wuLocalCutoff N δ x.1 gamma5ClassicalS)).card : ℕ) : ℝ) := by
  simp only [gamma5ClassicalCount, sourceSieveCount, Nat.cast_sum, Nat.cast_mul,
    Int.cast_natCast]

theorem gamma5Classical_sifted_mul_prime {A n p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    Sifted A n z ↔ Sifted (A * p) n z := by
  constructor
  · intro h r hr hc hrz
    exact h r hr (Nat.coprime_mul_iff_right.mp hc).1 hrz
  · intro h r hr hc hrz
    have hrp : r ≠ p := by
      intro he
      subst r
      exact (not_lt_of_ge hz) hrz
    exact h r hr (Nat.coprime_mul_iff_right.mpr
      ⟨hc, (Nat.coprime_primes hr hp).mpr hrp⟩) hrz

/-- Exact equality of the two unscaled source counts. -/
theorem gamma5Classical_source_count_eq {N d p q : ℕ} {z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ)) (hzq : z ≤ (q : ℝ)) :
    sourceSieveCount N (d * p * q) (d * N) z =
      sourceSieveCount N (d * p * q) ((d * p * q) * N) z := by
  unfold sourceSieveCount
  congr 2
  ext r
  simp only [sourceSieveCarrier, mem_filter]
  have h := gamma5Classical_sifted_mul_prime (A := d * N) (n := N - r) hp hzp
  have h' := gamma5Classical_sifted_mul_prime (A := d * N * p) (n := N - r) hq hzq
  have he : d * N * p * q = d * p * q * N := by ring
  rw [he] at h'
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => h.trans h'

theorem gamma5Classical_source_count_antitone (N d A : ℕ) {z w : ℝ}
    (hzw : z ≤ w) :
    (sourceSieveCount N d A w : ℝ) ≤ (sourceSieveCount N d A z : ℝ) := by
  have hsub : sourceSieveCarrier N d A w ⊆ sourceSieveCarrier N d A z := by
    intro p hp
    obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp, hprime, hd,
      fun r hr hc hz => hs r hr hc (hz.trans_le hzw)⟩
  unfold sourceSieveCount
  exact_mod_cast card_le_card hsub

/-- The two adjoined windows preserve all ordered tuple fibres. -/
theorem gamma5Classical_AP_expansion {i : ℕ} (N Q : ℕ)
    (W : Fin i → Finset ℕ) (P : Finset ℕ) :
    convolutionAPError N Q (Fin.cons P (Fin.cons P W)) =
      ∑ x ∈ boxConvolutionSupport W ×ˢ (P ×ˢ P),
        (convolutionCoeff W x.1 : ℝ) *
          ∑ r ∈ (Icc 1 (Q / gamma5ClassicalProduct x)).filter
              (fun r => r.Coprime (gamma5ClassicalProduct x * N)),
            |primeAPError N (gamma5ClassicalProduct x * r) N| := by
  rw [convolutionAPError_eq_support_sum]
  change (∑ m ∈ boxConvolutionSupport (Fin.cons P (Fin.cons P W)),
    (convolutionCoeff (Fin.cons P (Fin.cons P W)) m : ℝ) *
      ∑ r ∈ (Icc 1 (Q / m)).filter (fun r => r.Coprime (m * N)),
        |primeAPError N (m * r) N|) = _
  rw [boxConvolution_sum_cons, boxConvolution_sum_cons]
  simp only [sum_product, mul_sum, gamma5ClassicalProduct]
  rfl

/-- Uniform in every finite mask and every label-dependent cutoff, including
different cutoffs on distinct labels with the same product. -/
theorem gamma5Classical_masked_remainder_le {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (X : Finset Gamma5ClassicalLabel)
    (hX : X ⊆ boxConvolutionSupport W ×ˢ (P ×ˢ P))
    (z : Gamma5ClassicalLabel → ℝ) :
    |gamma5ClassicalRemainder N δ W X z| ≤
      convolutionAPError N (convolutionModulusCutoff N δ) (Fin.cons P (Fin.cons P W)) := by
  rw [gamma5Classical_AP_expansion]
  unfold gamma5ClassicalRemainder
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
        ∑ r ∈ (Icc 1 (convolutionModulusCutoff N δ / gamma5ClassicalProduct x)).filter
            (fun r => r.Coprime (gamma5ClassicalProduct x * N)),
          |primeAPError N (gamma5ClassicalProduct x * r) N| := by
      apply sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact ordinaryRosserRemainder_le_AP (z x)
        (wuVariableRosserLevel_eq_combined N (gamma5ClassicalProduct x) δ).le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hX (fun x _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun r _ => abs_nonneg _)))

end Wu2008DoubleSieve
