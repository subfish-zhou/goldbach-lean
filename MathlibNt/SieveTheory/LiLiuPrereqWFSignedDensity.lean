import MathlibNt.SieveTheory.LiLiuPrereqWFSignedSieve
import MathlibNt.SieveTheory.LiLiuPrereqWFFundamentalLemma

/-!
# Same-family density and the small-weight replacement cost

All densities below belong to the fixed normalized family of `SignedFamily`.
The negative rough mass is counted once per prime subset, not once per
labelled permutation. The upper replacement error is added, and the lower
replacement error is subtracted. The remaining coarse rounded density is not
estimated by the small-weight fundamental lemma.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open scoped Classical

noncomputable def smallWeightDensity (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
    (if upper then upperSmallWeight P D ε d else lowerSmallWeight P D ε d) * g d

noncomputable def signedFamilyDensity (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ d ∈ (P.prod id).divisors, signedFamilyAggregate upper P D ε label d * g d

noncomputable def roughSignedDensity (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (R : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ R.powerset, normalizedSignedSet upper b c D r * ∏ p ∈ r, g p

/-- The magnitude of the actual odd (negative) coefficient, not an absolute
value bound on a different box expansion. -/
noncomputable def negativeRoughMass (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (R : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ R.powerset,
    (if Even r.card then 0 else -normalizedSignedSet upper b c D r) * ∏ p ∈ r, g p

private theorem smallWeightDensity_eq_powerset (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    smallWeightDensity upper P D ε g =
      ∑ a ∈ (geometricSmallPrimes P D ε).powerset,
        (if upper then upperSmallWeight P D ε (a.prod id)
          else lowerSmallWeight P D ε (a.prod id)) * ∏ p ∈ a, g p := by
  let B := geometricSmallPrimes P D ε
  have hsf := primeProduct_squarefree B (smallPrimes_prime P D ε)
  have hpf : (B.prod id).primeFactors = B := Nat.primeFactors_prod (smallPrimes_prime P D ε)
  rw [smallWeightDensity, sum_divisors_eq_sum_powerset hsf]
  change (∑ a ∈ (B.prod id).primeFactors.powerset, _) = _
  rw [hpf]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact hg.map_prod_of_subset_primeFactors (B.prod id) a
    (by simpa only [hpf] using mem_powerset.mp ha)

private theorem prod_partition (s B : Finset ℕ) (g : ℕ → ℝ) :
    (∏ p ∈ s, g p) = (∏ p ∈ s \ B, g p) * ∏ p ∈ s ∩ B, g p := by
  rw [← Finset.prod_union]
  · rw [sdiff_union_inter]
  · exact Finset.disjoint_left.mpr
      (fun p hp hq => (mem_sdiff.mp hp).2 (mem_inter.mp hq).2)

/-- Exact multiplicative-density reindexing of the actual full-integer
aggregate on its squarefree consumption domain. -/
theorem signedFamilyDensity_partition (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (label : ℕ → ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    signedFamilyDensity upper P D ε label g =
      ∑ r ∈ (P \ geometricSmallPrimes P D ε).powerset,
        normalizedSignedSet upper
          (fun p => geometricLower D ε (ε ^ 9) (label p))
          (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D r *
        (if LooseSign upper r.card then smallWeightDensity true P D ε g
          else smallWeightDensity false P D ε g) * ∏ p ∈ r, g p := by
  let B := geometricSmallPrimes P D ε
  let b := fun p => geometricLower D ε (ε ^ 9) (label p)
  let c := fun p => b p ^ (1 + ε ^ 9)
  have hsf := primeProduct_squarefree P hP
  have hpf : (P.prod id).primeFactors = P := Nat.primeFactors_prod hP
  have hB : B ⊆ P := Finset.filter_subset _ _
  rw [signedFamilyDensity, sum_divisors_eq_sum_powerset hsf, hpf]
  calc
    _ = ∑ s ∈ P.powerset,
        normalizedSignedSet upper b c D (s \ B) *
        signedSmallWeight upper P D ε (s \ B).card ((s ∩ B).prod id) *
        ((∏ p ∈ s \ B, g p) * ∏ p ∈ s ∩ B, g p) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := mem_powerset.mp hs
      have hsp : ∀ p ∈ s, p.Prime := fun p hp => hP p (hs' hp)
      have hspF : (s.prod id).primeFactors = s := Nat.primeFactors_prod hsp
      have hgs : g (s.prod id) = ∏ p ∈ s, g p :=
        hg.map_prod_of_subset_primeFactors (P.prod id) s
          (by simpa only [hpf] using hs')
      rw [signedFamilyAggregate_squarefree_normalized upper P label hD hε hlabel hhead
        (primeProduct_squarefree s hsp) (by simpa only [hspF] using hs'),
        hspF, hgs, prod_partition s B g]
    _ = ∑ r ∈ (P \ B).powerset, ∑ a ∈ B.powerset,
        normalizedSignedSet upper b c D r *
        signedSmallWeight upper P D ε r.card (a.prod id) *
        ((∏ p ∈ r, g p) * ∏ p ∈ a, g p) := by
      simpa only [Finset.inter_eq_right.mpr hB] using
        sum_powerset_partition P B (fun r a =>
          normalizedSignedSet upper b c D r *
          signedSmallWeight upper P D ε r.card (a.prod id) *
          ((∏ p ∈ r, g p) * ∏ p ∈ a, g p))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [smallWeightDensity_eq_powerset true P D ε hg,
        smallWeightDensity_eq_powerset false P D ε hg]
      simp only [Bool.false_eq_true, if_false, if_true]
      unfold signedSmallWeight
      by_cases hr : LooseSign upper r.card <;> simp only [hr, if_false, if_true]
      · rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      · rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring

private theorem coefficient_small_replacement (upper : Bool) (b c : ℕ → ℝ)
    (D lo hi : ℝ) (r : Finset ℕ) :
    normalizedSignedSet upper b c D r * (if LooseSign upper r.card then hi else lo) =
      (if upper then hi else lo) * normalizedSignedSet upper b c D r +
        (if upper then 1 else -1) * (hi - lo) *
          (if Even r.card then 0 else -normalizedSignedSet upper b c D r) := by
  cases upper <;> by_cases heven : Even r.card <;>
    simp only [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet,
      LooseSign, Bool.false_eq_true, if_false, if_true, heven, not_true_eq_false,
      not_false_eq_true] <;> split_ifs <;> ring

/-- Both signs use the SAME aggregate: the upper error is positive and the
lower error negative when `hi ≥ lo`. -/
theorem signedFamilyDensity_replacement_identity (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (label : ℕ → ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    let B := geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (label p)
    let c := fun p => b p ^ (1 + ε ^ 9)
    signedFamilyDensity upper P D ε label g =
      smallWeightDensity upper P D ε g * roughSignedDensity upper b c D (P \ B) g +
        (if upper then 1 else -1) *
          (smallWeightDensity true P D ε g - smallWeightDensity false P D ε g) *
          negativeRoughMass upper b c D (P \ B) g := by
  dsimp only
  rw [signedFamilyDensity_partition upper P hP label hD hε hlabel hhead hg]
  simp only [roughSignedDensity, negativeRoughMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [coefficient_small_replacement]
  cases upper <;> simp only [if_true, Bool.false_eq_true, if_false] <;> ring

theorem negativeRoughMass_bounds (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (R : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ R, 0 ≤ g p) :
    0 ≤ negativeRoughMass upper b c D R g ∧
      negativeRoughMass upper b c D R g ≤ ∏ p ∈ R, (1 + g p) := by
  have hcoeff : ∀ r : Finset ℕ,
      0 ≤ (if Even r.card then (0 : ℝ) else -normalizedSignedSet upper b c D r) ∧
        (if Even r.card then (0 : ℝ) else -normalizedSignedSet upper b c D r) ≤ 1 := by
    intro r
    cases upper <;> by_cases heven : Even r.card <;>
      simp only [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet,
        Bool.false_eq_true, if_false, if_true, heven] <;> (try split_ifs) <;> norm_num
  have hprod : ∀ r ∈ R.powerset, 0 ≤ ∏ p ∈ r, g p :=
    fun r hr => Finset.prod_nonneg (fun p hp => hg p (mem_powerset.mp hr hp))
  constructor
  · exact Finset.sum_nonneg
      (fun r hr => mul_nonneg (hcoeff r).1 (hprod r hr))
  · rw [Finset.prod_one_add]
    exact Finset.sum_le_sum (fun r hr => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcoeff r).2 (hprod r hr))

/-- The accepted full small-weight fundamental lemma now pays the replacement
inside this very family. The absolute constant precedes epsilon, and the
large-D threshold precedes P, omega, K and the choice of side.

The rough Euler majorant is explicit; this is NOT the remaining estimate of
the signed rounded density by the linear-sieve functions F and f. -/
theorem exists_signedFamilyDensity_replacement_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
          (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) →
          ∀ (ω : ArithmeticFunction ℝ), ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ upper : Bool,
                let B := geometricSmallPrimes P D ε
                let label := geometricSieveLabel D ε
                let b := fun p => geometricLower D ε (ε ^ 9) (label p)
                let c := fun p => b p ^ (1 + ε ^ 9)
                let V := ∏ p ∈ B, (1 - ω p / (p : ℝ))
                let E := C * (Real.exp (-(1 / ε)) +
                  Real.exp (Real.sqrt K - 1 / ε) *
                    (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
                let δ := signedFamilyDensity upper P D ε label (primeDensity ω) -
                  smallWeightDensity upper P D ε (primeDensity ω) *
                    roughSignedDensity upper b c D (P \ B) (primeDensity ω)
                0 ≤ (if upper then 1 else -1) * δ ∧
                  |δ| ≤ 2 * V * E * ∏ p ∈ P \ B, (1 + ω p / (p : ℝ)) := by
  obtain ⟨C, hC, hfund⟩ := exists_smallWeight_source_density_sandwich
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₀, hD₀, hfund⟩ := hfund ε hε hεsmall
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD P hP hcut ω hω hg K hK hdim upper
  have hD2 : 2 ≤ D := hD₀.trans hD
  have hsmall := hfund D hD P ω hω
    (fun p hp => hg p (Finset.mem_filter.mp hp).1) K hK hdim
  let B := geometricSmallPrimes P D ε
  let label := geometricSieveLabel D ε
  let b := fun p => geometricLower D ε (ε ^ 9) (label p)
  let c := fun p => b p ^ (1 + ε ^ 9)
  let g := primeDensity ω
  let V := ∏ p ∈ B, (1 - ω p / (p : ℝ))
  let E := C * (Real.exp (-(1 / ε)) +
    Real.exp (Real.sqrt K - 1 / ε) * (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
  let gap := smallWeightDensity true P D ε g - smallWeightDensity false P D ε g
  have hgap0 : 0 ≤ gap := by
    dsimp only at hsmall
    dsimp [gap, smallWeightDensity, g]
    linarith [hsmall.2.1, hsmall.2.2.1]
  have hgap : gap ≤ 2 * V * E := by
    simpa only [gap, smallWeightDensity, Bool.false_eq_true, if_false, if_true,
      g, primeDensity_apply] using hsmall.2.2.2.2
  have hmax0 : 0 ≤ 2 * V * E := hgap0.trans hgap
  have hm := negativeRoughMass_bounds upper b c D (P \ B) g
    (fun p hp => (hg p (Finset.mem_sdiff.mp hp).1).1)
  have hid := signedFamilyDensity_replacement_identity upper P hP label hD2 hε
    (geometricSieveLabel_mem P hP (by linarith) hε)
    (geometricSieveLabel_head_lt P hP (by linarith) hε hcut)
    (primeDensity_isMultiplicative hω)
  change signedFamilyDensity upper P D ε label g =
    smallWeightDensity upper P D ε g * roughSignedDensity upper b c D (P \ B) g +
      (if upper then 1 else -1) * gap * negativeRoughMass upper b c D (P \ B) g at hid
  have hcost : gap * negativeRoughMass upper b c D (P \ B) g ≤
      2 * V * E * ∏ p ∈ P \ B, (1 + g p) :=
    mul_le_mul hgap hm.2 hm.1 hmax0
  change 0 ≤ (if upper then 1 else -1) *
      (signedFamilyDensity upper P D ε label g -
        smallWeightDensity upper P D ε g * roughSignedDensity upper b c D (P \ B) g) ∧
    |signedFamilyDensity upper P D ε label g -
      smallWeightDensity upper P D ε g * roughSignedDensity upper b c D (P \ B) g| ≤
      2 * V * E * ∏ p ∈ P \ B, (1 + g p)
  rw [hid, add_sub_cancel_left]
  have hn := mul_nonneg hgap0 hm.1
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true, one_mul,
    neg_mul, abs_neg, neg_neg, abs_of_nonneg hn] <;> exact ⟨hn, hcost⟩

#check signedFamilyDensity_partition
#check signedFamilyDensity_replacement_identity
#check negativeRoughMass_bounds
#print axioms signedFamilyDensity_partition
#print axioms signedFamilyDensity_replacement_identity
#print axioms negativeRoughMass_bounds
#check exists_signedFamilyDensity_replacement_bound
#print axioms exists_signedFamilyDensity_replacement_bound

end MathlibNt.SieveTheory.LiLiuPrereqWF
