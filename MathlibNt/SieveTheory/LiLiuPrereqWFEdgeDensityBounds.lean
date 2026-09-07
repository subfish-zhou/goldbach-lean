import MathlibNt.SieveTheory.LiLiuPrereqWFFamilyDensity

/-!
# Euler and absolute bounds for the same truncated signed family

The tail includes primes equal to the truncation point. The absolute estimate
uses the actual squarefree aggregate, not the sum of magnitudes of its labels.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity

open Finset ArithmeticFunction SmallRosser
open scoped Classical

theorem euler_truncation_ratio (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    {w z K : ℝ} (hw : 2 ≤ w) (hwz : w < z)
    (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (hdim : DimensionOneProductBound P g K) :
    (∏ p ∈ P.filter (fun p : ℕ => (p : ℝ) < w), (1 - g p)) /
        (∏ p ∈ P, (1 - g p)) ≤
      Real.log z / Real.log w * (1 + K / Real.log w) := by
  let B := P.filter (fun p : ℕ => (p : ℝ) < w)
  have hB : B ⊆ P := filter_subset _ _
  have hVB : (∏ p ∈ B, (1 - g p)) ≠ 0 :=
    ne_of_gt (prod_pos (fun p hp => sub_pos.mpr (hg p (hB hp)).2))
  have hpart : (∏ p ∈ P, (1 - g p)) =
      (∏ p ∈ B, (1 - g p)) * (∏ p ∈ P \ B, (1 - g p)) := by
    rw [mul_comm, ← prod_union sdiff_disjoint, sdiff_union_of_subset hB]
  have heq : P \ B =
      P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
    ext p
    simp only [mem_sdiff, mem_filter, B]
    constructor
    · rintro ⟨hp, hn⟩
      exact ⟨hp, hP p hp, le_of_not_gt (fun h => hn ⟨hp, h⟩), hcut p hp⟩
    · rintro ⟨hp, _, hw, _⟩
      exact ⟨hp, fun h => (not_lt_of_ge hw) h.2⟩
  change (∏ p ∈ B, (1 - g p)) / _ ≤ _
  rw [hpart, div_mul_eq_div_div, div_self hVB, one_div, ← prod_inv_distrib, heq]
  exact hdim w z hw hwz

theorem signedFamilyDensity_abs_le_plusProduct (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ArithmeticFunction ℝ} (hgm : g.IsMultiplicative)
    (hg : ∀ p ∈ P, 0 ≤ g p) :
    |signedFamilyDensity upper P D ε (geometricSieveLabel D ε) g| ≤
      ∏ p ∈ P, (1 + g p) := by
  have hpf : (P.prod id).primeFactors = P := Nat.primeFactors_prod hP
  rw [signedFamilyDensity, sum_divisors_eq_sum_powerset (primeProduct_squarefree P hP),
    hpf, prod_one_add]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro s hs
  have hsP := mem_powerset.mp hs
  have hsp : ∀ p ∈ s, p.Prime := fun p hp => hP p (hsP hp)
  have hspf : (s.prod id).primeFactors = s := Nat.primeFactors_prod hsp
  have hgs : g (s.prod id) = ∏ p ∈ s, g p :=
    hgm.map_prod_of_subset_primeFactors (P.prod id) s (by simpa only [hpf] using hsP)
  have hcoef : |signedFamilyAggregate upper P D ε (geometricSieveLabel D ε)
      (s.prod id)| ≤ 1 := by
    rw [signedFamilyAggregate_squarefree_normalized upper P (geometricSieveLabel D ε)
      hD hε (geometricSieveLabel_mem P hP (by linarith) hε)
      (geometricSieveLabel_head_lt P hP (by linarith) hε hcut)
      (primeProduct_squarefree s hsp) (by simpa only [hspf] using hsP), abs_mul]
    apply mul_le_one₀
    · cases upper <;>
        simp only [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet,
          Bool.false_eq_true, if_true, if_false] <;> split_ifs <;> norm_num
    · exact abs_nonneg _
    · unfold signedSmallWeight
      split_ifs
      · exact upperSmallWeight_boundedOne P D ε _
      · exact lowerSmallWeight_boundedOne P D ε _
  rw [abs_mul, hgs, abs_of_nonneg (prod_nonneg (fun p hp => hg p (hsP hp)))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef
    (prod_nonneg (fun p hp => hg p (hsP hp)))

theorem plusProduct_le_full_euler (P B : Finset ℕ) (hBP : B ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) {g : ℕ → ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    {z K : ℝ} (hz : 2 < z) (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (hdim : DimensionOneProductBound P g K) :
    (∏ p ∈ B, (1 + g p)) ≤ (∏ p ∈ P, (1 - g p)) *
      (Real.log z / Real.log 2 * (1 + K / Real.log 2)) ^ 2 := by
  let V := ∏ p ∈ P, (1 - g p)
  let A := Real.log z / Real.log 2 * (1 + K / Real.log 2)
  have hV : 0 < V := prod_pos (fun p hp => sub_pos.mpr (hg p hp).2)
  have hfilter : P.filter
      (fun p : ℕ => p.Prime ∧ (2 : ℝ) ≤ p ∧ (p : ℝ) < z) = P := by
    apply filter_eq_self.mpr
    intro p hp
    exact ⟨hP p hp, by exact_mod_cast (hP p hp).two_le, hcut p hp⟩
  have hA : V⁻¹ ≤ A := by
    have h := hdim 2 z le_rfl hz
    rw [hfilter, prod_inv_distrib] at h
    exact h
  have hplus : (∏ p ∈ B, (1 + g p)) ≤ ∏ p ∈ P, (1 + g p) := by
    apply prod_le_prod_of_subset_of_one_le hBP
    · intro p hp
      linarith [(hg p (hBP hp)).1]
    · intro p hp _
      linarith [(hg p hp).1]
  have hprod : (∏ p ∈ P, (1 + g p)) * V ≤ 1 := by
    rw [show V = ∏ p ∈ P, (1 - g p) from rfl, ← prod_mul_distrib]
    exact prod_le_one
      (fun p hp => mul_nonneg (by linarith [(hg p hp).1])
        (sub_nonneg.mpr (hg p hp).2.le))
      (fun p _ => by nlinarith [sq_nonneg (g p)])
  have hAV : 1 ≤ A * V := (inv_le_iff_one_le_mul₀ hV).mp hA
  have hpow : 1 ≤ (A * V) ^ 2 := one_le_pow₀ hAV
  apply hplus.trans
  apply (mul_le_mul_iff_left₀ hV).mp
  nlinarith [show (A * V) ^ 2 = V * (V * A ^ 2) by ring]

#print axioms euler_truncation_ratio
#print axioms signedFamilyDensity_abs_le_plusProduct
#print axioms plusProduct_le_full_euler

end MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity
