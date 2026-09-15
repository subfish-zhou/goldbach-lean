import MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalytic

/-!
# The actual rough boundary mass

A failed full-product or parity-qualified cubic-prefix test supplies one
distinguished prime. Its complementary prefix and suffix are kept disjoint
until their weight factors exactly. Only then are both subsets summed freely.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset SmallRosser
open scoped Classical

namespace BoundaryAnalytic

theorem product_crossing_window {D a : ℝ} {b : ℕ → ℝ}
    {A : Finset ℕ} {p n : ℕ} (hD : 0 < D) (ha : 0 < a)
    (hb : ∀ q ∈ A, 0 < b q) (hp : p ∈ A)
    (hlo : (∏ q ∈ A, b q) * b p ^ n < D)
    (hhi : D ≤ (∏ q ∈ A, b q ^ a) * (b p ^ a) ^ n) :
    Window D a (∑ q ∈ A.erase p, Real.log (b q)) (n + 1) b p := by
  have hbp := hb p hp
  have hprod : 0 < ∏ q ∈ A, b q := prod_pos hb
  have hprod' : 0 < ∏ q ∈ A, b q ^ a :=
    prod_pos (fun q hq => Real.rpow_pos_of_pos (hb q hq) _)
  have hl := Real.log_lt_log (mul_pos hprod (pow_pos hbp _)) hlo
  have hh := Real.log_le_log hD hhi
  rw [Real.log_mul (ne_of_gt hprod) (ne_of_gt (pow_pos hbp _)),
    Real.log_prod (fun q hq => ne_of_gt (hb q hq)), Real.log_pow] at hl
  rw [Real.log_mul (ne_of_gt hprod')
      (ne_of_gt (pow_pos (Real.rpow_pos_of_pos hbp a) _)),
    Real.log_prod (fun q hq => ne_of_gt (Real.rpow_pos_of_pos (hb q hq) a)),
    Real.log_pow, Real.log_rpow hbp] at hh
  have heq : (∑ q ∈ A, Real.log (b q ^ a)) =
      a * ∑ q ∈ A, Real.log (b q) := by
    rw [mul_sum]
    exact sum_congr rfl (fun q hq => Real.log_rpow (hb q hq) _)
  rw [heq] at hh
  have hs := sum_erase_add A (fun q => Real.log (b q)) hp
  unfold Window
  constructor
  · apply (div_le_iff₀ ha).mpr
    nlinarith
  · nlinarith

/-- This extraction uses the exact strict crossing theorem. Parity is
discarded only after an actual failed cubic test has supplied its prime. -/
theorem crossing_witness {upper : Bool} {D a : ℝ} {b : ℕ → ℝ}
    {s : Finset ℕ} (hD : 1 < D) (ha : 0 < a)
    (hb : ∀ p ∈ s, 0 < b p)
    (hc : RoughBoundaryCrossing upper b (fun p => b p ^ a) D s) :
    ∃ k ∈ ({1, 3} : Finset ℕ), ∃ A ⊆ s, ∃ p ∈ A,
      Window D a (∑ q ∈ A.erase p, Real.log (b q)) k b p := by
  obtain ⟨_, hcross⟩ := (roughBoundaryCrossing_iff _ _ _ _ _).mp hc
  rcases hcross with hfull | ⟨p, hp, _, hlo, hhi⟩
  · have hs : s.Nonempty := by
      by_contra hn
      have he := not_nonempty_iff_eq_empty.mp hn
      simp only [he, prod_empty] at hfull
      linarith
    obtain ⟨p, hp⟩ := hs
    refine ⟨1, by simp, s, subset_rfl, p, hp, ?_⟩
    simpa using product_crossing_window (n := 0) (by linarith) ha hb hp
      (by simpa using hfull.1) (by simpa using hfull.2)
  · refine ⟨3, by simp, s.filter (fun q => p ≤ q), filter_subset _ _, p,
      mem_filter.mpr ⟨hp, le_rfl⟩, ?_⟩
    convert product_crossing_window (n := 2) (by linarith) ha
      (fun q hq => hb q (mem_filter.mp hq).1) (mem_filter.mpr ⟨hp, le_rfl⟩) hlo hhi
      using 1
    norm_num

abbrev Index := ℕ × Finset ℕ × Finset ℕ × ℕ

def reconstruct (i : Index) : Finset ℕ :=
  insert i.2.2.2 (i.2.1 ∪ i.2.2.1)

def indices (R : Finset ℕ) : Finset Index :=
  ({1, 3} : Finset ℕ) ×ˢ (R.powerset ×ˢ (R.powerset ×ˢ R))

def Valid (D a : ℝ) (b : ℕ → ℝ) (i : Index) : Prop :=
  Disjoint i.2.1 i.2.2.1 ∧ i.2.2.2 ∉ i.2.1 ∪ i.2.2.1 ∧
    Window D a (∑ q ∈ i.2.1, Real.log (b q)) i.1 b i.2.2.2

theorem boundary_subset_image (R : Finset ℕ) {upper : Bool} {D a : ℝ}
    {b : ℕ → ℝ} (hD : 1 < D) (ha : 0 < a)
    (hb : ∀ p ∈ R, 0 < b p) :
    roughBoundarySets upper b (fun p => b p ^ a) D R ⊆
      ((indices R).filter (Valid D a b)).image reconstruct := by
  intro s hs
  obtain ⟨hsR, hc⟩ := mem_filter.mp hs
  have hsR' := mem_powerset.mp hsR
  obtain ⟨k, hk, A, hAs, p, hp, hw⟩ :=
    crossing_witness hD ha (fun p hp => hb p (hsR' hp)) hc
  let S := A.erase p
  let T := s \ A
  have hSR : S ⊆ R := (erase_subset _ _).trans (hAs.trans hsR')
  have hTR : T ⊆ R := sdiff_subset.trans hsR'
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro q hqS hqT
    exact (mem_sdiff.mp hqT).2 (mem_of_mem_erase hqS)
  have hpnot : p ∉ S ∪ T := by simp [S, T, hp]
  have hrecon : reconstruct (k, S, T, p) = s := by
    unfold reconstruct
    change insert p (A.erase p ∪ (s \ A)) = s
    rw [← insert_union, insert_erase hp, union_sdiff_of_subset hAs]
  apply mem_image.mpr
  refine ⟨(k, S, T, p), mem_filter.mpr ⟨?_, hdis, hpnot, hw⟩, hrecon⟩
  exact mem_product.mpr ⟨hk, mem_product.mpr ⟨mem_powerset.mpr hSR,
    mem_product.mpr ⟨mem_powerset.mpr hTR, hsR' (hAs hp)⟩⟩⟩

theorem reconstruct_subset {R : Finset ℕ} {i : Index} (hi : i ∈ indices R) :
    reconstruct i ⊆ R := by
  obtain ⟨_, hS, hT, hp⟩ : i.1 ∈ ({1, 3} : Finset ℕ) ∧
      i.2.1 ⊆ R ∧ i.2.2.1 ⊆ R ∧ i.2.2.2 ∈ R := by
    simpa only [indices, mem_product, mem_powerset] using hi
  exact insert_subset hp (union_subset hS hT)

theorem mass_le_window_sums (upper : Bool) (R : Finset ℕ) {D a : ℝ}
    {b g : ℕ → ℝ} (hD : 1 < D) (ha : 0 < a)
    (hb : ∀ p ∈ R, 0 < b p) (hg : ∀ p ∈ R, 0 ≤ g p) :
    roughBoundaryMass upper b (fun p => b p ^ a) D R g ≤
      ∑ k ∈ ({1, 3} : Finset ℕ), ∑ S ∈ R.powerset, ∑ T ∈ R.powerset,
        (∏ q ∈ S, g q) * (∏ q ∈ T, g q) *
          ∑ p ∈ R.filter (Window D a (∑ q ∈ S, Real.log (b q)) k b), g p := by
  let I := (indices R).filter (Valid D a b)
  let w := fun i : Index => g i.2.2.2 * (∏ q ∈ i.2.1, g q) *
    ∏ q ∈ i.2.2.1, g q
  have hnon : ∀ s ∈ I.image reconstruct, 0 ≤ ∏ p ∈ s, g p := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
    exact prod_nonneg (fun p hp => hg p (reconstruct_subset (mem_filter.mp hi).1 hp))
  calc
    _ ≤ ∑ s ∈ I.image reconstruct, ∏ p ∈ s, g p :=
      sum_le_sum_of_subset_of_nonneg (boundary_subset_image R hD ha hb)
        (fun s hs _ => hnon s hs)
    _ ≤ ∑ i ∈ I, ∏ p ∈ reconstruct i, g p :=
      sum_image_le_of_nonneg hnon
    _ = ∑ i ∈ I, w i := by
      apply sum_congr rfl
      intro i hi
      obtain ⟨hdis, hp, _⟩ := (mem_filter.mp hi).2
      dsimp [w, reconstruct]
      rw [prod_insert hp, prod_union hdis]
      ring
    _ ≤ ∑ i ∈ indices R,
        if Window D a (∑ q ∈ i.2.1, Real.log (b q)) i.1 b i.2.2.2
        then w i else 0 := by
      rw [show I = (indices R).filter (Valid D a b) from rfl, sum_filter]
      apply sum_le_sum
      intro i hi
      have hw : 0 ≤ w i := by
        obtain ⟨_, hS, hT, hp⟩ : i.1 ∈ ({1, 3} : Finset ℕ) ∧
            i.2.1 ⊆ R ∧ i.2.2.1 ⊆ R ∧ i.2.2.2 ∈ R := by
          simpa only [indices, mem_product, mem_powerset] using hi
        exact mul_nonneg (mul_nonneg (hg _ hp)
          (prod_nonneg (fun p hp => hg p (hS hp))))
          (prod_nonneg (fun p hp => hg p (hT hp)))
      by_cases hv : Valid D a b i
      · simp only [hv, hv.2.2, if_true, le_refl]
      · simp only [hv, if_false]
        split_ifs <;> linarith
    _ = _ := by
      simp only [indices, sum_product]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro T _
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro p _
      dsimp [w]
      split_ifs <;> ring

/-- An Euler-weighted estimate of the actual boundary mass. There is no
slot count, powerset cardinality, or replacement by a different family. -/
theorem mass_le_dimensionOne (upper : Bool) (P R : Finset ℕ)
    {D ε K : ℝ} {b : ℕ → ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hR : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hb : ∀ p ∈ R, 1 ≤ b p ∧ b p ≤ (p : ℝ) ∧
      (p : ℝ) < b p ^ (1 + ε ^ 9))
    (hrough : ∀ p ∈ R, D ^ (ε ^ 2) ≤ (p : ℝ))
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    roughBoundaryMass upper b (fun p => b p ^ (1 + ε ^ 9)) D R g ≤
      2 * (∏ p ∈ R, (1 + g p)) ^ 2 *
        (3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D)) := by
  let B := 3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D)
  have hprod : ∀ S ∈ R.powerset, 0 ≤ ∏ p ∈ S, g p :=
    fun S hS => prod_nonneg (fun p hp => (hg p (hR (mem_powerset.mp hS hp))).1)
  calc
    _ ≤ ∑ k ∈ ({1, 3} : Finset ℕ), ∑ S ∈ R.powerset, ∑ T ∈ R.powerset,
        (∏ q ∈ S, g q) * (∏ q ∈ T, g q) *
          ∑ p ∈ R.filter (Window D (1 + ε ^ 9)
            (∑ q ∈ S, Real.log (b q)) k b), g p :=
      mass_le_window_sums upper R (by linarith) (by positivity)
        (fun p hp => lt_of_lt_of_le zero_lt_one (hb p hp).1)
        (fun p hp => (hg p (hR hp)).1)
    _ ≤ ∑ k ∈ ({1, 3} : Finset ℕ), ∑ S ∈ R.powerset, ∑ T ∈ R.powerset,
        (∏ q ∈ S, g q) * (∏ q ∈ T, g q) * B := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hprod S hS) (hprod T hT))
      apply window_sum_le P R hD hε hεsmall hlarge hK hR hP
        (sum_nonneg (fun p hp => Real.log_nonneg (hb p (mem_powerset.mp hS hp)).1))
        ?_ hb hrough hg hdim
      have hk' : k = 1 ∨ k = 3 := by simpa only [mem_insert, mem_singleton] using hk
      rcases hk' with rfl | rfl <;> norm_num
    _ = _ := by
      simp only [← sum_mul, ← mul_sum]
      rw [← prod_one_add]
      norm_num
      dsimp [B]
      ring

/-- Canonical geometric boxes on the original prime carrier and the same
dimension-one constant `K`. Both Rosser parities are covered. -/
theorem roughBoundaryMass_le_dimensionOne (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    roughBoundaryMass upper b (fun p => b p ^ (1 + ε ^ 9)) D R g ≤
      2 * (∏ p ∈ R, (1 + g p)) ^ 2 *
        (3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D)) := by
  dsimp only
  apply mass_le_dimensionOne upper P _ hD hε hεsmall hlarge hK
    sdiff_subset hP ?_ (fun p hp => CollisionAnalytic.rough_prime_lower P hP D ε hp)
    hg hdim
  intro p hp
  refine ⟨geometricLower_one_le (by linarith) (by positivity) _, ?_, ?_⟩
  · exact ((mem_geometricPrimeBox _ _ _ _ _ _).mp
      (geometricSieveLabel_mem P hP (by linarith) hε p hp)).2.2.1
  · exact geometricPrimeBox_upper P (by linarith) _ p
      (geometricSieveLabel_mem P hP (by linarith) hε p hp)

#print axioms crossing_witness
#print axioms boundary_subset_image
#check roughBoundaryMass_le_dimensionOne
#print axioms roughBoundaryMass_le_dimensionOne

end BoundaryAnalytic
end MathlibNt.SieveTheory.LiLiuPrereqWF
