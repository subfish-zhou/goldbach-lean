import MathlibNt.SieveTheory.LiLiuPrereqWFSignedDensity

/-!
# Finite comparison with the ordinary coarse Rosser density

The normalized signed family and the ordinary Rosser family use the same
prime subsets, level, multiplicative density, and parity. Their directed
discrepancy is supported on repeated lower endpoints and strict full-product
or parity-qualified cubic-prefix boundary crossings. Every coefficient
defect has magnitude at most one, not two.

These are finite quantitative comparisons. Estimates of the resulting pair
and boundary masses on the analytic scale, and the full coarse F/f estimate,
are not asserted here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset
open scoped Classical

/-- The ordinary coefficient at the same coarse level, without rounding. -/
noncomputable def ordinaryRoughSet (upper : Bool) (D : ℝ) (s : Finset ℕ) : ℝ :=
  if upper then SmallRosser.upperSetWeight D s else SmallRosser.setWeight D s

noncomputable def roughOrdinaryDensity (upper : Bool) (D : ℝ)
    (R : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ s ∈ R.powerset, ordinaryRoughSet upper D s * ∏ p ∈ s, g p

/-- Two distinct original prime slots have the same lower endpoint. -/
def RoughCollision (b : ℕ → ℝ) (s : Finset ℕ) : Prop :=
  ¬Set.InjOn b (↑s : Set ℕ)

/-- Lower endpoints pass every strict test, but upper endpoints fail one. -/
def RoughBoundaryCrossing (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (s : Finset ℕ) : Prop :=
  RoundedSupport upper b D s ∧ ¬RoundedSupport upper c D s

noncomputable def roughCollisionSets (b : ℕ → ℝ) (R : Finset ℕ) :
    Finset (Finset ℕ) :=
  R.powerset.filter (RoughCollision b)

noncomputable def roughBoundarySets (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (R : Finset ℕ) : Finset (Finset ℕ) :=
  R.powerset.filter (RoughBoundaryCrossing upper b c D)

noncomputable def roughCollisionMass (b : ℕ → ℝ) (R : Finset ℕ)
    (g : ℕ → ℝ) : ℝ :=
  ∑ s ∈ roughCollisionSets b R, ∏ p ∈ s, g p

noncomputable def roughBoundaryMass (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (R : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ s ∈ roughBoundarySets upper b c D R, ∏ p ∈ s, g p

/-- The crossing is an actual full-product or inclusive cubic-prefix
crossing. Equality belongs to the failed (upper-endpoint) side. -/
theorem roughBoundaryCrossing_iff (upper : Bool) (b c : ℕ → ℝ) (D : ℝ)
    (s : Finset ℕ) :
    RoughBoundaryCrossing upper b c D s ↔
      RoundedSupport upper b D s ∧
        (((∏ p ∈ s, b p) < D ∧ D ≤ ∏ p ∈ s, c p) ∨
          ∃ p ∈ s,
            (s.filter (fun q => p ≤ q)).card % 2 = (if upper then 1 else 0) ∧
            (∏ q ∈ s.filter (fun q => p ≤ q), b q) * b p ^ 2 < D ∧
            D ≤ (∏ q ∈ s.filter (fun q => p ≤ q), c q) * c p ^ 2) := by
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨hb, ?_⟩
    by_cases hprod : (∏ p ∈ s, c p) < D
    · have hbad : ¬RoundedSetAdmissible upper c D s :=
        fun h => hc ⟨hprod, h⟩
      simp only [RoundedSetAdmissible, not_forall, not_lt] at hbad
      obtain ⟨p, hp, hpar, hfail⟩ := hbad
      exact Or.inr ⟨p, hp, hpar, hb.2 p hp hpar, hfail⟩
    · exact Or.inl ⟨hb.1, le_of_not_gt hprod⟩
  · rintro ⟨hb, hbad⟩
    refine ⟨hb, ?_⟩
    intro hc
    rcases hbad with hprod | ⟨p, hp, hpar, _, hfail⟩
    · exact (not_lt_of_ge hprod.2) hc.1
    · exact (not_lt_of_ge hfail) (hc.2 p hp hpar)

theorem ordinaryRoughSet_eq_support (upper : Bool) (D : ℝ) (s : Finset ℕ) :
    ordinaryRoughSet upper D s =
      if RoundedSupport upper (fun p : ℕ => (p : ℝ)) D s then
        (if Even s.card then 1 else -1) else 0 := by
  cases upper <;>
    simp only [ordinaryRoughSet, Bool.false_eq_true, if_false, if_true,
      SmallRosser.setWeight, SmallRosser.upperSetWeight,
      roundedSupport_cast_lower_iff, roundedSupport_cast_upper_iff]

/-- Away from the two concrete bad sets the exact signed coefficients agree. -/
theorem normalizedSignedSet_eq_ordinaryRoughSet_of_good
    {upper : Bool} {b c : ℕ → ℝ} {D : ℝ} {s : Finset ℕ}
    (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbp : ∀ p ∈ s, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ s, (p : ℝ) ≤ c p)
    (hcollision : ¬RoughCollision b s)
    (hboundary : ¬RoughBoundaryCrossing upper b c D s) :
    normalizedSignedSet upper b c D s = ordinaryRoughSet upper D s := by
  have hinj : Set.InjOn b (↑s : Set ℕ) := not_not.mp hcollision
  have hbc : RoundedSupport upper b D s ↔ RoundedSupport upper c D s :=
    ⟨fun h => Classical.byContradiction (fun hc => hboundary ⟨h, hc⟩),
      roundedSupport_mono hb (fun p hp => (hbp p hp).trans (hpc p hp))⟩
  have hcast : RoundedSupport upper (fun p : ℕ => (p : ℝ)) D s ↔
      RoundedSupport upper b D s :=
    ⟨roundedSupport_mono hb hbp,
      fun h => roundedSupport_mono (fun p _ => Nat.cast_nonneg p) hpc (hbc.mp h)⟩
  rw [ordinaryRoughSet_eq_support, hcast]
  cases upper <;>
    simp only [normalizedSignedSet, Bool.false_eq_true, if_false, if_true,
      normalizedUpperSet, normalizedLowerSet, TightRoundedSupport, hinj, true_and,
      ← hbc] <;> split_ifs <;> rfl

/-- Both coefficients are either zero or the SAME parity sign. No enclosure
assumptions are needed for the bound one. -/
theorem normalizedSignedSet_abs_sub_le_one (upper : Bool) (b c : ℕ → ℝ)
    (D : ℝ) (s : Finset ℕ) :
    |normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s| ≤ 1 := by
  cases upper <;> by_cases heven : Even s.card <;>
    simp only [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet,
      ordinaryRoughSet, SmallRosser.upperSetWeight, SmallRosser.setWeight,
      Bool.false_eq_true, if_false, if_true, heven] <;> split_ifs <;> norm_num

theorem normalizedSignedSet_directed_nonneg
    {upper : Bool} {b c : ℕ → ℝ} {D : ℝ} {s : Finset ℕ}
    (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbp : ∀ p ∈ s, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ s, (p : ℝ) ≤ c p) :
    0 ≤ (if upper then 1 else -1) *
      (normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s) := by
  cases upper <;>
    simp only [normalizedSignedSet, ordinaryRoughSet, Bool.false_eq_true,
      if_false, if_true, one_mul, neg_one_mul]
  · linarith [normalizedLowerSet_le_setWeight hb hbp hpc (D := D)]
  · exact sub_nonneg.mpr (upperSetWeight_le_normalizedUpperSet hb hbp hpc)

theorem normalizedSignedSet_abs_sub_le_bad
    {upper : Bool} {b c : ℕ → ℝ} {D : ℝ} {s : Finset ℕ}
    (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbp : ∀ p ∈ s, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ s, (p : ℝ) ≤ c p) :
    |normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s| ≤
      (if RoughCollision b s then 1 else 0) +
        (if RoughBoundaryCrossing upper b c D s then 1 else 0) := by
  have hunit := normalizedSignedSet_abs_sub_le_one upper b c D s
  by_cases hc : RoughCollision b s <;>
    by_cases hx : RoughBoundaryCrossing upper b c D s <;>
    simp only [hc, hx, if_true, if_false]
  · linarith
  · linarith
  · linarith
  · rw [normalizedSignedSet_eq_ordinaryRoughSet_of_good hb hbp hpc hc hx]
    norm_num

/-- Quantitative comparison to the SAME ordinary coarse density: only
collisions and strict boundary crossings pay for the directed gap. -/
theorem roughSignedDensity_comparison
    (upper : Bool) (b c : ℕ → ℝ) (D : ℝ) (R : Finset ℕ) (g : ℕ → ℝ)
    (hb : ∀ p ∈ R, 0 ≤ b p)
    (hbp : ∀ p ∈ R, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ R, (p : ℝ) ≤ c p)
    (hg : ∀ p ∈ R, 0 ≤ g p) :
    0 ≤ (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ∧
      (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ≤
        roughCollisionMass b R g + roughBoundaryMass upper b c D R g := by
  have hid :
      (if upper then (1 : ℝ) else -1) *
          (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) =
        ∑ s ∈ R.powerset, ((if upper then 1 else -1) *
          (normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s)) *
          ∏ p ∈ s, g p := by
    simp only [roughSignedDensity, roughOrdinaryDensity, ← Finset.sum_sub_distrib,
      Finset.mul_sum, sub_mul, mul_assoc]
  rw [hid]
  have hprod : ∀ s ∈ R.powerset, 0 ≤ ∏ p ∈ s, g p :=
    fun s hs => Finset.prod_nonneg (fun p hp => hg p (mem_powerset.mp hs hp))
  constructor
  · apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg
      (normalizedSignedSet_directed_nonneg
        (fun p hp => hb p (mem_powerset.mp hs hp))
        (fun p hp => hbp p (mem_powerset.mp hs hp))
        (fun p hp => hpc p (mem_powerset.mp hs hp))) (hprod s hs)
  · simp only [roughCollisionMass, roughBoundaryMass, roughCollisionSets,
      roughBoundarySets, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have hbad := normalizedSignedSet_abs_sub_le_bad
      (upper := upper) (D := D)
      (fun p hp => hb p (mem_powerset.mp hs hp))
      (fun p hp => hbp p (mem_powerset.mp hs hp))
      (fun p hp => hpc p (mem_powerset.mp hs hp))
    have hsign : (if upper then (1 : ℝ) else -1) *
        (normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s) ≤
        |normalizedSignedSet upper b c D s - ordinaryRoughSet upper D s| := by
      cases upper <;> simp only [Bool.false_eq_true, if_false, if_true,
        one_mul, neg_one_mul]
      · exact neg_le_abs _
      · exact le_abs_self _
    convert mul_le_mul_of_nonneg_right (hsign.trans hbad) (hprod s hs) using 1
    simp only [add_mul, ite_mul, one_mul, zero_mul]

theorem roughSignedDensity_abs_sub_le
    (upper : Bool) (b c : ℕ → ℝ) (D : ℝ) (R : Finset ℕ) (g : ℕ → ℝ)
    (hb : ∀ p ∈ R, 0 ≤ b p)
    (hbp : ∀ p ∈ R, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ R, (p : ℝ) ≤ c p)
    (hg : ∀ p ∈ R, 0 ≤ g p) :
    |roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g| ≤
      roughCollisionMass b R g + roughBoundaryMass upper b c D R g := by
  obtain ⟨h0, h1⟩ := roughSignedDensity_comparison upper b c D R g hb hbp hpc hg
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true,
    one_mul, neg_one_mul] at *
  · rw [abs_of_nonpos (by linarith)]
    exact h1
  · rw [abs_of_nonneg h0]
    exact h1

/-- Removing a compulsory subset leaves freely chosen complementary slots. -/
theorem sum_powerset_superset_prod (R A : Finset ℕ) (hA : A ⊆ R)
    (g : ℕ → ℝ) :
    (∑ s ∈ R.powerset.filter (fun s => A ⊆ s), ∏ p ∈ s, g p) =
      (∏ p ∈ A, g p) * ∏ p ∈ R \ A, (1 + g p) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_bij (fun s _ => s \ A)
  · intro s hs
    exact mem_powerset.mpr
      (fun p hp => mem_sdiff.mpr
        ⟨mem_powerset.mp (mem_filter.mp hs).1 (mem_sdiff.mp hp).1,
          (mem_sdiff.mp hp).2⟩)
  · intro s hs t ht heq
    calc
      s = s \ A ∪ A := (sdiff_union_of_subset (mem_filter.mp hs).2).symm
      _ = t \ A ∪ A := congrArg (fun u => u ∪ A) heq
      _ = t := sdiff_union_of_subset (mem_filter.mp ht).2
  · intro t ht
    have hsub := mem_powerset.mp ht
    have hdis : Disjoint t A := disjoint_left.mpr
      (fun p hp hpa => (mem_sdiff.mp (hsub hp)).2 hpa)
    refine ⟨t ∪ A, mem_filter.mpr ⟨mem_powerset.mpr ?_, subset_union_right⟩, ?_⟩
    · exact union_subset
        (fun p hp => (mem_sdiff.mp (hsub hp)).1) hA
    · exact union_sdiff_cancel_right hdis
  · intro s hs
    simpa only [mul_comm] using (Finset.prod_sdiff (f := g) (mem_filter.mp hs).2).symm

/-- Exact pair-containing powerset mass, with no division and no positivity
assumptions; zero prime densities are allowed. -/
theorem sum_powerset_contains_pair_prod (R : Finset ℕ) (g : ℕ → ℝ)
    {p q : ℕ} (hp : p ∈ R) (hq : q ∈ R) (hpq : p ≠ q) :
    (∑ s ∈ R.powerset.filter (fun s => p ∈ s ∧ q ∈ s), ∏ r ∈ s, g r) =
      g p * g q * ∏ r ∈ R \ {p, q}, (1 + g r) := by
  have hpair : ({p, q} : Finset ℕ) ⊆ R :=
    insert_subset_iff.mpr ⟨hp, singleton_subset_iff.mpr hq⟩
  simpa only [insert_subset_iff, singleton_subset_iff, Finset.prod_pair hpq] using
    sum_powerset_superset_prod R {p, q} hpair g

theorem roughCollision_iff_exists_pair (b : ℕ → ℝ) (s : Finset ℕ) :
    RoughCollision b s ↔ ∃ p ∈ s, ∃ q ∈ s, p < q ∧ b p = b q := by
  constructor
  · intro hc
    by_contra hn
    apply hc
    intro p hp q hq heq
    by_contra hpq
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact hn ⟨p, hp, q, hq, hlt, heq⟩
    · exact hn ⟨q, hq, p, hp, hgt, heq.symm⟩
  · rintro ⟨p, hp, q, hq, hpq, heq⟩ hinj
    exact (ne_of_lt hpq) (hinj hp hq heq)

noncomputable def roughCollisionPairMass (b : ℕ → ℝ) (R : Finset ℕ)
    (g : ℕ → ℝ) : ℝ :=
  ∑ p ∈ R, ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q), g p * g q

/-- A weighted union bound over distinct same-box pairs. This retains the
quadratic pair factor rather than bounding by a powerset cardinality. -/
theorem roughCollisionMass_le_pair_euler (b : ℕ → ℝ) (R : Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ p ∈ R, 0 ≤ g p) :
    roughCollisionMass b R g ≤
      (∏ p ∈ R, (1 + g p)) * roughCollisionPairMass b R g := by
  have hprod : ∀ s ∈ R.powerset, 0 ≤ ∏ p ∈ s, g p :=
    fun s hs => Finset.prod_nonneg (fun p hp => hg p (mem_powerset.mp hs hp))
  calc
    roughCollisionMass b R g =
        ∑ s ∈ R.powerset, if RoughCollision b s then ∏ p ∈ s, g p else 0 := by
      simp only [roughCollisionMass, roughCollisionSets, Finset.sum_filter]
    _ ≤ ∑ s ∈ R.powerset, ∑ p ∈ R,
        ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q),
          if p ∈ s ∧ q ∈ s then ∏ r ∈ s, g r else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      have hw := hprod s hs
      have hterm : ∀ p q : ℕ,
          0 ≤ (if p ∈ s ∧ q ∈ s then ∏ r ∈ s, g r else 0) :=
        fun _ _ => by split_ifs <;> positivity
      by_cases hc : RoughCollision b s
      · rw [if_pos hc]
        obtain ⟨p, hp, q, hq, hpq, heq⟩ :=
          (roughCollision_iff_exists_pair b s).mp hc
        have hqR : q ∈ R.filter (fun q => p < q ∧ b p = b q) :=
          mem_filter.mpr ⟨mem_powerset.mp hs hq, hpq, heq⟩
        have hinner := Finset.single_le_sum (fun q _ => hterm p q) hqR
        have houter := Finset.single_le_sum
          (f := fun p => ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q),
            if p ∈ s ∧ q ∈ s then ∏ r ∈ s, g r else 0)
          (fun p _ => Finset.sum_nonneg (fun q _ => hterm p q)) (mem_powerset.mp hs hp)
        apply le_trans _ houter
        simpa only [hp, hq, and_self, if_true] using hinner
      · rw [if_neg hc]
        exact Finset.sum_nonneg
          (fun p _ => Finset.sum_nonneg (fun q _ => hterm p q))
    _ = ∑ p ∈ R, ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q),
        ∑ s ∈ R.powerset.filter (fun s => p ∈ s ∧ q ∈ s), ∏ r ∈ s, g r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ p ∈ R, ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q),
        g p * g q * ∏ r ∈ R \ {p, q}, (1 + g r) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact sum_powerset_contains_pair_prod R g hp (mem_filter.mp hq).1
        (ne_of_lt (mem_filter.mp hq).2.1)
    _ ≤ ∑ p ∈ R, ∑ q ∈ R.filter (fun q => p < q ∧ b p = b q),
        (∏ r ∈ R, (1 + g r)) * (g p * g q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hE : (∏ r ∈ R \ {p, q}, (1 + g r)) ≤ ∏ r ∈ R, (1 + g r) :=
        Finset.prod_le_prod_of_subset_of_one_le sdiff_subset
          (fun r hr => by linarith [hg r (mem_sdiff.mp hr).1])
          (fun r hr _ => by linarith [hg r hr])
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hE (mul_nonneg (hg p hp) (hg q (mem_filter.mp hq).1))
    _ = (∏ p ∈ R, (1 + g p)) * roughCollisionPairMass b R g := by
      simp only [roughCollisionPairMass, Finset.mul_sum]

/-- The remaining finite error consists of a same-box pair mass times the
rough Euler product and the strict boundary mass. -/
theorem roughSignedDensity_comparison_pair_bound
    (upper : Bool) (b c : ℕ → ℝ) (D : ℝ) (R : Finset ℕ) (g : ℕ → ℝ)
    (hb : ∀ p ∈ R, 0 ≤ b p)
    (hbp : ∀ p ∈ R, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ R, (p : ℝ) ≤ c p)
    (hg : ∀ p ∈ R, 0 ≤ g p) :
    0 ≤ (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ∧
      (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ≤
        (∏ p ∈ R, (1 + g p)) * roughCollisionPairMass b R g +
          roughBoundaryMass upper b c D R g := by
  obtain ⟨h0, h1⟩ := roughSignedDensity_comparison upper b c D R g hb hbp hpc hg
  exact ⟨h0, h1.trans (add_le_add (roughCollisionMass_le_pair_euler b R g hg) le_rfl)⟩

/-- Canonical geometric endpoints discharge the enclosure assumptions at
the original D and epsilon; no new coarse level or box family is chosen. -/
theorem roughSignedDensity_canonical_comparison
    (upper : Bool) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 1 < D) (hε : 0 < ε) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P \ geometricSmallPrimes P D ε, 0 ≤ g p) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    let c := fun p => b p ^ (1 + ε ^ 9)
    0 ≤ (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ∧
      (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ≤
        roughCollisionMass b R g + roughBoundaryMass upper b c D R g := by
  dsimp only
  apply roughSignedDensity_comparison
  · intro p _
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (geometricLower_one_le hD.le (pow_nonneg hε.le _) _)
  · intro p hp
    exact ((mem_geometricPrimeBox _ _ _ _ _ _).mp
      (geometricSieveLabel_mem P hP hD hε p hp)).2.2.1
  · intro p hp
    exact (geometricPrimeBox_upper P (by linarith) _ p
      (geometricSieveLabel_mem P hP hD hε p hp)).le
  · exact hg

theorem roughSignedDensity_canonical_pair_bound
    (upper : Bool) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 1 < D) (hε : 0 < ε) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P \ geometricSmallPrimes P D ε, 0 ≤ g p) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    let c := fun p => b p ^ (1 + ε ^ 9)
    0 ≤ (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ∧
      (if upper then 1 else -1) *
        (roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g) ≤
        (∏ p ∈ R, (1 + g p)) * roughCollisionPairMass b R g +
          roughBoundaryMass upper b c D R g := by
  dsimp only
  obtain ⟨h0, h1⟩ := roughSignedDensity_canonical_comparison upper P hP hD hε g hg
  exact ⟨h0, h1.trans (add_le_add (roughCollisionMass_le_pair_euler _ _ g hg) le_rfl)⟩

#check roughBoundaryCrossing_iff
#check normalizedSignedSet_eq_ordinaryRoughSet_of_good
#check normalizedSignedSet_abs_sub_le_one
#check roughSignedDensity_comparison
#check sum_powerset_contains_pair_prod
#check roughCollisionMass_le_pair_euler
#check roughSignedDensity_comparison_pair_bound
#check roughSignedDensity_canonical_comparison
#check roughSignedDensity_canonical_pair_bound
#print axioms roughBoundaryCrossing_iff
#print axioms normalizedSignedSet_eq_ordinaryRoughSet_of_good
#print axioms normalizedSignedSet_abs_sub_le_one
#print axioms roughSignedDensity_comparison
#print axioms roughSignedDensity_abs_sub_le
#print axioms sum_powerset_superset_prod
#print axioms sum_powerset_contains_pair_prod
#print axioms roughCollision_iff_exists_pair
#print axioms roughCollisionMass_le_pair_euler
#print axioms roughSignedDensity_comparison_pair_bound
#print axioms roughSignedDensity_canonical_comparison
#print axioms roughSignedDensity_canonical_pair_bound

end MathlibNt.SieveTheory.LiLiuPrereqWF
