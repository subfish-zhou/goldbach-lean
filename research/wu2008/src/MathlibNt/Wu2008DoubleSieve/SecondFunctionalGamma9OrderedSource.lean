import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource

namespace Wu2008DoubleSieve
open Finset
open scoped Classical

namespace Gamma9OrderedSource

theorem tuples_three (P : Finset ℕ) :
    secondFunctionalMotherTuples P 3 =
      (orderedTriples P).image (fun t => [t.1, t.2.1, t.2.2]) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem P 3 l).mp hl
    obtain ⟨p, q, r, rfl⟩ := List.length_eq_three.mp hlen
    refine mem_image.mpr ⟨(p,q,r), ?_, rfl⟩
    simp only [orderedTriples, mem_filter, mem_product]
    have hpq : p < q := (List.pairwise_cons.mp hord).1 q (by simp)
    have hqr : q < r := (List.pairwise_cons.mp (List.pairwise_cons.mp hord).2).1 r (by simp)
    exact ⟨⟨hmem p (by simp), hmem q (by simp), hmem r (by simp)⟩, hpq, hqr⟩
  · rintro hl
    obtain ⟨⟨p,q,r⟩, ht, rfl⟩ := mem_image.mp hl
    obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
      (p ∈ P ∧ q ∈ P ∧ r ∈ P) ∧ p < q ∧ q < r from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
    rw [secondFunctionalMother_tuple_mem]
    simp [hp, hq, hr, hpq, hqr, hpq.trans hqr]

theorem sum_tuples_three (P : Finset ℕ) (F : List ℕ → ℝ) :
    (∑ l ∈ secondFunctionalMotherTuples P 3, F l) =
      ∑ t ∈ orderedTriples P, F [t.1, t.2.1, t.2.2] := by
  rw [tuples_three, sum_image]
  intro x _ y _ h
  obtain ⟨p,q,r⟩ := x
  obtain ⟨u,v,w⟩ := y
  simpa only [List.cons.injEq, and_true, Prod.mk.injEq] using h

theorem prefix_three (N d p q r : ℕ) :
    ((secondFunctionalMotherPrefixCarrier N d [p,q,r]).card : ℝ) =
      (sourceSieveCount N (d*p*q*r) (d*p*N) q : ℝ) := by
  simp [fourthRowMotherPrefixCarrier, sourceSieveCount, mul_assoc]

theorem colour_partition (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) (v : ℝ) :
    (if [x,y,z] = [1,1,1] then v else 0) +
    (if [x,y,z] = [1,1,2] then v else 0) +
    (if [x,y,z] = [1,2,2] then v else 0) +
    (if [x,y,z] = [2,2,2] then v else 0) =
      if 1 ≤ x ∧ z ≤ 2 then v else 0 := by
  simp only [List.cons.injEq, and_true]
  split_ifs <;> first | omega | ring

theorem triples_window (M : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    orderedTriples (primeWindow M b e) =
      (orderedTriples (primeWindow M a f)).filter (fun t =>
        1 ≤ secondFunctionalMotherColour b c e t.1 ∧
          secondFunctionalMotherColour b c e t.2.2 ≤ 2) := by
  ext ⟨p,q,r⟩
  have hc1 : 1 ≤ secondFunctionalMotherColour b c e p ↔ b ≤ (p : ℝ) := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, secondFunctionalMother_colour_zero, not_lt]
  simp only [mem_filter, orderedTriples, mem_product, mem_primeWindow, hc1,
    secondFunctionalMother_colour_mid hbc hce]
  have hpq : p < q → (p : ℝ) < q := fun h => by exact_mod_cast h
  have hqr : q < r → (q : ℝ) < r := fun h => by exact_mod_cast h
  constructor
  · rintro ⟨⟨⟨hp,hpM,hpb,hpe⟩, ⟨hq,hqM,hqb,hqe⟩, hr,hrM,hrb,hre⟩, hpq',hqr'⟩
    exact ⟨⟨⟨⟨hp,hpM,hab.trans hpb,hpe.trans_le hef⟩,
      ⟨hq,hqM,hab.trans hqb,hqe.trans_le hef⟩,
      hr,hrM,hab.trans hrb,hre.trans_le hef⟩,hpq',hqr'⟩,hpb,hre⟩
  · rintro ⟨⟨⟨⟨hp,hpM,_,_⟩,⟨hq,hqM,_,_⟩,hr,hrM,_,_⟩,hpq',hqr'⟩,hpb,hre⟩
    exact ⟨⟨⟨hp,hpM,hpb,(hpq hpq').trans ((hqr hqr').trans hre)⟩,
      ⟨hq,hqM,hpb.trans (hpq hpq').le,(hqr hqr').trans hre⟩,
      hr,hrM,hpb.trans ((hpq hpq').trans (hqr hqr')).le,hre⟩,hpq',hqr'⟩

end Gamma9OrderedSource

/-- The four monotone colour words partition exactly the original [b,e) source. -/
theorem secondFunctionalMother_gamma9_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 9 =
      ∑ t ∈ orderedTriples (primeWindow M b e),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three, ← sum_add_distrib]
  rw [Gamma9OrderedSource.triples_window M hab hbc hce hef, sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨_,_,_⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  simpa only [add_assoc] using Gamma9OrderedSource.colour_partition
    (secondFunctionalMotherColour b c e t.1)
    (secondFunctionalMotherColour b c e t.2.1)
    (secondFunctionalMotherColour b c e t.2.2)
    (secondFunctionalMother_colour_monotone b c e hpq.le)
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ)

end Wu2008DoubleSieve
