import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9OrderedSource

namespace Wu2008DoubleSieve
open Finset
open scoped Classical

namespace LowerTripleOrderedSource

theorem colour_one {b c e : ℝ} (hbc : b ≤ c) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 1 ↔ b ≤ (p : ℝ) ∧ (p : ℝ) < c := by
  have h0 := secondFunctionalMother_colour_zero b c e p
  have h1 := secondFunctionalMother_colour_low hbc e p
  constructor
  · intro h
    exact ⟨not_lt.mp (fun hn => by have := h0.mpr hn; omega), h1.mp (by omega)⟩
  · rintro ⟨hb, hc⟩
    have := h1.mpr hc
    have hn : secondFunctionalMotherColour b c e p ≠ 0 := fun h => (not_lt.mpr hb) (h0.mp h)
    omega

theorem colour_le_three (b c e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p ≤ 3 := by
  unfold secondFunctionalMotherColour
  split_ifs <;> omega

theorem colour_three {b c e : ℝ} (hbc : b ≤ c) (hce : c ≤ e) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 3 ↔ e ≤ (p : ℝ) := by
  rw [← not_lt, ← secondFunctionalMother_colour_mid hbc hce p]
  have := colour_le_three b c e p
  omega

theorem colour_high {b c e : ℝ} (hbc : b ≤ c) (p : ℕ) :
    2 ≤ secondFunctionalMotherColour b c e p ↔ c ≤ (p : ℝ) := by
  have h := not_congr (secondFunctionalMother_colour_low hbc e p)
  simpa only [not_le, Nat.lt_iff_add_one_le, not_lt] using h

theorem partition10 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [1,1,2] then v else 0) +
    (if [x,y,z] = [1,1,3] then v else 0) = if x = 1 ∧ y = 1 ∧ 2 ≤ z then v else 0 := by
  simp only [List.cons.injEq, and_true]
  split_ifs <;> first | omega | ring

theorem partition11 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [1,2,2] then v else 0) = if x = 1 ∧ y = 2 ∧ z = 2 then v else 0 := by
  simp only [List.cons.injEq, and_true]

theorem partition12 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [0,0,3] then v else 0) = if x = 0 ∧ y = 0 ∧ z = 3 then v else 0 := by
  simp only [List.cons.injEq, and_true]

theorem partition13 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [0,1,2] then v else 0) +
    (if [x,y,z] = [0,1,3] then v else 0) = if x = 0 ∧ y = 1 ∧ 2 ≤ z then v else 0 := by
  simp only [List.cons.injEq, and_true]
  split_ifs <;> first | omega | ring

theorem partition14 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [0,2,2] then v else 0) +
    (if [x,y,z] = [0,2,3] then v else 0) +
    (if [x,y,z] = [0,3,3] then v else 0) = if x = 0 ∧ 2 ≤ y ∧ 2 ≤ z then v else 0 := by
  simp only [List.cons.injEq, and_true]
  split_ifs <;> first | omega | ring

theorem partition15 (x y z : ℕ) (_hyz : y ≤ z) (_hz : z ≤ 3) (v : ℝ) :
    (if [x,y,z] = [1,2,3] then v else 0) = if x = 1 ∧ y = 2 ∧ z = 3 then v else 0 := by
  simp only [List.cons.injEq, and_true]

end LowerTripleOrderedSource


/-- Original Gamma10, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma10_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (_hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 10 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          b ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < c ∧
          b ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < c ∧
          c ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < f),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three, ← sum_add_distrib]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [LowerTripleOrderedSource.partition10 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [LowerTripleOrderedSource.colour_one hbc,
    LowerTripleOrderedSource.colour_high hbc,
    hrf,
    and_true,
    and_assoc]

/-- Original Gamma11, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma11_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (_hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 11 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          b ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < c ∧
          c ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < e ∧
          c ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < e),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [LowerTripleOrderedSource.partition11 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [LowerTripleOrderedSource.colour_one hbc,
    secondFunctionalMother_colour_two hbc,
    and_assoc]

/-- Original Gamma12, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma12_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 12 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          a ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < b ∧
          a ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < b ∧
          e ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < f),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [LowerTripleOrderedSource.partition12 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [secondFunctionalMother_colour_zero,
    LowerTripleOrderedSource.colour_three hbc hce,
    hpa,
    hqa,
    hrf,
    true_and,
    and_true]

/-- Original Gamma13, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma13_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (_hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 13 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          a ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < b ∧
          b ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < c ∧
          c ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < f),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three, ← sum_add_distrib]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [LowerTripleOrderedSource.partition13 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [secondFunctionalMother_colour_zero,
    LowerTripleOrderedSource.colour_one hbc,
    LowerTripleOrderedSource.colour_high hbc,
    hpa,
    hrf,
    true_and,
    and_true,
    and_assoc]

/-- Original Gamma14, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma14_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (_hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 14 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          a ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < b ∧
          c ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < f ∧
          c ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < f),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three, ← sum_add_distrib]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [← add_assoc, LowerTripleOrderedSource.partition14 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [secondFunctionalMother_colour_zero,
    LowerTripleOrderedSource.colour_high hbc,
    hpa,
    hqf,
    hrf,
    true_and,
    and_true]

/-- Original Gamma15, preserving strict order, original window and prefix mask. -/
theorem secondFunctionalMother_gamma15_ordered_source (N d M : ℕ) {a b c e f : ℝ}
    (_hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (_hef : e ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 15 =
      ∑ t ∈ (orderedTriples (primeWindow M a f)).filter (fun t =>
          b ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < c ∧
          c ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) < e ∧
          e ≤ (t.2.2 : ℝ) ∧ (t.2.2 : ℝ) < f),
        (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℝ) := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    secondFunctionalMotherPrefixTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [Gamma9OrderedSource.sum_tuples_three]
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  obtain ⟨⟨hp,hq,hr⟩, hpq,hqr⟩ := (show
    (t.1 ∈ primeWindow M a f ∧ t.2.1 ∈ primeWindow M a f ∧
      t.2.2 ∈ primeWindow M a f) ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 from by
        simpa only [orderedTriples, mem_filter, mem_product] using ht)
  obtain ⟨_,_,hpa,hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨_,_,hqa,hqf⟩ := mem_primeWindow.mp hq
  obtain ⟨_,_,hra,hrf⟩ := mem_primeWindow.mp hr
  simp only [List.map_cons, List.map_nil, Gamma9OrderedSource.prefix_three]
  rw [LowerTripleOrderedSource.partition15 _ _ _
    (secondFunctionalMother_colour_monotone b c e hqr.le)
    (LowerTripleOrderedSource.colour_le_three b c e t.2.2)]
  simp only [LowerTripleOrderedSource.colour_one hbc,
    secondFunctionalMother_colour_two hbc,
    LowerTripleOrderedSource.colour_three hbc hce,
    hrf,
    and_true,
    and_assoc]

end Wu2008DoubleSieve
