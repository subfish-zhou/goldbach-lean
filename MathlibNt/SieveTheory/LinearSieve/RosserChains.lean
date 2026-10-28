import MathlibNt.SieveTheory.LinearSieve.FiniteWeights

/-!
# Rosser boundary chains and logarithmic regions

Upper admissibility, sorted prime chains, lower fixed-depth recursions,
pair removal, and logarithmic-coordinate regions.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-! ## 0.3. Finite upper Rosser weights -/

/-- The standard upper Rosser test on a finite set of distinct primes.  The
test is imposed at odd positions in the decreasing list: at
`p = p_{2l+1}` it says `p₁⋯p_{2l} * p_{2l+1}^3 < D`. -/
def UpperRosserAdmissibleSet (D : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, ¬Even ((s.filter (fun q => p ≤ q)).card) →
    (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < D

/-- The upper Rosser test for the prime factors of a natural number. -/
def UpperRosserAdmissible (D d : ℕ) : Prop :=
  UpperRosserAdmissibleSet D d.primeFactors

/-- The upper Rosser coefficient attached to a finite set of distinct primes. -/
noncomputable def upperRosserSetWeight (D : ℕ) (s : Finset ℕ) : ℝ :=
  if s.prod id < D ∧ UpperRosserAdmissibleSet D s then
    if Even s.card then 1 else -1
  else 0

/-- The even Rosser boundary exposed when a new least prime is inserted: the
old set is active, but adjoining `q` crosses either the level or an odd-position
Rosser constraint. -/
def UpperRosserBoundarySet (D q : ℕ) (s : Finset ℕ) : Prop :=
  Even s.card ∧
    s.prod id < D ∧ UpperRosserAdmissibleSet D s ∧
    ¬((insert q s).prod id < D ∧
      UpperRosserAdmissibleSet D (insert q s))

/-- The first `i + 1` entries of the decreasing enumeration of a finite set are
exactly the entries greater than or equal to its entry at index `i`. -/
theorem sorted_prefix_toFinset_eq_filter_ge (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    ((s.sort (· ≥ ·)).take (i + 1)).toFinset =
      s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q) := by
  symm
  ext q
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hq, hle⟩
    obtain ⟨j, hj, rfl⟩ :=
      List.mem_iff_getElem.mp ((Finset.mem_sort (· ≥ ·)).mpr hq)
    have hji := (s.sortedGT_sort.getElem_le_getElem_iff).mp hle
    exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
  · intro hq
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hq
    refine ⟨(Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem (by omega)), ?_⟩
    exact s.sortedGT_sort.getElem_le_getElem_iff.mpr (by omega)

/-- The filtered prefix through index `i` has exactly `i + 1` entries. -/
theorem sorted_prefix_card_eq_filter_ge (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    (s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q)).card = i + 1 := by
  rw [← sorted_prefix_toFinset_eq_filter_ge s i hi,
    List.toFinset_card_of_nodup (Finset.sort_nodup s (· ≥ ·)).take,
    List.length_take]
  exact Nat.min_eq_left (by omega)

/-- Product form of `sorted_prefix_toFinset_eq_filter_ge`: the filtered Rosser
prefix is the product of the preceding entries and the entry at `i`. -/
theorem sorted_prefix_prod_eq_filter_ge (s : Finset ℕ) (i : ℕ)
    (hi : i < (s.sort (· ≥ ·)).length) :
    (s.filter (fun q => (s.sort (· ≥ ·))[i] ≤ q)).prod id =
      ((s.sort (· ≥ ·)).take i).prod * (s.sort (· ≥ ·))[i] := by
  rw [← sorted_prefix_toFinset_eq_filter_ge s i hi]
  rw [List.prod_toFinset id (Finset.sort_nodup s (· ≥ ·)).take]
  simp only [List.map_id_fun, id_eq]
  rw [← List.take_concat_get hi, List.prod_concat]

/-- The upper Rosser admissibility test in canonical chain coordinates.  In the
decreasing enumeration `p₀ > p₁ > ...`, precisely the even zero-based indices
are tested, and their inequalities are
`p₀ ... pᵢ₋₁ * pᵢ³ < D`. -/
theorem upperRosserAdmissibleSet_iff_sorted_prefix_cube_lt
    {D : ℕ} {s : Finset ℕ} :
    UpperRosserAdmissibleSet D s ↔
      ∀ i (hi : i < (s.sort (· ≥ ·)).length), Even i →
        ((s.sort (· ≥ ·)).take i).prod *
          (s.sort (· ≥ ·))[i] ^ 3 < D := by
  constructor
  · intro hs i hi heven
    let p := (s.sort (· ≥ ·))[i]
    have hp : p ∈ s :=
      (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)
    have hcard : (s.filter (fun q => p ≤ q)).card = i + 1 :=
      sorted_prefix_card_eq_filter_ge s i hi
    have hodd : ¬Even (s.filter (fun q => p ≤ q)).card := by
      rw [hcard]
      intro h
      exact (Nat.even_add_one.mp h) heven
    have htest := hs p hp hodd
    rw [sorted_prefix_prod_eq_filter_ge s i hi] at htest
    simpa [p, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest
  · intro hs p hp hodd
    have hpl : p ∈ s.sort (· ≥ ·) := (Finset.mem_sort (· ≥ ·)).mpr hp
    obtain ⟨i, hi, hip⟩ := List.mem_iff_getElem.mp hpl
    have hcard : (s.filter (fun q => p ≤ q)).card = i + 1 := by
      rw [← hip]
      exact sorted_prefix_card_eq_filter_ge s i hi
    have heven : Even i := by
      by_contra hiOdd
      apply hodd
      rw [hcard, Nat.even_add_one]
      exact hiOdd
    have htest := hs i hi heven
    subst p
    rw [sorted_prefix_prod_eq_filter_ge s i hi]
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest

/-- The lower Rosser admissibility test in canonical chain coordinates. In the
strictly decreasing enumeration, precisely the odd zero-based indices are
tested by the cubic prefix inequalities. -/
theorem lowerRosserAdmissibleSet_iff_sorted_prefix_cube_lt
    {D : ℕ} {s : Finset ℕ} :
    LowerRosserAdmissibleSet D s ↔
      ∀ i (hi : i < (s.sort (· ≥ ·)).length), ¬Even i →
        ((s.sort (· ≥ ·)).take i).prod *
          (s.sort (· ≥ ·))[i] ^ 3 < D := by
  constructor
  · intro hs i hi hodd
    let p := (s.sort (· ≥ ·))[i]
    have hp : p ∈ s :=
      (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)
    have hcard : (s.filter (fun q => p ≤ q)).card = i + 1 :=
      sorted_prefix_card_eq_filter_ge s i hi
    have heven : Even (s.filter (fun q => p ≤ q)).card := by
      rw [hcard, Nat.even_add_one]
      exact hodd
    have htest := hs p hp heven
    rw [sorted_prefix_prod_eq_filter_ge s i hi] at htest
    simpa [p, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest
  · intro hs p hp heven
    have hpl : p ∈ s.sort (· ≥ ·) := (Finset.mem_sort (· ≥ ·)).mpr hp
    obtain ⟨i, hi, hip⟩ := List.mem_iff_getElem.mp hpl
    have hcard : (s.filter (fun q => p ≤ q)).card = i + 1 := by
      rw [← hip]
      exact sorted_prefix_card_eq_filter_ge s i hi
    have hodd : ¬Even i := by
      rw [hcard, Nat.even_add_one] at heven
      exact heven
    have htest := hs i hi hodd
    subst p
    rw [sorted_prefix_prod_eq_filter_ge s i hi]
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest

/-- The ordered odd-chain region underlying one lower Rosser boundary term. -/
def LowerRosserBoundaryChain (D q : ℕ) (l : List ℕ) : Prop :=
  l.SortedGT ∧ ¬Even l.length ∧ l.prod < D ∧
    (∀ i : Fin l.length, ¬Even i.val →
      (l.take i.val).prod * (l.get i) ^ 3 < D) ∧
    D ≤ l.prod * q ^ 3

/-- A lower boundary subset is equivalent to its canonical strictly decreasing,
odd-length boundary chain. -/
theorem lowerRosserBoundarySet_iff_sorted_chain
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    LowerRosserBoundarySet D q s ↔
      LowerRosserBoundaryChain D q (s.sort (· ≥ ·)) := by
  rw [lowerRosserBoundarySet_iff_cube_le hqs hqprime hqmin]
  have hprod : (s.sort (· ≥ ·)).prod = s.prod id := by
    simpa using
      (List.prod_toFinset id (Finset.sort_nodup s (· ≥ ·))).symm
  constructor
  · rintro ⟨hodd, hprodD, hadm, hcube⟩
    refine ⟨Finset.sortedGT_sort s, ?_, ?_, ?_, ?_⟩
    · simpa using hodd
    · simpa [hprod] using hprodD
    · intro i hi
      exact lowerRosserAdmissibleSet_iff_sorted_prefix_cube_lt.mp hadm
        i.val i.isLt hi
    · simpa [hprod] using hcube
  · rintro ⟨hsorted, hodd, hprodD, hadm, hcube⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hodd
    · simpa [hprod] using hprodD
    · apply lowerRosserAdmissibleSet_iff_sorted_prefix_cube_lt.mpr
      intro i hi hiOdd
      exact hadm ⟨i, hi⟩ hiOdd
    · simpa [hprod] using hcube

/-- The explicit ordered-chain region underlying one upper Rosser boundary
term.  This is the finite region that is later reindexed and compared with the
Buchstab nested integrals. -/
def UpperRosserBoundaryChain (D q : ℕ) (l : List ℕ) : Prop :=
  l.SortedGT ∧ Even l.length ∧ l.prod < D ∧
    (∀ i : Fin l.length, Even i.val →
      (l.take i.val).prod * (l.get i) ^ 3 < D) ∧
    D ≤ l.prod * q ^ 3

private theorem lt_ceilDiv_iff_mul_lt_nat
    {D c n : ℕ} (hc : 0 < c) :
    n < D ⌈/⌉ c ↔ c * n < D := by
  rw [← not_le, ceilDiv_le_iff_le_mul hc]
  omega

/-- A singleton lower Rosser boundary chain has no internal cubic test; only
level activity and the terminal boundary remain. -/
theorem lowerRosserBoundaryChain_singleton_iff {D q p : ℕ} :
    LowerRosserBoundaryChain D q [p] ↔
      p < D ∧ D ≤ p * q ^ 3 := by
  constructor
  · rintro ⟨_, _, hprod, _, hterminal⟩
    simpa using And.intro hprod hterminal
  · rintro ⟨hpD, hterminal⟩
    refine ⟨?_, by simp, by simpa using hpD, ?_, by simpa using hterminal⟩
    · intro i j hij
      fin_cases i; fin_cases j
      simp at hij
    · intro i hiOdd
      fin_cases i
      simp at hiOdd

/-- Removing the first two entries of a positive lower Rosser boundary chain
produces the exact residual lower chain at the ceiling-divided level.  The
peeled pair contributes the first odd-index test `p₀ * p₁^3 < D`. -/
theorem lowerRosserBoundaryChain_cons_cons_iff
    {D q p₀ p₁ : ℕ} {xs : List ℕ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) :
    LowerRosserBoundaryChain D q (p₀ :: p₁ :: xs) ↔
      p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧ p₀ * p₁ ^ 3 < D ∧
        LowerRosserBoundaryChain (D ⌈/⌉ (p₀ * p₁)) q xs := by
  have hc : 0 < p₀ * p₁ := Nat.mul_pos hp₀ hp₁
  constructor
  · rintro ⟨hsorted, hodd, hprod, hprefix, hterminal⟩
    have hpw := List.sortedGT_iff_pairwise.mp hsorted
    simp only [List.pairwise_cons] at hpw
    refine ⟨hpw.1 p₁ (by simp), hpw.2.1, ?_, ?_⟩
    · have h := hprefix ⟨1, by simp⟩ (by norm_num)
      simpa using h
    · refine ⟨List.sortedGT_iff_pairwise.mpr hpw.2.2, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.even_add] using hodd
      · apply (lt_ceilDiv_iff_mul_lt_nat hc).2
        simpa [mul_assoc] using hprod
      · intro i hiOdd
        let j : Fin (p₀ :: p₁ :: xs).length :=
          ⟨i.val + 2, by simp⟩
        have hjOdd : ¬Even j.val := by
          simpa [j, Nat.even_add] using hiOdd
        have h := hprefix j hjOdd
        apply (lt_ceilDiv_iff_mul_lt_nat hc).2
        simpa [j, mul_assoc] using h
      · apply (ceilDiv_le_iff_le_mul hc).2
        simpa [mul_assoc] using hterminal
  · rintro ⟨h10, hxs1, hhead, hsorted, hodd, hprod, hprefix, hterminal⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.sortedGT_iff_pairwise, List.pairwise_cons, List.pairwise_cons,
        ← List.sortedGT_iff_pairwise]
      constructor
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact h10
        · exact (hxs1 p hp).trans h10
      · exact ⟨hxs1, hsorted⟩
    · simpa [Nat.even_add] using hodd
    · have h := (lt_ceilDiv_iff_mul_lt_nat hc).1 hprod
      simpa [mul_assoc] using h
    · intro i hiOdd
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => simp at hiOdd
      | succ i =>
          cases i with
          | zero => simpa using hhead
          | succ i =>
              let j : Fin xs.length := ⟨i, by simp at hi; omega⟩
              have hjOdd : ¬Even j.val := by
                simpa [j, Nat.even_add] using hiOdd
              have h := (lt_ceilDiv_iff_mul_lt_nat hc).1 (hprefix j hjOdd)
              simpa [j, mul_assoc] using h
    · have h := (ceilDiv_le_iff_le_mul hc).1 hterminal
      simpa [mul_assoc] using h

/-- Canonical decreasing-list representatives of all lower boundary subsets of
`P`; every represented list has odd length. -/
noncomputable def lowerRosserBoundaryChains
    (D q : ℕ) (P : Finset ℕ) : Finset (List ℕ) :=
  (P.powerset.filter (LowerRosserBoundarySet D q)).image
    (fun s => s.sort (· ≥ ·))

/-- Exact membership characterization for the finite lower-boundary chain
carrier. -/
theorem mem_lowerRosserBoundaryChains_iff
    {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) {l : List ℕ} :
    l ∈ lowerRosserBoundaryChains D q P ↔
      l.Nodup ∧ l.SortedGT ∧ l.toFinset ⊆ P ∧
        LowerRosserBoundaryChain D q l := by
  constructor
  · intro hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hup := Finset.mem_filter.mp hu
    refine ⟨Finset.sort_nodup u (· ≥ ·), Finset.sortedGT_sort u, ?_, ?_⟩
    · simpa using Finset.mem_powerset.mp hup.1
    · exact (lowerRosserBoundarySet_iff_sorted_chain
        (fun hqu => hqs (Finset.mem_powerset.mp hup.1 hqu)) hqprime
        (fun p hp => hqmin p (Finset.mem_powerset.mp hup.1 hp))).mp hup.2
  · rintro ⟨hnodup, hsorted, hsub, hchain⟩
    let u := l.toFinset
    have hsort : u.sort (· ≥ ·) = l :=
      (List.toFinset_sort (r := (· ≥ ·)) hnodup).mpr
        hsorted.sortedGE.pairwise
    apply Finset.mem_image.mpr
    refine ⟨u, ?_, hsort⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsub, ?_⟩
    apply (lowerRosserBoundarySet_iff_sorted_chain
      (fun hqu => hqs (hsub hqu)) hqprime
      (fun p hp => hqmin p (hsub hp))).mpr
    rw [hsort]
    exact hchain


/-- Exact injective finite reindexing of the lower-boundary powerset sum by
canonical odd decreasing chains. -/
theorem sum_lowerRosserBoundary_eq_sum_chains
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) :
    ∑ u ∈ P.powerset.filter (LowerRosserBoundarySet D q),
        ∏ p ∈ u, w p =
      ∑ l ∈ lowerRosserBoundaryChains D q P, (l.map w).prod := by
  rw [lowerRosserBoundaryChains, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    simpa using List.prod_toFinset w (Finset.sort_nodup u (· ≥ ·))
  · intro u hu v hv huv
    have := congrArg List.toFinset huv
    simpa using this

/-- Every lower boundary chain belongs to a unique odd-depth slice. -/
theorem lowerRosserBoundaryChains_exists_unique_depth
    {D q : ℕ} {P : Finset ℕ} {l : List ℕ}
    (hl : l ∈ lowerRosserBoundaryChains D q P) :
    ∃! k : ℕ, l.length = 2 * k + 1 := by
  have hodd : ¬Even l.length := by
    unfold lowerRosserBoundaryChains at hl
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hl
    simpa using (Finset.mem_filter.mp hs).2.1
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
  refine ⟨k, hk, ?_⟩
  intro j hj
  omega

/-- The selected density mass of lower Rosser boundary chains at zero-based
pair-depth `k`, i.e. of exact odd length `2*k+1`. -/
noncomputable def lowerRosserBoundaryChainsFixedPairDepth0Density
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ l ∈ (lowerRosserBoundaryChains D q P).filter
      (fun l => l.length = 2 * k + 1),
    (l.map nu).prod


/-- The singleton lower-boundary density is exactly the one-prime terminal
cubic shell. -/
theorem lowerRosserBoundaryChainsFixedPairDepth0Density_zero
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqs : q ∉ P) (hqprime : q.Prime) (hqmin : ∀ p ∈ P, q ≤ p) :
    lowerRosserBoundaryChainsFixedPairDepth0Density nu D q P 0 =
      ∑ p ∈ P.filter (fun p => p < D ∧ D ≤ p * q ^ 3), nu p := by
  classical
  have hcarrier :
      (lowerRosserBoundaryChains D q P).filter
          (fun l => l.length = 2 * 0 + 1) =
        (P.filter (fun p => p < D ∧ D ≤ p * q ^ 3)).image
          (fun p => [p]) := by
    ext l
    constructor
    · intro hl
      have hparts := Finset.mem_filter.mp hl
      have hlen : l.length = 1 := by simpa using hparts.2
      have hshape : ∃ p, l = [p] := by
        cases l with
        | nil => simp at hlen
        | cons p tail =>
            cases tail with
            | nil => exact ⟨p, rfl⟩
            | cons p' tail' => simp at hlen
      obtain ⟨p, rfl⟩ := hshape
      have hmem := (mem_lowerRosserBoundaryChains_iff hqs hqprime hqmin).1 hparts.1
      apply Finset.mem_image.mpr
      refine ⟨p, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨hmem.2.2.1 (by simp), ?_⟩
      exact lowerRosserBoundaryChain_singleton_iff.mp hmem.2.2.2
    · intro hl
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
      have hp' := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨(mem_lowerRosserBoundaryChains_iff hqs hqprime hqmin).2 ?_, by simp⟩
      have hchain := lowerRosserBoundaryChain_singleton_iff.mpr hp'.2
      refine ⟨by simp, hchain.1, ?_, hchain⟩
      simpa using hp'.1
  rw [lowerRosserBoundaryChainsFixedPairDepth0Density, hcarrier,
    Finset.sum_image]
  · simp
  · intro p hp r hr hpr
    simpa using hpr


/-- Exact carrier recursion for positive pair-depth lower Rosser boundary
chains.  Peeling the two largest selected primes shifts source index by two. -/
theorem mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff
    {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) {l : List ℕ} (k : ℕ) :
    l ∈ (lowerRosserBoundaryChains D q P).filter
          (fun l => l.length = 2 * (k + 1) + 1) ↔
      ∃ p₀ ∈ P, ∃ p₁ ∈ P, p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D ∧
        ∃ xs, l = p₀ :: p₁ :: xs ∧
          xs ∈ (lowerRosserBoundaryChains (D ⌈/⌉ (p₀ * p₁)) q
            (P.filter (fun p => p < p₁))).filter
              (fun xs => xs.length = 2 * k + 1) := by
  constructor
  · intro hl
    have hmem := (mem_lowerRosserBoundaryChains_iff hqs hqprime hqmin).1
      (Finset.mem_filter.mp hl).1
    have hlen := (Finset.mem_filter.mp hl).2
    cases l with
    | nil => simp at hlen
    | cons p₀ tail =>
        cases tail with
        | nil =>
            simp only [List.length_cons, List.length_nil] at hlen
            omega
        | cons p₁ xs =>
            have hp₀P : p₀ ∈ P := hmem.2.2.1 (by simp)
            have hp₁P : p₁ ∈ P := hmem.2.2.1 (by simp)
            have hrec := (lowerRosserBoundaryChain_cons_cons_iff
              (hprime p₀ hp₀P).pos (hprime p₁ hp₁P).pos).1 hmem.2.2.2
            refine ⟨p₀, hp₀P, p₁, hp₁P, hrec.1, hrec.2.2.1, xs, rfl, ?_⟩
            apply Finset.mem_filter.mpr
            refine ⟨(mem_lowerRosserBoundaryChains_iff ?_ hqprime ?_).2 ?_, ?_⟩
            · intro hq
              exact hqs (Finset.mem_filter.mp hq).1
            · intro p hp
              exact hqmin p (Finset.mem_filter.mp hp).1
            · refine ⟨hmem.1.of_cons.of_cons, hrec.2.2.2.1, ?_, hrec.2.2.2⟩
              intro p hp
              exact Finset.mem_filter.mpr
                ⟨hmem.2.2.1 (by simp [hp]), hrec.2.1 p (by simpa using hp)⟩
            · simp only [List.length_cons] at hlen
              omega
  · rintro ⟨p₀, hp₀P, p₁, hp₁P, h10, hhead, xs, rfl, hxs⟩
    have hxsMem := (mem_lowerRosserBoundaryChains_iff
      (by
        intro hq
        exact hqs (Finset.mem_filter.mp hq).1)
      hqprime
      (fun p hp => hqmin p (Finset.mem_filter.mp hp).1)).1
        (Finset.mem_filter.mp hxs).1
    have hxslt : ∀ p ∈ xs, p < p₁ := by
      intro p hp
      exact (Finset.mem_filter.mp (hxsMem.2.2.1 (by simpa using hp))).2
    have hchain : LowerRosserBoundaryChain D q (p₀ :: p₁ :: xs) :=
      (lowerRosserBoundaryChain_cons_cons_iff
        (hprime p₀ hp₀P).pos (hprime p₁ hp₁P).pos).2
          ⟨h10, hxslt, hhead, hxsMem.2.2.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_lowerRosserBoundaryChains_iff hqs hqprime hqmin).2 ?_, ?_⟩
    · refine ⟨?_, hchain.1, ?_, hchain⟩
      · simp only [List.nodup_cons]
        constructor
        · intro hp₀
          simp only [List.mem_cons] at hp₀
          rcases hp₀ with rfl | hp₀
          · exact (Nat.ne_of_gt h10) rfl
          · exact (Nat.ne_of_gt ((hxslt p₀ hp₀).trans h10)) rfl
        · constructor
          · exact fun hp₁ => (Nat.ne_of_gt (hxslt p₁ hp₁)) rfl
          · exact hxsMem.1
      · intro p hp
        simp only [List.mem_toFinset, List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · exact hp₀P
        · exact hp₁P
        · exact (Finset.mem_filter.mp (hxsMem.2.2.1 (by simpa using hp))).1
    · have hlen := (Finset.mem_filter.mp hxs).2
      simp only [List.length_cons]
      omega

/-- Exact two-prime successor recurrence for lower fixed-pair-depth density. -/
theorem lowerRosserBoundaryChainsFixedPairDepth0Density_succ
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) (k : ℕ) :
    lowerRosserBoundaryChainsFixedPairDepth0Density nu D q P (k + 1) =
      ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
          nu p₀ * nu p₁ *
            lowerRosserBoundaryChainsFixedPairDepth0Density nu
              (D ⌈/⌉ (p₀ * p₁)) q (P.filter (fun p => p < p₁)) k := by
  classical
  let A := (lowerRosserBoundaryChains D q P).filter
    (fun l => l.length = 2 * (k + 1) + 1)
  let B : Finset (Σ _p₀ : ℕ, Σ _p₁ : ℕ, List ℕ) :=
    P.sigma fun p₀ =>
      (P.filter (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D)).sigma fun p₁ =>
        (lowerRosserBoundaryChains (D ⌈/⌉ (p₀ * p₁)) q
          (P.filter (fun p => p < p₁))).filter
            (fun xs => xs.length = 2 * k + 1)
  let encode : List ℕ → (Σ _p₀ : ℕ, Σ _p₁ : ℕ, List ℕ) := fun l =>
    match l with
    | p₀ :: p₁ :: xs => ⟨p₀, ⟨p₁, xs⟩⟩
    | _ => ⟨0, ⟨0, []⟩⟩
  let decode : (Σ _p₀ : ℕ, Σ _p₁ : ℕ, List ℕ) → List ℕ := fun b =>
    b.1 :: b.2.1 :: b.2.2
  have hsum :
      ∑ l ∈ A, (l.map nu).prod =
        ∑ b ∈ B, nu b.1 * nu b.2.1 * (b.2.2.map nu).prod := by
    apply Finset.sum_bij' (fun l _ => encode l) (fun b _ => decode b)
    · intro l hl
      have hdecomp := (mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      simpa [encode, B, h10, hhead, hp₀, hp₁] using hxs
    · rintro ⟨p₀, p₁, xs⟩ hb
      simp only [B, Finset.mem_sigma, Finset.mem_filter] at hb
      exact (mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff
        hqs hqprime hprime hqmin k).2
          ⟨p₀, hb.1, p₁, hb.2.1.1, hb.2.1.2.1, hb.2.1.2.2,
            xs, rfl, Finset.mem_filter.mpr hb.2.2⟩
    · intro l hl
      have hdecomp := (mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      rfl
    · rintro ⟨p₀, p₁, xs⟩ hb
      rfl
    · intro l hl
      have hdecomp := (mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      simp [encode, mul_assoc]
  rw [lowerRosserBoundaryChainsFixedPairDepth0Density]
  change ∑ l ∈ A, (l.map nu).prod = _
  rw [hsum]
  simp only [B, Finset.sum_sigma]
  simp_rw [lowerRosserBoundaryChainsFixedPairDepth0Density, Finset.mul_sum]

/-- Removing the first two entries of a positive upper Rosser boundary chain
gives an exact residual chain at the ceiling-divided level. -/
theorem upperRosserBoundaryChain_cons_cons_iff
    {D q p₀ p₁ : ℕ} {xs : List ℕ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) :
    UpperRosserBoundaryChain D q (p₀ :: p₁ :: xs) ↔
      p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧ p₀ ^ 3 < D ∧
        UpperRosserBoundaryChain (D ⌈/⌉ (p₀ * p₁)) q xs := by
  have hc : 0 < p₀ * p₁ := Nat.mul_pos hp₀ hp₁
  constructor
  · rintro ⟨hsorted, heven, hprod, hprefix, hterminal⟩
    have hpw := List.sortedGT_iff_pairwise.mp hsorted
    simp only [List.pairwise_cons] at hpw
    refine ⟨hpw.1 p₁ (by simp), hpw.2.1, ?_, ?_⟩
    · have h := hprefix ⟨0, by simp⟩ (by simp)
      simpa using h
    · refine ⟨List.sortedGT_iff_pairwise.mpr hpw.2.2, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.even_add] using heven
      · apply (lt_ceilDiv_iff_mul_lt_nat hc).2
        simpa [mul_assoc] using hprod
      · intro i hiEven
        let j : Fin (p₀ :: p₁ :: xs).length :=
          ⟨i.val + 2, by simp⟩
        have hjEven : Even j.val := hiEven.add (by norm_num)
        have h := hprefix j hjEven
        apply (lt_ceilDiv_iff_mul_lt_nat hc).2
        simpa [j, mul_assoc] using h
      · apply (ceilDiv_le_iff_le_mul hc).2
        simpa [mul_assoc] using hterminal
  · rintro ⟨h10, hxs1, hhead, hsorted, heven, hprod, hprefix, hterminal⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.sortedGT_iff_pairwise, List.pairwise_cons, List.pairwise_cons,
        ← List.sortedGT_iff_pairwise]
      constructor
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact h10
        · exact (hxs1 p hp).trans h10
      · exact ⟨hxs1, hsorted⟩
    · simpa [Nat.even_add] using heven
    · have h := (lt_ceilDiv_iff_mul_lt_nat hc).1 hprod
      simpa [mul_assoc] using h
    · intro i hiEven
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => simpa using hhead
      | succ i =>
          cases i with
          | zero => simp at hiEven
          | succ i =>
              let j : Fin xs.length := ⟨i, by simp at hi; omega⟩
              have hjEven : Even j.val := by
                simpa [j, Nat.even_add] using hiEven
              have h := (lt_ceilDiv_iff_mul_lt_nat hc).1 (hprefix j hjEven)
              simpa [j, mul_assoc] using h
    · have h := (ceilDiv_le_iff_le_mul hc).1 hterminal
      simpa [mul_assoc] using h


end MathlibNt.SieveTheory.LinearSieve
