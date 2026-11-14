module

public import MathlibNt.SieveTheory.LinearSieve.FiniteWeights

/-!
# Rosser boundary chains and logarithmic regions

Upper admissibility, sorted prime chains, lower fixed-depth recursions,
pair removal, and logarithmic-coordinate regions.
-/

@[expose] public section

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

private theorem rosser_tests_iff_sorted_prefix_cube_lt {D : ℕ} {s : Finset ℕ}
    (test : ℕ → Prop) :
    (∀ p ∈ s, test ((s.filter (fun q => p ≤ q)).card) →
      (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < D) ↔
    ∀ i (hi : i < (s.sort (· ≥ ·)).length), test (i + 1) →
      ((s.sort (· ≥ ·)).take i).prod * (s.sort (· ≥ ·))[i] ^ 3 < D := by
  constructor
  · intro hs i hi hindex
    have hp := (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)
    have htest := hs _ hp (by rwa [sorted_prefix_card_eq_filter_ge s i hi])
    rw [sorted_prefix_prod_eq_filter_ge s i hi] at htest
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest
  · intro hs p hp hcard
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≥ ·)).mpr hp)
    rw [sorted_prefix_card_eq_filter_ge s i hi] at hcard
    rw [sorted_prefix_prod_eq_filter_ge s i hi]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hs i hi hcard

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
  simpa only [UpperRosserAdmissibleSet, Nat.even_add_one, not_not] using
    (rosser_tests_iff_sorted_prefix_cube_lt (D := D) (s := s) (fun n => ¬Even n))

/-- The lower Rosser admissibility test in canonical chain coordinates. In the
strictly decreasing enumeration, precisely the odd zero-based indices are
tested by the cubic prefix inequalities. -/
theorem lowerRosserAdmissibleSet_iff_sorted_prefix_cube_lt
    {D : ℕ} {s : Finset ℕ} :
    LowerRosserAdmissibleSet D s ↔
      ∀ i (hi : i < (s.sort (· ≥ ·)).length), ¬Even i →
        ((s.sort (· ≥ ·)).take i).prod *
          (s.sort (· ≥ ·))[i] ^ 3 < D := by
  simpa only [LowerRosserAdmissibleSet, Nat.even_add_one] using
    (rosser_tests_iff_sorted_prefix_cube_lt (D := D) (s := s) Even)

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

private def rosserBoundaryChain (test : ℕ → Prop) (D q : ℕ) (l : List ℕ) : Prop :=
  l.SortedGT ∧ test l.length ∧ l.prod < D ∧
    (∀ i : Fin l.length, test i.val →
      (l.take i.val).prod * (l.get i) ^ 3 < D) ∧
    D ≤ l.prod * q ^ 3

private theorem rosserBoundaryChain_cons_cons
    {D q p₀ p₁ : ℕ} {xs : List ℕ} (hc : 0 < p₀ * p₁)
    (test : ℕ → Prop) (hshift : ∀ i, test (i + 2) ↔ test i) :
    rosserBoundaryChain test D q (p₀ :: p₁ :: xs) ↔
      p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧
        (test 0 → p₀ ^ 3 < D) ∧ (test 1 → p₀ * p₁ ^ 3 < D) ∧
        rosserBoundaryChain test (D ⌈/⌉ (p₀ * p₁)) q xs := by
  have hsorted : (p₀ :: p₁ :: xs).SortedGT ↔
      p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧ xs.SortedGT := by
    simp only [List.sortedGT_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨hlt, _⟩, htail⟩ => ⟨hlt, htail⟩,
      fun ⟨hlt, htail, hs⟩ => ⟨⟨hlt, fun p hp => (htail p hp).trans hlt⟩, htail, hs⟩⟩
  have hlt : ∀ n, n < D ⌈/⌉ (p₀ * p₁) ↔ p₀ * p₁ * n < D :=
    fun _ => (gc_mul_ceilDiv hc).lt_iff_lt
  unfold rosserBoundaryChain
  simp only [hsorted, List.length_cons, show ∀ n : ℕ, n + 1 + 1 = n + 2 from fun _ => rfl,
    hshift, Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, List.get_cons_zero,
    List.get_cons_succ', List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons,
    one_mul, hlt, ceilDiv_le_iff_le_mul hc, mul_assoc]
  tauto

/-- A singleton lower Rosser boundary chain has no internal cubic test; only
level activity and the terminal boundary remain. -/
theorem lowerRosserBoundaryChain_singleton_iff {D q p : ℕ} :
    LowerRosserBoundaryChain D q [p] ↔
      p < D ∧ D ≤ p * q ^ 3 := by
  constructor
  · rintro ⟨_, _, hprod, _, hterminal⟩
    simpa using And.intro hprod hterminal
  · rintro ⟨hpD, hterminal⟩
    refine ⟨by simp [List.sortedGT_iff_pairwise], by simp, by simpa using hpD,
      ?_, by simpa using hterminal⟩
    intro i hiOdd
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
  simpa [rosserBoundaryChain, LowerRosserBoundaryChain] using
    (rosserBoundaryChain_cons_cons (Nat.mul_pos hp₀ hp₁) (fun i => ¬Even i)
      (fun i => not_congr (by simp [Nat.even_add] : Even (i + 2) ↔ Even i)))

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


/-- A boundary chain whose length is at least two can be split at its two
largest entries. The residual carrier keeps only primes below the second entry. -/
theorem rosser_boundary_chains_pair_depth_succ_iff
    {D : ℕ} {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    {carrier : ℕ → Finset ℕ → Finset (List ℕ)}
    {chain : ℕ → List ℕ → Prop} {headTest : ℕ → ℕ → Prop}
    (hmem : ∀ {E : ℕ} {A : Finset ℕ} {l : List ℕ}, A ⊆ P →
      (l ∈ carrier E A ↔ l.toFinset ⊆ A ∧ chain E l))
    (hstep : ∀ {p₀ p₁ : ℕ} {xs : List ℕ}, p₀.Prime → p₁.Prime →
      (chain D (p₀ :: p₁ :: xs) ↔ p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧
        headTest p₀ p₁ ∧ chain (D ⌈/⌉ (p₀ * p₁)) xs))
    {l : List ℕ} (k offset : ℕ) :
    l ∈ (carrier D P).filter (fun l => l.length = 2 * (k + 1) + offset) ↔
      ∃ p₀ ∈ P, ∃ p₁ ∈ P, p₁ < p₀ ∧ headTest p₀ p₁ ∧
        ∃ xs, l = p₀ :: p₁ :: xs ∧
          xs ∈ (carrier (D ⌈/⌉ (p₀ * p₁)) (P.filter (fun p => p < p₁))).filter
            (fun xs => xs.length = 2 * k + offset) := by
  simp only [Finset.mem_filter, hmem (show P ⊆ P from fun _ h => h), hmem (Finset.filter_subset _ _)]
  constructor
  · rintro ⟨⟨hsub, hchain⟩, hlen⟩
    match l with
    | [] | [_] => simp only [List.length_nil, List.length_cons] at hlen; omega
    | p₀ :: p₁ :: xs =>
      have hp₀ : p₀ ∈ P := hsub (by simp)
      have hp₁ : p₁ ∈ P := hsub (by simp)
      obtain ⟨hlt, htail, hhead, hrec⟩ := (hstep (hprime p₀ hp₀) (hprime p₁ hp₁)).mp hchain
      refine ⟨p₀, hp₀, p₁, hp₁, hlt, hhead, xs, rfl, ⟨?_, hrec⟩, ?_⟩
      · intro p hp
        exact Finset.mem_filter.mpr ⟨hsub (by simp [hp]), htail p (by simpa using hp)⟩
      · simp only [List.length_cons] at hlen
        omega
  · rintro ⟨p₀, hp₀, p₁, hp₁, hlt, hhead, xs, rfl, ⟨hsub, hrec⟩, hlen⟩
    refine ⟨⟨?_, (hstep (hprime p₀ hp₀) (hprime p₁ hp₁)).mpr
      ⟨hlt, fun p hp => (Finset.mem_filter.mp (hsub (by simpa using hp))).2, hhead, hrec⟩⟩, ?_⟩
    · intro p hp
      simp only [List.mem_toFinset, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact hp₀
      · exact hp₁
      · exact (Finset.mem_filter.mp (hsub (by simpa using hp))).1
    · simp only [List.length_cons]
      omega


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
  have hmem {E : ℕ} {A : Finset ℕ} {xs : List ℕ} (hA : A ⊆ P) :
      xs ∈ lowerRosserBoundaryChains E q A ↔
        xs.toFinset ⊆ A ∧ LowerRosserBoundaryChain E q xs := by
    rw [mem_lowerRosserBoundaryChains_iff (fun h => hqs (hA h)) hqprime (fun p hp => hqmin p (hA hp))]
    exact ⟨fun h => h.2.2, fun h => ⟨h.2.1.nodup, h.2.1, h.1, h.2⟩⟩
  exact
    rosser_boundary_chains_pair_depth_succ_iff (D := D)
      (chain := fun E => LowerRosserBoundaryChain E q) (headTest := fun p₀ p₁ => p₀ * p₁ ^ 3 < D)
      hprime hmem (fun hp₀ hp₁ => lowerRosserBoundaryChain_cons_cons_iff hp₀.pos hp₁.pos) k 1

/-- Sum the product weights by their first two entries and residual chain. -/
theorem rosser_boundary_chains_pair_sum
    (nu : ℕ → ℝ) {P : Finset ℕ} {A : Finset (List ℕ)}
    {tail : ℕ → ℕ → Finset (List ℕ)} {headTest : ℕ → ℕ → Prop}
    [DecidableRel headTest]
    (hsplit : ∀ {l : List ℕ}, l ∈ A ↔
      ∃ p₀ ∈ P, ∃ p₁ ∈ P, p₁ < p₀ ∧ headTest p₀ p₁ ∧
        ∃ xs, l = p₀ :: p₁ :: xs ∧ xs ∈ tail p₀ p₁) :
    ∑ l ∈ A, (l.map nu).prod =
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ headTest p₀ p₁),
        nu p₀ * nu p₁ * ∑ xs ∈ tail p₀ p₁, (xs.map nu).prod := by
  classical
  let B := P.sigma fun p₀ =>
    (P.filter (fun p₁ => p₁ < p₀ ∧ headTest p₀ p₁)).sigma (tail p₀)
  have hsum : ∑ b ∈ B, nu b.1 * nu b.2.1 * (b.2.2.map nu).prod =
      ∑ l ∈ A, (l.map nu).prod := by
    apply Finset.sum_nbij (fun b => b.1 :: b.2.1 :: b.2.2)
    · rintro ⟨p₀, p₁, xs⟩ hb
      simp only [B, Finset.mem_sigma, Finset.mem_filter] at hb
      exact hsplit.mpr ⟨p₀, hb.1, p₁, hb.2.1.1, hb.2.1.2.1, hb.2.1.2.2, xs, rfl, hb.2.2⟩
    · rintro ⟨p₀, p₁, xs⟩ _ ⟨r₀, r₁, ys⟩ _ heq
      obtain ⟨rfl, heq⟩ := List.cons.inj heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      rfl
    · intro l hl
      obtain ⟨p₀, hp₀, p₁, hp₁, hlt, hhead, xs, rfl, hxs⟩ := hsplit.mp hl
      exact ⟨⟨p₀, p₁, xs⟩, by simpa [B, hp₀, hp₁, hlt, hhead] using hxs, rfl⟩
    · rintro ⟨p₀, p₁, xs⟩ _
      simp [mul_assoc]
  rw [← hsum]
  simp only [B, Finset.sum_sigma, Finset.mul_sum]


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
  simpa only [lowerRosserBoundaryChainsFixedPairDepth0Density] using
    rosser_boundary_chains_pair_sum nu
      (mem_lowerRosserBoundaryChains_fixedPairDepth0_succ_iff hqs hqprime hprime hqmin k)

/-- Removing the first two entries of a positive upper Rosser boundary chain
gives an exact residual chain at the ceiling-divided level. -/
theorem upperRosserBoundaryChain_cons_cons_iff
    {D q p₀ p₁ : ℕ} {xs : List ℕ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) :
    UpperRosserBoundaryChain D q (p₀ :: p₁ :: xs) ↔
      p₁ < p₀ ∧ (∀ p ∈ xs, p < p₁) ∧ p₀ ^ 3 < D ∧
        UpperRosserBoundaryChain (D ⌈/⌉ (p₀ * p₁)) q xs := by
  simpa [rosserBoundaryChain, UpperRosserBoundaryChain] using
    (rosserBoundaryChain_cons_cons (Nat.mul_pos hp₀ hp₁) Even
      (by intro i; simp [Nat.even_add]))

end MathlibNt.SieveTheory.LinearSieve
