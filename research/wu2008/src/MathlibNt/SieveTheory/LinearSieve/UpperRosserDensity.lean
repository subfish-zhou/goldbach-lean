import MathlibNt.SieveTheory.LinearSieve.BoundaryIntegrals

/-!
# Finite upper Rosser density and certificates

Logarithmic realization of discrete chains, fixed-depth density recursions,
Euler-normalized boundary identities, and upper weight certificates.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-- A discrete Rosser boundary chain lies in its exact logarithmic-coordinate
region. The floor in the natural level weakens strict prefix inequalities to
closed faces, while making the terminal shell strict. -/
theorem UpperRosserBoundaryChain.logarithmicCoordinates_mem
    {z Δ s : ℝ} {q : ℕ} {l : List ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hq : 0 < q) (hl : ∀ p ∈ l, 0 < p)
    (hchain : UpperRosserBoundaryChain (Nat.floor Δ + 1) q l) :
    UpperRosserLogRegion s (Real.log q / Real.log z)
      (logarithmicCoordinates z l) := by
  rcases hchain with ⟨hsorted, heven, hprod, hprefix, hterminal⟩
  refine ⟨logarithmicCoordinates_sortedGT hz hl hsorted,
    by simpa [logarithmicCoordinates] using heven, ?_, ?_, ?_⟩
  · rw [sum_logarithmicCoordinates_eq_log_prod l hl, hs]
    exact log_nat_div_log_le_of_lt_floor_add_one hz hΔ
      (List.prod_pos hl) hprod
  · intro i hi hiEven
    have hil : i < l.length := by
      simpa [logarithmicCoordinates] using hi
    let j : Fin l.length := ⟨i, hil⟩
    have htake :
        (logarithmicCoordinates z l).take i =
          logarithmicCoordinates z (l.take i) := by
      simp [logarithmicCoordinates]
    have hget :
        (logarithmicCoordinates z l)[i] =
          Real.log (l.get j : ℝ) / Real.log z := by
      simp [logarithmicCoordinates, j]
    rw [htake, hget, logarithmicCoordinates_prefix_cube hl j, hs]
    exact log_nat_div_log_le_of_lt_floor_add_one hz hΔ
      (mul_pos
        (List.prod_pos fun p hp => hl p (List.mem_of_mem_take hp))
        (pow_pos (hl _ (List.get_mem l j)) 3))
      (hprefix j hiEven)
  · rw [sum_logarithmicCoordinates_eq_log_prod l hl, hs]
    have heq :
        Real.log (l.prod : ℝ) / Real.log z +
            3 * (Real.log q / Real.log z) =
          Real.log ((l.prod * q ^ 3 : ℕ) : ℝ) / Real.log z := by
      have hlprodpos : 0 < l.prod := List.prod_pos hl
      rw [Nat.cast_mul, Nat.cast_pow,
        Real.log_mul (by exact_mod_cast hlprodpos.ne') (by positivity),
        Real.log_pow]
      ring
    rw [heq]
    exact log_div_log_lt_of_floor_add_one_le hz hΔ hterminal

/-- The finite upper Rosser density sum over subsets of a prescribed prime set. -/
noncomputable def upperRosserSetDensitySum
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ s ∈ P.powerset, upperRosserSetWeight D s * ∏ p ∈ s, nu p

/-- Initial value for the finite upper Rosser density recursion. -/
theorem upperRosserSetDensitySum_empty
    (nu : ℕ → ℝ) {D : ℕ} (hD : 1 < D) :
    upperRosserSetDensitySum nu D ∅ = 1 := by
  simp [upperRosserSetDensitySum, upperRosserSetWeight,
    UpperRosserAdmissibleSet, hD]

/-- Exact one-prime recursion for the finite upper Rosser density sum.  It is
the finite combinatorial form of the Buchstab decomposition: subsets not
containing `q` and subsets containing `q` are paired over `P.powerset`. -/
theorem upperRosserSetDensitySum_insert
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) (hq : q ∉ P) :
    upperRosserSetDensitySum nu D (insert q P) =
      ∑ s ∈ P.powerset,
        (upperRosserSetWeight D s +
            nu q * upperRosserSetWeight D (insert q s)) *
          ∏ p ∈ s, nu p := by
  have hdis :
      Disjoint P.powerset (P.powerset.image (insert q)) := by
    rw [Finset.disjoint_left]
    intro s hs hsi
    have hqs : q ∉ s :=
      fun h ↦ hq (Finset.mem_powerset.mp hs h)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hsi
    exact hqs (Finset.mem_insert_self q u)
  have hinj :
      Set.InjOn (insert q) (↑P.powerset : Set (Finset ℕ)) := by
    intro s hs u hu hsu
    have hqs : q ∉ s :=
      fun h ↦ hq (Finset.mem_powerset.mp hs h)
    have hqu : q ∉ u :=
      fun h ↦ hq (Finset.mem_powerset.mp hu h)
    have heq := congrArg (fun v : Finset ℕ ↦ v.erase q) hsu
    simpa [Finset.erase_insert, hqs, hqu] using heq
  unfold upperRosserSetDensitySum
  rw [Finset.powerset_insert, Finset.sum_union hdis,
    Finset.sum_image hinj, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hqs : q ∉ s :=
    fun h ↦ hq (Finset.mem_powerset.mp hs h)
  rw [Finset.prod_insert hqs]
  ring

/-- Cardinality-decreasing form of the finite Buchstab recursion, obtained by
peeling off the least prime in a nonempty finite set. -/
theorem upperRosserSetDensitySum_min_recursion
    (nu : ℕ → ℝ) (D : ℕ) {P : Finset ℕ} (hP : P.Nonempty) :
    upperRosserSetDensitySum nu D P =
      ∑ s ∈ (P.erase (P.min' hP)).powerset,
        (upperRosserSetWeight D s +
            nu (P.min' hP) *
              upperRosserSetWeight D (insert (P.min' hP) s)) *
          ∏ p ∈ s, nu p := by
  let q := P.min' hP
  let T := P.erase q
  have hqP : q ∈ P := Finset.min'_mem P hP
  have hqT : q ∉ T := by simp [T]
  have hPT : insert q T = P := Finset.insert_erase hqP
  calc
    upperRosserSetDensitySum nu D P =
        upperRosserSetDensitySum nu D (insert q T) := by rw [hPT]
    _ = ∑ s ∈ T.powerset,
        (upperRosserSetWeight D s +
            nu q * upperRosserSetWeight D (insert q s)) *
          ∏ p ∈ s, nu p :=
      upperRosserSetDensitySum_insert nu D q T hqT
    _ = ∑ s ∈ (P.erase (P.min' hP)).powerset,
        (upperRosserSetWeight D s +
            nu (P.min' hP) *
              upperRosserSetWeight D (insert (P.min' hP) s)) *
          ∏ p ∈ s, nu p := by rfl

private theorem upperRosserAdmissibleSet_insert_min_of_odd
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : UpperRosserAdmissibleSet D s)
    (hodd : ¬Even s.card) :
    UpperRosserAdmissibleSet D (insert q s) := by
  intro p hp hcard
  obtain hp_eq | hp_s := Finset.mem_insert.mp hp
  · subst p
    have hfilter : (insert q s).filter (fun r ↦ q ≤ r) = insert q s :=
      Finset.filter_eq_self.mpr fun r hr ↦ by
        obtain rfl | hr_s := Finset.mem_insert.mp hr
        · exact le_rfl
        · exact hqmin r hr_s
    have hinsEven : Even (insert q s).card := by
      rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
      exact hodd
    rw [hfilter] at hcard
    exact (hcard hinsEven).elim
  · have hpq : ¬p ≤ q := by
      rw [not_le]
      exact lt_of_le_of_ne (hqmin p hp_s) (Ne.symm fun h ↦ hqs (h ▸ hp_s))
    have hfilter : (insert q s).filter (fun r ↦ p ≤ r) =
        s.filter (fun r ↦ p ≤ r) := by
      simp [Finset.filter_insert, hpq]
    rw [hfilter] at hcard ⊢
    exact hs p hp_s hcard

private theorem upperRosserAdmissibleSet_of_insert_min
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : UpperRosserAdmissibleSet D (insert q s)) :
    UpperRosserAdmissibleSet D s := by
  intro p hp hcard
  have hpq : ¬p ≤ q := by
    rw [not_le]
    exact lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h ↦ hqs (h ▸ hp))
  have hfilter : (insert q s).filter (fun r ↦ p ≤ r) =
      s.filter (fun r ↦ p ≤ r) := by
    simp [Finset.filter_insert, hpq]
  rw [← hfilter] at hcard ⊢
  exact hs p (Finset.mem_insert_of_mem hp) hcard

private theorem prod_insert_min_lt_of_upperRosserAdmissibleSet_odd
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqD : q < D) (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : UpperRosserAdmissibleSet D s) (hodd : ¬Even s.card) :
    (insert q s).prod id < D := by
  by_cases hs0 : s = ∅
  · subst s
    simpa using hqD
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    let p := s.min' hsne
    have hp : p ∈ s := Finset.min'_mem s hsne
    have hpmin : ∀ r ∈ s, p ≤ r := fun r hr ↦ Finset.min'_le s r hr
    have hfilter : s.filter (fun r ↦ p ≤ r) = s :=
      Finset.filter_eq_self.mpr hpmin
    have htest := hs p hp (by simpa [hfilter] using hodd)
    rw [hfilter] at htest
    have hqp2 : q ≤ p ^ 2 := by
      calc
        q ≤ p := hqmin p hp
        _ ≤ p * p := Nat.le_mul_of_pos_right p
          (lt_of_lt_of_le hqprime.pos (hqmin p hp))
        _ = p ^ 2 := by ring
    rw [Finset.prod_insert hqs]
    exact lt_of_le_of_lt (by
      simpa [mul_comm] using Nat.mul_le_mul_right (s.prod id) hqp2) htest

/-- For an active even set, adjoining a new least prime remains active exactly
until the cubic Rosser cutoff `q ^ 3 * ∏ s < D` is crossed. -/
theorem upperRosser_insert_min_active_iff_cube_lt
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) (heven : Even s.card)
    (hs : s.prod id < D ∧ UpperRosserAdmissibleSet D s) :
    (insert q s).prod id < D ∧
        UpperRosserAdmissibleSet D (insert q s) ↔
      s.prod id * q ^ 3 < D := by
  have hfilterq :
      (insert q s).filter (fun r ↦ q ≤ r) = insert q s :=
    Finset.filter_eq_self.mpr fun r hr ↦ by
      obtain rfl | hr_s := Finset.mem_insert.mp hr
      · exact le_rfl
      · exact hqmin r hr_s
  have hodd : ¬Even (insert q s).card := by
    rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
    exact not_not_intro heven
  constructor
  · intro hins
    have htest := hins.2 q (Finset.mem_insert_self q s) (by
      simpa [hfilterq] using hodd)
    rw [hfilterq, Finset.prod_insert hqs] at htest
    simpa only [id_eq, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest
  · intro hcube
    constructor
    · rw [Finset.prod_insert hqs]
      have hqle : q ≤ q ^ 3 := by
        exact Nat.le_pow (by norm_num)
      exact lt_of_le_of_lt
        (by simpa [mul_comm] using Nat.mul_le_mul_left (s.prod id) hqle)
        (by simpa [mul_comm] using hcube)
    · intro p hp hcard
      obtain rfl | hp_s := Finset.mem_insert.mp hp
      · rw [hfilterq, Finset.prod_insert hqs]
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hcube
      · have hpq : ¬p ≤ q := by
          rw [not_le]
          exact lt_of_le_of_ne (hqmin p hp_s)
            (Ne.symm fun h ↦ hqs (h ▸ hp_s))
        have hfilter :
            (insert q s).filter (fun r ↦ p ≤ r) =
              s.filter (fun r ↦ p ≤ r) := by
          simp [Finset.filter_insert, hpq]
        rw [hfilter] at hcard ⊢
        exact hs.2 p hp_s hcard

/-- The abstract even Rosser boundary is exactly the cubic shell
`D ≤ q ^ 3 * ∏ s` once `q` is the new least prime. -/
theorem upperRosserBoundarySet_iff_cube_le
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    UpperRosserBoundarySet D q s ↔
      Even s.card ∧
        s.prod id < D ∧ UpperRosserAdmissibleSet D s ∧
        D ≤ s.prod id * q ^ 3 := by
  constructor
  · rintro ⟨heven, hsD, hsAdmissible, hins⟩
    refine ⟨heven, hsD, hsAdmissible, ?_⟩
    rw [← not_lt]
    exact fun hcube ↦ hins
      ((upperRosser_insert_min_active_iff_cube_lt hqs hqprime hqmin heven
        ⟨hsD, hsAdmissible⟩).mpr hcube)
  · rintro ⟨heven, hsD, hsAdmissible, hcube⟩
    refine ⟨heven, hsD, hsAdmissible, ?_⟩
    intro hins
    have hlt :=
      (upperRosser_insert_min_active_iff_cube_lt hqs hqprime hqmin heven
        ⟨hsD, hsAdmissible⟩).mp hins
    omega

/-- A boundary subset is equivalently its canonical decreasing Rosser chain.
The statement retains all alternating-prefix inequalities, rather than
incorrectly truncating boundary tails to cardinality zero or two. -/
theorem upperRosserBoundarySet_iff_sorted_chain
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    UpperRosserBoundarySet D q s ↔
      UpperRosserBoundaryChain D q (s.sort (· ≥ ·)) := by
  rw [upperRosserBoundarySet_iff_cube_le hqs hqprime hqmin]
  have hprod : (s.sort (· ≥ ·)).prod = s.prod id := by
    simpa using
      (List.prod_toFinset id (Finset.sort_nodup s (· ≥ ·))).symm
  constructor
  · rintro ⟨heven, hprodD, hadm, hcube⟩
    refine ⟨Finset.sortedGT_sort s, ?_, ?_, ?_, ?_⟩
    · simpa using heven
    · simpa [hprod] using hprodD
    · intro i hi
      exact upperRosserAdmissibleSet_iff_sorted_prefix_cube_lt.mp hadm
        i.val i.isLt hi
    · simpa [hprod] using hcube
  · rintro ⟨hsorted, heven, hprodD, hadm, hcube⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using heven
    · simpa [hprod] using hprodD
    · apply upperRosserAdmissibleSet_iff_sorted_prefix_cube_lt.mpr
      intro i hi hiEven
      exact hadm ⟨i, hi⟩ hiEven
    · simpa [hprod] using hcube

/-- Canonical decreasing-list representatives of all boundary subsets of `P`.
Unlike a powerset, this carrier exposes the chain length and indexed prefixes
used by the Buchstab iteration. -/
noncomputable def upperRosserBoundaryChains
    (D q : ℕ) (P : Finset ℕ) : Finset (List ℕ) :=
  (P.powerset.filter (UpperRosserBoundarySet D q)).image
    (fun s => s.sort (· ≥ ·))

/-- Membership in the canonical boundary-chain carrier is exactly strict
decrease, containment in `P`, and the explicit arbitrary-depth Rosser region. -/
theorem mem_upperRosserBoundaryChains_iff
    {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) {l : List ℕ} :
    l ∈ upperRosserBoundaryChains D q P ↔
      l.Nodup ∧ l.SortedGT ∧ l.toFinset ⊆ P ∧
        UpperRosserBoundaryChain D q l := by
  constructor
  · intro hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hup := Finset.mem_filter.mp hu
    refine ⟨Finset.sort_nodup u (· ≥ ·), Finset.sortedGT_sort u, ?_, ?_⟩
    · simpa using Finset.mem_powerset.mp hup.1
    · exact (upperRosserBoundarySet_iff_sorted_chain
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
    apply (upperRosserBoundarySet_iff_sorted_chain
      (fun hqu => hqs (hsub hqu)) hqprime
      (fun p hp => hqmin p (hsub hp))).mpr
    rw [hsort]
    exact hchain

/-- The selected density mass of upper Rosser boundary chains of exact length
`2k`.  This is the discrete quantity compared depth-by-depth with
`upperRosserBoundaryMassAux`. -/
noncomputable def upperRosserBoundaryChainsFixedDepthDensity
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ l ∈ (upperRosserBoundaryChains D q P).filter
      (fun l => l.length = 2 * k),
    (l.map nu).prod

/-- The exact fixed-depth boundary density on the relative Euler-product scale.
Keeping the quotient intact is essential in the depth tail: replacing its
denominator by a pointwise local-product majorant loses the full sieve-product
factor required by the fundamental lemma. -/
noncomputable def upperRosserBoundaryChainsFixedDepthRelativeDensity
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) (k : ℕ) : ℝ :=
  upperRosserBoundaryChainsFixedDepthDensity nu D q P k /
    ∏ p ∈ P, (1 - nu p)

/-- The exact relative weight for peeling the two largest selected primes.
The quotient of Euler products retains all primes skipped before the residual
carrier `p < p₁`; no local-product estimate has yet been applied. -/
noncomputable def upperRosserBoundaryRelativePairTransition
    (nu : ℕ → ℝ) (P : Finset ℕ) (p₀ p₁ : ℕ) : ℝ :=
  (nu p₀ * nu p₁ *
      ∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p)) /
    ∏ p ∈ P, (1 - nu p)

/-- Restoring the ambient Euler product cancels a relative pair transition
exactly, leaving the selected pair and the residual Euler product. -/
theorem upperRosserBoundaryRelativePairTransition_mul_eulerProduct
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserBoundaryRelativePairTransition nu P p₀ p₁ *
        ∏ p ∈ P, (1 - nu p) =
      nu p₀ * nu p₁ *
        ∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p) := by
  have hprod : (∏ p ∈ P, (1 - nu p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor
  unfold upperRosserBoundaryRelativePairTransition
  field_simp [hprod]

/-- Exact carrier recursion for positive-depth upper Rosser boundary chains.
The first two entries determine a residual chain at the ceiling-divided level,
with its ambient primes restricted below the second entry. -/
theorem mem_upperRosserBoundaryChains_fixedDepth_succ_iff
    {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) {l : List ℕ} (k : ℕ) :
    l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = 2 * (k + 1)) ↔
      ∃ p₀ ∈ P, ∃ p₁ ∈ P, p₁ < p₀ ∧ p₀ ^ 3 < D ∧
        ∃ xs, l = p₀ :: p₁ :: xs ∧
          xs ∈ (upperRosserBoundaryChains (D ⌈/⌉ (p₀ * p₁)) q
            (P.filter (fun p => p < p₁))).filter
              (fun xs => xs.length = 2 * k) := by
  constructor
  · intro hl
    have hmem := (mem_upperRosserBoundaryChains_iff hqs hqprime hqmin).1
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
            have hrec := (upperRosserBoundaryChain_cons_cons_iff
              (hprime p₀ hp₀P).pos (hprime p₁ hp₁P).pos).1 hmem.2.2.2
            refine ⟨p₀, hp₀P, p₁, hp₁P, hrec.1, hrec.2.2.1, xs, rfl, ?_⟩
            apply Finset.mem_filter.mpr
            refine ⟨(mem_upperRosserBoundaryChains_iff ?_ hqprime ?_).2 ?_, ?_⟩
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
    have hxsMem := (mem_upperRosserBoundaryChains_iff
      (by
        intro hq
        exact hqs (Finset.mem_filter.mp hq).1)
      hqprime
      (fun p hp => hqmin p (Finset.mem_filter.mp hp).1)).1
        (Finset.mem_filter.mp hxs).1
    have hxslt : ∀ p ∈ xs, p < p₁ := by
      intro p hp
      exact (Finset.mem_filter.mp (hxsMem.2.2.1 (by simpa using hp))).2
    have hchain : UpperRosserBoundaryChain D q (p₀ :: p₁ :: xs) :=
      (upperRosserBoundaryChain_cons_cons_iff
        (hprime p₀ hp₀P).pos (hprime p₁ hp₁P).pos).2
          ⟨h10, hxslt, hhead, hxsMem.2.2.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_upperRosserBoundaryChains_iff hqs hqprime hqmin).2 ?_, ?_⟩
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

/-- Exact finite Buchstab recursion for the selected density mass.  A positive
depth peels the two largest selected primes and leaves the same boundary mass at
the ceiling-divided level, with all remaining primes below the second one. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_succ
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) (k : ℕ) :
    upperRosserBoundaryChainsFixedDepthDensity nu D q P (k + 1) =
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        nu p₀ * nu p₁ *
          upperRosserBoundaryChainsFixedDepthDensity nu
            (D ⌈/⌉ (p₀ * p₁)) q (P.filter (fun p => p < p₁)) k := by
  classical
  let A := (upperRosserBoundaryChains D q P).filter
    (fun l => l.length = 2 * (k + 1))
  let B : Finset (Σ _p₀ : ℕ, Σ _p₁ : ℕ, List ℕ) :=
    P.sigma fun p₀ =>
      (P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D)).sigma fun p₁ =>
        (upperRosserBoundaryChains (D ⌈/⌉ (p₀ * p₁)) q
          (P.filter (fun p => p < p₁))).filter
            (fun xs => xs.length = 2 * k)
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
      have hdecomp := (mem_upperRosserBoundaryChains_fixedDepth_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      simpa [encode, B, h10, hhead, hp₀, hp₁] using hxs
    · rintro ⟨p₀, p₁, xs⟩ hb
      simp only [B, Finset.mem_sigma, Finset.mem_filter] at hb
      exact (mem_upperRosserBoundaryChains_fixedDepth_succ_iff
        hqs hqprime hprime hqmin k).2
          ⟨p₀, hb.1, p₁, hb.2.1.1, hb.2.1.2.1, hb.2.1.2.2,
            xs, rfl, Finset.mem_filter.mpr hb.2.2⟩
    · intro l hl
      have hdecomp := (mem_upperRosserBoundaryChains_fixedDepth_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      rfl
    · rintro ⟨p₀, p₁, xs⟩ hb
      rfl
    · intro l hl
      have hdecomp := (mem_upperRosserBoundaryChains_fixedDepth_succ_iff
        hqs hqprime hprime hqmin k).1 (by simpa [A] using hl)
      rcases hdecomp with ⟨p₀, hp₀, p₁, hp₁, h10, hhead, xs, rfl, hxs⟩
      simp [encode, mul_assoc]
  rw [upperRosserBoundaryChainsFixedDepthDensity]
  change ∑ l ∈ A, (l.map nu).prod = _
  rw [hsum]
  simp only [B, Finset.sum_sigma]
  simp_rw [upperRosserBoundaryChainsFixedDepthDensity, Finset.mul_sum]

/-- Exact finite Buchstab--Rosser recursion on the relative Euler-product scale.
The transition keeps the quotient between the residual and ambient Euler
products, and therefore retains every skipped-prime inverse factor. -/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_succ
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) (k : ℕ) :
    upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q P (k + 1) =
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        upperRosserBoundaryRelativePairTransition nu P p₀ p₁ *
          upperRosserBoundaryChainsFixedDepthRelativeDensity nu
            (D ⌈/⌉ (p₀ * p₁)) q (P.filter (fun p => p < p₁)) k := by
  rw [upperRosserBoundaryChainsFixedDepthRelativeDensity,
    upperRosserBoundaryChainsFixedDepthDensity_succ
      nu hqs hqprime hprime hqmin k,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  have hres :
      (∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hfactor p (Finset.mem_filter.mp hp).1
  unfold upperRosserBoundaryRelativePairTransition
    upperRosserBoundaryChainsFixedDepthRelativeDensity
  field_simp [hres]

/-- Relative pair transitions are nonnegative under the natural local-density
bounds. -/
theorem upperRosserBoundaryRelativePairTransition_nonneg
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (hnuOne : ∀ p ∈ P, nu p ≤ 1) :
    0 ≤ upperRosserBoundaryRelativePairTransition nu P p₀ p₁ := by
  unfold upperRosserBoundaryRelativePairTransition
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (hnu p₀ hp₀) (hnu p₁ hp₁)
    · apply Finset.prod_nonneg
      intro p hp
      exact sub_nonneg.mpr (hnuOne p (Finset.mem_filter.mp hp).1)
  · apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hnuOne p hp)

/-- Monotone interface for the relative Buchstab--Rosser recursion.  Any
majorant for the residual relative state propagates through the exact,
nonnegative skipped-prime transitions. -/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_succ_le
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (hnuOne : ∀ p ∈ P, nu p ≤ 1)
    (F : ℕ → ℕ → ℝ) (k : ℕ)
    (hF : ∀ p₀ ∈ P, ∀ p₁ ∈ P, p₁ < p₀ → p₀ ^ 3 < D →
      upperRosserBoundaryChainsFixedDepthRelativeDensity nu
          (D ⌈/⌉ (p₀ * p₁)) q (P.filter (fun p => p < p₁)) k ≤
        F p₀ p₁) :
    upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q P (k + 1) ≤
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        upperRosserBoundaryRelativePairTransition nu P p₀ p₁ * F p₀ p₁ := by
  rw [upperRosserBoundaryChainsFixedDepthRelativeDensity_succ
    nu hqs hqprime hprime hqmin hfactor k]
  apply Finset.sum_le_sum
  intro p₀ hp₀
  apply Finset.sum_le_sum
  intro p₁ hp₁
  have hp₁' := Finset.mem_filter.mp hp₁
  exact mul_le_mul_of_nonneg_left
    (hF p₀ hp₀ p₁ hp₁'.1 hp₁'.2.1 hp₁'.2.2)
    (upperRosserBoundaryRelativePairTransition_nonneg
      nu hp₀ hp₁'.1 hnu hnuOne)

/-- Monotone form of the finite Buchstab recursion.  This is the induction
interface for replacing every residual discrete mass by a continuous majorant. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_succ_le
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hqs : q ∉ P)
    (hqprime : q.Prime) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) (hnu : ∀ p ∈ P, 0 ≤ nu p)
    (F : ℕ → ℕ → ℝ) (k : ℕ)
    (hF : ∀ p₀ ∈ P, ∀ p₁ ∈ P, p₁ < p₀ → p₀ ^ 3 < D →
      upperRosserBoundaryChainsFixedDepthDensity nu
          (D ⌈/⌉ (p₀ * p₁)) q (P.filter (fun p => p < p₁)) k ≤
        F p₀ p₁) :
    upperRosserBoundaryChainsFixedDepthDensity nu D q P (k + 1) ≤
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        nu p₀ * nu p₁ * F p₀ p₁ := by
  rw [upperRosserBoundaryChainsFixedDepthDensity_succ
    nu hqs hqprime hprime hqmin k]
  apply Finset.sum_le_sum
  intro p₀ hp₀
  apply Finset.sum_le_sum
  intro p₁ hp₁
  apply mul_le_mul_of_nonneg_left
  · exact hF p₀ hp₀ p₁ (Finset.mem_filter.mp hp₁).1
      (Finset.mem_filter.mp hp₁).2.1 (Finset.mem_filter.mp hp₁).2.2
  · exact mul_nonneg (hnu p₀ hp₀) (hnu p₁ (Finset.mem_filter.mp hp₁).1)

/-- The depth-zero discrete boundary mass is exactly the terminal cubic shell. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_zero
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hD : 1 < D) (hqs : q ∉ P) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) :
    upperRosserBoundaryChainsFixedDepthDensity nu D q P 0 =
      if D ≤ q ^ 3 then 1 else 0 := by
  have hcarrier :
      (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = 2 * 0) =
        if D ≤ q ^ 3 then {[]} else ∅ := by
    ext l
    rw [Finset.mem_filter]
    by_cases hcube : D ≤ q ^ 3
    · rw [if_pos hcube]
      constructor
      · rintro ⟨hl, hlen⟩
        have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst l
        simp
      · intro hl
        have hl0 : l = [] := by simpa using hl
        subst l
        refine ⟨(mem_upperRosserBoundaryChains_iff hqs hqprime hqmin).2 ?_,
          by simp⟩
        refine ⟨by simp, ?_, by simp, ?_⟩
        · intro i
          exact Fin.elim0 i
        · refine ⟨?_, by simp, by simpa using hD, ?_, by simpa using hcube⟩
          · intro i
            exact Fin.elim0 i
          · intro i
            exact Fin.elim0 i
    · rw [if_neg hcube]
      constructor
      · rintro ⟨hl, hlen⟩
        have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst l
        have hmem :=
          (mem_upperRosserBoundaryChains_iff hqs hqprime hqmin).1 hl
        have hterminal := (hmem.2.2.2).2.2.2.2
        exact (hcube (by simpa using hterminal)).elim
      · simp
  rw [upperRosserBoundaryChainsFixedDepthDensity, hcarrier]
  split_ifs <;> simp

/-- At depth zero the relative density is exactly the terminal shell times the
inverse ambient Euler product. -/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_zero
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hD : 1 < D) (hqs : q ∉ P) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) :
    upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q P 0 =
      if D ≤ q ^ 3 then (∏ p ∈ P, (1 - nu p))⁻¹ else 0 := by
  rw [upperRosserBoundaryChainsFixedDepthRelativeDensity,
    upperRosserBoundaryChainsFixedDepthDensity_zero nu hD hqs hqprime hqmin]
  split_ifs <;> simp

/-- Summing the depth-zero boundary density over the distinguished prime collapses
exactly to the terminal cubic shell. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero
    (nu w : ℕ → ℝ) {D : ℕ} {P : Finset ℕ}
    (hD : 1 < D) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ q ∈ P, w q *
        upperRosserBoundaryChainsFixedDepthDensity nu D q
          (P.filter (fun p => q < p)) 0 =
      ∑ q ∈ P.filter (fun q => D ≤ q ^ 3), w q := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  rw [upperRosserBoundaryChainsFixedDepthDensity_zero nu hD
    (by simp) (hprime q hq)]
  · by_cases hcube : D ≤ q ^ 3 <;> simp [hcube]
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.le

/-- Exact outer form of the finite Buchstab recursion.  It simultaneously peels
the distinguished prime and the first pair of every positive-depth boundary
chain, leaving a residual depth-`2k` density at the ceiling-divided level. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ
    (nu w : ℕ → ℝ) {D : ℕ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (k : ℕ) :
    ∑ q ∈ P, w q *
        upperRosserBoundaryChainsFixedDepthDensity nu D q
          (P.filter (fun p => q < p)) (k + 1) =
      ∑ q ∈ P, w q *
        (∑ p₀ ∈ P.filter (fun p => q < p),
          ∑ p₁ ∈ (P.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            nu p₀ * nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((P.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
  classical
  apply Finset.sum_congr rfl
  intro q hq
  rw [upperRosserBoundaryChainsFixedDepthDensity_succ nu
    (by simp) (hprime q hq)]
  · intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.le

/-- The discrete depth-zero shell is bounded by the base continuous boundary
mass after passage to logarithmic coordinates. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux
    (nu : ℕ → ℝ) {z Δ s a b : ℝ} {q D : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z)
    (ha : a = Real.log q / Real.log z) (hsnonneg : 0 ≤ s)
    (hD : D = Nat.floor Δ + 1) (hDlarge : 1 < D)
    (hqs : q ∉ P) (hqprime : q.Prime) (hqmin : ∀ p ∈ P, q ≤ p) :
    upperRosserBoundaryChainsFixedDepthDensity nu D q P 0 ≤
      upperRosserBoundaryMassAux 0 s a b := by
  rw [upperRosserBoundaryChainsFixedDepthDensity_zero nu hDlarge hqs hqprime
      hqmin,
    upperRosserBoundaryMassAux_zero]
  by_cases hcube : D ≤ q ^ 3
  · rw [if_pos hcube]
    have hcube' : Nat.floor Δ + 1 ≤ q ^ 3 := by simpa [hD] using hcube
    have hterminal := log_div_log_lt_of_floor_add_one_le hz hΔ hcube'
    have hterminal' : s < 3 * a := by
      rw [hs, ha]
      convert hterminal using 1
      rw [Nat.cast_pow, Real.log_pow]
      ring
    rw [if_pos ⟨hsnonneg, hterminal'⟩]
  · rw [if_neg hcube]
    split_ifs <;> norm_num

/-- Exact injective reindexing of the boundary powerset sum by canonical
decreasing chains. -/
theorem sum_upperRosserBoundary_eq_sum_chains
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) :
    ∑ u ∈ P.powerset.filter (UpperRosserBoundarySet D q),
        ∏ p ∈ u, w p =
      ∑ l ∈ upperRosserBoundaryChains D q P, (l.map w).prod := by
  rw [upperRosserBoundaryChains, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    simpa using List.prod_toFinset w (Finset.sort_nodup u (· ≥ ·))
  · intro u hu v hv huv
    have := congrArg List.toFinset huv
    simpa using this

/-- A canonical boundary chain cannot be longer than its ambient finite prime
set. -/
theorem upperRosserBoundaryChains_length_le
    {D q : ℕ} {P : Finset ℕ} {l : List ℕ}
    (hl : l ∈ upperRosserBoundaryChains D q P) :
    l.length ≤ P.card := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
  rw [Finset.length_sort]
  exact Finset.card_le_card
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1)

/-- Every upper Rosser boundary chain has even length. -/
theorem upperRosserBoundaryChains_length_even
    {D q : ℕ} {P : Finset ℕ} {l : List ℕ}
    (hl : l ∈ upperRosserBoundaryChains D q P) :
    Even l.length := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
  simpa using (Finset.mem_filter.mp hu).2.1

/-- A fixed-depth selected boundary density is nonnegative when all ambient
prime weights are nonnegative. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_nonneg
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (k : ℕ) :
    0 ≤ upperRosserBoundaryChainsFixedDepthDensity nu D q P k := by
  unfold upperRosserBoundaryChainsFixedDepthDensity
  apply Finset.sum_nonneg
  intro l hl
  apply List.prod_nonneg
  intro r hr
  rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
  apply hnu p
  have hchain := Finset.mem_filter.mp hl |>.1
  obtain ⟨u, hu, hsort⟩ := Finset.mem_image.mp hchain
  have hlu : l.toFinset = u := by
    rw [← hsort]
    simp
  have huP : u ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
  apply huP
  rw [← hlu]
  simpa using hp

/-- Relative fixed-depth boundary densities are nonnegative under the natural
local-density bounds. -/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_nonneg
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (hnuOne : ∀ p ∈ P, nu p ≤ 1) (k : ℕ) :
    0 ≤ upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q P k := by
  unfold upperRosserBoundaryChainsFixedDepthRelativeDensity
  apply div_nonneg
  · exact upperRosserBoundaryChainsFixedDepthDensity_nonneg nu hnu k
  · apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hnuOne p hp)

/-- Fixed-depth boundary-chain density is monotone in every nonnegative prime
weight on its ambient carrier. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_mono
    {f g : ℕ → ℝ} {D q k : ℕ} {P : Finset ℕ}
    (hf : ∀ p ∈ P, 0 ≤ f p) (hfg : ∀ p ∈ P, f p ≤ g p) :
    upperRosserBoundaryChainsFixedDepthDensity f D q P k ≤
      upperRosserBoundaryChainsFixedDepthDensity g D q P k := by
  classical
  unfold upperRosserBoundaryChainsFixedDepthDensity
  apply Finset.sum_le_sum
  intro l hl
  -- Every entry of the chain belongs to the same ambient prime set.
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hl).1
  have huP : u ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
  apply List.prod_map_le_prod_map₀
  · intro p hp
    exact hf p (huP (by simpa using hp))
  · intro p hp
    exact hfg p (huP (by simpa using hp))

/-- A fixed-depth selected boundary density vanishes once twice the depth
exceeds the number of available ambient primes. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
    (nu : ℕ → ℝ) {D q k : ℕ} {P : Finset ℕ} (hk : P.card < 2 * k) :
    upperRosserBoundaryChainsFixedDepthDensity nu D q P k = 0 := by
  unfold upperRosserBoundaryChainsFixedDepthDensity
  apply Finset.sum_eq_zero
  intro l hl
  have hchain := Finset.mem_filter.mp hl
  have hlen := upperRosserBoundaryChains_length_le hchain.1
  omega

/-- The canonical chain sum decomposes as a finite sigma over chain length.
This is the exact finite starting point for estimating each nested Rosser
region and then controlling the tail uniformly in the length. -/
theorem sum_upperRosserBoundaryChains_by_length
    (D q : ℕ) (P : Finset ℕ) (f : List ℕ → ℝ) :
    ∑ l ∈ upperRosserBoundaryChains D q P, f l =
      ∑ ell ∈ Finset.range (P.card + 1),
        ∑ l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = ell), f l := by
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hl
    have hle := upperRosserBoundaryChains_length_le hl
    exact ⟨hl, by omega⟩
  · exact fun hl => hl.1

/-- Since boundary chains have even cardinality, the depth sigma may be
restricted exactly to even lengths. -/
theorem sum_upperRosserBoundaryChains_by_even_length
    (D q : ℕ) (P : Finset ℕ) (f : List ℕ → ℝ) :
    ∑ l ∈ upperRosserBoundaryChains D q P, f l =
      ∑ ell ∈ (Finset.range (P.card + 1)).filter Even,
        ∑ l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = ell), f l := by
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hl
    have hle := upperRosserBoundaryChains_length_le hl
    exact ⟨hl, by omega, upperRosserBoundaryChains_length_even hl⟩
  · exact fun hl => hl.1

/-- The canonical boundary-chain sum decomposes exactly by pair depth.  This
reindexes the even chain length `2k` directly by the recursion parameter `k`. -/
theorem sum_upperRosserBoundaryChains_by_depth
   (D q : ℕ) (P : Finset ℕ) (f : List ℕ → ℝ) :
   ∑ l ∈ upperRosserBoundaryChains D q P, f l =
     ∑ k ∈ Finset.range (P.card + 1),
     ∑ l ∈ (upperRosserBoundaryChains D q P).filter
       (fun l => l.length = 2 * k), f l := by
  calc
   _ = ∑ k ∈ Finset.range (P.card + 1),
       ∑ l ∈ (upperRosserBoundaryChains D q P).filter
         (fun l => l.length / 2 = k), f l := by
     rw [Finset.sum_fiberwise_eq_sum_filter]
     congr 1
     ext l
     simp only [Finset.mem_filter, Finset.mem_range]
     constructor
     · intro hl
       refine ⟨hl, ?_⟩
       have hlen := upperRosserBoundaryChains_length_le hl
       have hdiv : l.length / 2 ≤ l.length := Nat.div_le_self _ _
       omega
     · exact fun hl => hl.1
   _ = _ := by
     apply Finset.sum_congr rfl
     intro k hk
     apply Finset.sum_congr
     · ext l
       simp only [Finset.mem_filter]
       constructor
       · rintro ⟨hl, hdiv⟩
         refine ⟨hl, ?_⟩
         obtain ⟨j, hj⟩ := upperRosserBoundaryChains_length_even hl
         omega
       · rintro ⟨hl, hlen⟩
         exact ⟨hl, by omega⟩
     · intro l hl
       rfl

/-- The complete selected boundary density is the finite sum of its exact
pair-depth slices. -/
theorem sum_upperRosserBoundary_eq_sum_fixedDepthDensity
   (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) :
   ∑ u ∈ P.powerset.filter (UpperRosserBoundarySet D q),
     ∏ p ∈ u, nu p =
     ∑ k ∈ Finset.range (P.card + 1),
     upperRosserBoundaryChainsFixedDepthDensity nu D q P k := by
  rw [sum_upperRosserBoundary_eq_sum_chains,
   sum_upperRosserBoundaryChains_by_depth]
  rfl

/-- Exact decomposition of a normalized boundary density into its finite
relative pair-depth slices. -/
theorem upperRosserBoundaryDensity_div_eulerProduct_eq_sum_fixedDepthRelativeDensity
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) :
    (∑ u ∈ P.powerset.filter (UpperRosserBoundarySet D q),
        ∏ p ∈ u, nu p) /
        ∏ p ∈ P, (1 - nu p) =
      ∑ k ∈ Finset.range (P.card + 1),
        upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q P k := by
  rw [sum_upperRosserBoundary_eq_sum_fixedDepthDensity, Finset.sum_div]
  rfl

/-- At a fixed depth, the canonical decreasing-chain sum is exactly the
corresponding cardinality slice of the boundary powerset. -/
theorem sum_upperRosserBoundaryChains_fixed_length
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) (ell : ℕ) :
    ∑ l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = ell), (l.map w).prod =
      ∑ u ∈ (P.powerset.filter (UpperRosserBoundarySet D q)).filter
          (fun u => u.card = ell), ∏ p ∈ u, w p := by
  rw [upperRosserBoundaryChains, Finset.filter_image]
  rw [Finset.sum_image]
  · simp_rw [Finset.length_sort]
    apply Finset.sum_congr rfl
    intro u hu
    symm
    simpa using List.prod_toFinset w (Finset.sort_nodup u (· ≥ ·))
  · intro u hu v hv huv
    have h := congrArg List.toFinset huv
    simpa using h

/-- Dropping the Rosser inequalities at a fixed depth leaves the full elementary
symmetric sum.  This is the finite domination needed before applying a
factorial/geometric tail estimate. -/
theorem sum_upperRosserBoundaryChains_fixed_length_le_powersetCard
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (ell : ℕ) :
    ∑ l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = ell), (l.map w).prod ≤
      ∑ u ∈ P.powersetCard ell, ∏ p ∈ u, w p := by
  rw [sum_upperRosserBoundaryChains_fixed_length]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard] at hu ⊢
    exact ⟨hu.1.1, hu.2⟩
  · intro u hu hnot
    apply Finset.prod_nonneg
    intro p hp
    exact hw p ((Finset.mem_powersetCard.mp hu).1 hp)

/-- The elementary symmetric sum of fixed degree is bounded by the corresponding
power sum, with the factorial accounting for all orderings of each subset. -/
theorem factorial_mul_sum_powersetCard_prod_le_pow_sum
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (ell : ℕ) :
    (ell.factorial : ℝ) * (∑ u ∈ P.powersetCard ell, ∏ p ∈ u, w p) ≤
     (∑ p ∈ P, w p) ^ ell := by
  induction P using Finset.induction generalizing ell with
  | empty =>
     cases ell with
     | zero => simp
     | succ n => rw [Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | @insert a P ha ih =>
     have hwa : 0 ≤ w a := hw a (by simp)
     have hwP : ∀ p ∈ P, 0 ≤ w p := fun p hp => hw p (by simp [hp])
     cases ell with
     | zero => simp
     | succ n =>
         rw [Finset.powersetCard_succ_insert ha]
         have hdisj : Disjoint (P.powersetCard n.succ)
             ((P.powersetCard n).image (insert a)) := by
           rw [Finset.disjoint_left]
           intro u hu hu'
           obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu'
           have hva : a ∈ insert a v := Finset.mem_insert_self a v
           exact ha ((Finset.mem_powersetCard.mp hu).1 hva)
         rw [Finset.sum_union hdisj]
         have himage :
             ∑ u ∈ (P.powersetCard n).image (insert a), ∏ p ∈ u, w p =
               w a * ∑ u ∈ P.powersetCard n, ∏ p ∈ u, w p := by
           rw [Finset.sum_image]
           · rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro u hu
             have hau : a ∉ u :=
               fun hau => ha ((Finset.mem_powersetCard.mp hu).1 hau)
             rw [Finset.prod_insert hau]
           · intro u hu v hv huv
             have hau : a ∉ u :=
               fun hau => ha ((Finset.mem_powersetCard.mp hu).1 hau)
             have hav : a ∉ v :=
               fun hav => ha ((Finset.mem_powersetCard.mp hv).1 hav)
             have h := congrArg (fun t => t.erase a) huv
             simpa [hau, hav] using h
         rw [himage]
         have ih_succ := ih hwP n.succ
         have ih_n := ih hwP n
         have hsum_nonneg : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg hwP
         calc
           (n.succ.factorial : ℝ) *
               ((∑ u ∈ P.powersetCard n.succ, ∏ p ∈ u, w p) +
                 w a * ∑ u ∈ P.powersetCard n, ∏ p ∈ u, w p)
               = (n.succ.factorial : ℝ) *
                   (∑ u ∈ P.powersetCard n.succ, ∏ p ∈ u, w p) +
                 (n.succ : ℝ) * w a *
                   ((n.factorial : ℝ) *
                     ∑ u ∈ P.powersetCard n, ∏ p ∈ u, w p) := by
                   rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
                   ring
           _ ≤ (∑ p ∈ P, w p) ^ n.succ +
                 (n.succ : ℝ) * w a * (∑ p ∈ P, w p) ^ n :=
                   add_le_add ih_succ
                     (mul_le_mul_of_nonneg_left ih_n
                       (mul_nonneg (Nat.cast_nonneg _) hwa))
           _ ≤ ((∑ p ∈ P, w p) + w a) ^ n.succ := by
                   have hpow := pow_add_mul_le_add_pow hsum_nonneg
                     (add_nonneg (mul_nonneg (by norm_num) hsum_nonneg) hwa) n.succ
                   rw [Nat.succ_sub_one] at hpow
                   simpa [mul_assoc, mul_left_comm, mul_comm] using hpow
           _ = (∑ p ∈ insert a P, w p) ^ n.succ := by
                   rw [Finset.sum_insert ha, add_comm]

/-- A fixed-depth upper Rosser boundary sum has factorial decay in its depth,
uniformly in the Rosser parameters. -/
theorem factorial_mul_sum_upperRosserBoundaryChains_fixed_length_le_pow_sum
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (ell : ℕ) :
    (ell.factorial : ℝ) *
       (∑ l ∈ (upperRosserBoundaryChains D q P).filter
         (fun l => l.length = ell), (l.map w).prod) ≤
     (∑ p ∈ P, w p) ^ ell := by
  calc
    (ell.factorial : ℝ) *
       (∑ l ∈ (upperRosserBoundaryChains D q P).filter
         (fun l => l.length = ell), (l.map w).prod) ≤
     (ell.factorial : ℝ) * (∑ u ∈ P.powersetCard ell, ∏ p ∈ u, w p) :=
       mul_le_mul_of_nonneg_left
         (sum_upperRosserBoundaryChains_fixed_length_le_powersetCard D q P w hw ell)
         (Nat.cast_nonneg ell.factorial)
    _ ≤ (∑ p ∈ P, w p) ^ ell :=
     factorial_mul_sum_powersetCard_prod_le_pow_sum P w hw ell

/-- Division form of the fixed-depth factorial estimate. -/
theorem sum_upperRosserBoundaryChains_fixed_length_le_pow_sum_div_factorial
    (D q : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (ell : ℕ) :
    ∑ l ∈ (upperRosserBoundaryChains D q P).filter
          (fun l => l.length = ell), (l.map w).prod ≤
      (∑ p ∈ P, w p) ^ ell / (ell.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ell.factorial)]
  simpa [mul_comm] using
    factorial_mul_sum_upperRosserBoundaryChains_fixed_length_le_pow_sum
      D q P w hw ell

/-- The depth-zero upper Rosser boundary is the elementary cubic cutoff. -/
theorem upperRosserBoundarySet_empty_iff
    {D q : ℕ} (hD : 1 < D) (hqprime : q.Prime) :
    UpperRosserBoundarySet D q ∅ ↔ D ≤ q ^ 3 := by
  rw [upperRosserBoundarySet_iff_cube_le (by simp) hqprime (by simp)]
  simp [hD, UpperRosserAdmissibleSet]

/-- The largest prime in any nonempty upper Rosser boundary tail is below the
cubic level.  This is the outer support inequality for arbitrary-depth boundary
chains, independent of the distinguished prime `q`. -/
theorem upperRosserBoundarySet_max_cube_lt
    {D q : ℕ} {s : Finset ℕ} (hs : s.Nonempty)
    (hboundary : UpperRosserBoundarySet D q s) :
    (s.max' hs) ^ 3 < D := by
  let t := s.max' hs
  have ht : t ∈ s := Finset.max'_mem s hs
  have hfilter : s.filter (fun r => t ≤ r) = {t} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, htr⟩
      exact le_antisymm (Finset.le_max' s r hr) htr
    · rintro rfl
      exact ⟨ht, le_rfl⟩
  have htest := hboundary.2.2.1 t ht (by simp [hfilter])
  rw [hfilter] at htest
  simpa [t, pow_succ, mul_assoc] using htest

/-- Every selected prime in an upper Rosser boundary tail lies below `D^(1/3)`
in the integral form `p³ < D`. -/
theorem upperRosserBoundarySet_mem_cube_lt
    {D q p : ℕ} {s : Finset ℕ} (hp : p ∈ s)
    (hboundary : UpperRosserBoundarySet D q s) :
    p ^ 3 < D := by
  have hs : s.Nonempty := ⟨p, hp⟩
  exact lt_of_le_of_lt
    (Nat.pow_le_pow_left (Finset.le_max' s p hp) 3)
    (upperRosserBoundarySet_max_cube_lt hs hboundary)

/-- At real level `Δ = z^s`, every prime in a boundary tail has logarithmic
coordinate at most `s / 3`.  The natural level `⌊Δ⌋ + 1` introduces no loss in
this upper support bound. -/
theorem upperRosserBoundarySet_mem_log_div_le_third
    {z Δ s : ℝ} {q p : ℕ} {t : Finset ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z)
    (hpPrime : p.Prime) (hp : p ∈ t)
    (hboundary : UpperRosserBoundarySet (Nat.floor Δ + 1) q t) :
    Real.log p / Real.log z ≤ s / 3 := by
  have hcube := upperRosserBoundarySet_mem_cube_lt hp hboundary
  have hcubeFloor : p ^ 3 ≤ Nat.floor Δ := by omega
  have hcubeReal : (p : ℝ) ^ 3 ≤ Δ := by
    calc
      (p : ℝ) ^ 3 = ((p ^ 3 : ℕ) : ℝ) := by norm_num
      _ ≤ (Nat.floor Δ : ℝ) := by exact_mod_cast hcubeFloor
      _ ≤ Δ := Nat.floor_le hΔ.le
  have hpRpos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hpCubePos : (0 : ℝ) < (p : ℝ) ^ 3 := pow_pos hpRpos 3
  have hlogle :=
    Real.strictMonoOn_log.monotoneOn hpCubePos hΔ hcubeReal
  rw [Real.log_pow] at hlogle
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hdiv :
      3 * Real.log p / Real.log z ≤ Real.log Δ / Real.log z :=
    (div_le_div_iff_of_pos_right hlogz).2 (by
      norm_num at hlogle ⊢
      exact hlogle)
  rw [hs]
  calc
    Real.log p / Real.log z =
        (3 * Real.log p / Real.log z) / 3 := by
      field_simp [hlogz.ne']
    _ ≤ (Real.log Δ / Real.log z) / 3 := by linarith

/-- For an increasing two-prime tail, upper Rosser admissibility is exactly
the cubic restriction on its larger prime. -/
theorem upperRosserAdmissibleSet_pair_iff
    {D r t : ℕ} (hrt : r < t) :
    UpperRosserAdmissibleSet D {r, t} ↔ t ^ 3 < D := by
  have hrt_ne : r ≠ t := ne_of_lt hrt
  have hfilter_r :
      ({r, t} : Finset ℕ).filter (fun x => r ≤ x) = {r, t} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro hx
      refine ⟨hx, ?_⟩
      rcases hx with rfl | rfl
      · exact le_rfl
      · exact hrt.le
  have hfilter_t :
      ({r, t} : Finset ℕ).filter (fun x => t ≤ x) = {t} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hx⟩
      · omega
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, le_rfl⟩
  constructor
  · intro h
    have ht := h t (by simp) (by simp [hfilter_t])
    simpa [hfilter_t, pow_succ, mul_assoc] using ht
  · intro ht p hp hodd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exfalso
      apply hodd
      simp [hfilter_r, hrt_ne]
    · simpa [hfilter_t, pow_succ, mul_assoc] using ht

/-- The two-prime boundary is the first nontrivial Rosser chain: if
`q < r < t`, then `t³ < D ≤ q³rt`. -/
theorem upperRosserBoundarySet_pair_iff
    {D q r t : ℕ} (hqprime : q.Prime) (htprime : t.Prime)
    (hqr : q < r) (hrt : r < t) :
    UpperRosserBoundarySet D q {r, t} ↔
      t ^ 3 < D ∧ D ≤ r * t * q ^ 3 := by
  have hqr_ne : q ≠ r := ne_of_lt hqr
  have hqt_ne : q ≠ t := ne_of_lt (hqr.trans hrt)
  have hrt_ne : r ≠ t := ne_of_lt hrt
  have hprod : ({r, t} : Finset ℕ).prod id = r * t := by
    simp [hrt_ne]
  have hcard : ({r, t} : Finset ℕ).card = 2 := by
    simp [hrt_ne]
  rw [upperRosserBoundarySet_iff_cube_le
      (by simp [hqr_ne, hqt_ne]) hqprime,
    upperRosserAdmissibleSet_pair_iff hrt, hprod, hcard]
  · have hprod_lt : r * t < t ^ 3 := by
      calc
        r * t < t * t := (Nat.mul_lt_mul_right htprime.pos).2 hrt
        _ ≤ (t * t) * t := Nat.le_mul_of_pos_right (t * t) htprime.pos
        _ = t ^ 3 := by ring
    constructor
    · rintro ⟨heven, hprodD, htD, hboundary⟩
      exact ⟨htD, hboundary⟩
    · rintro ⟨htD, hboundary⟩
      exact ⟨by norm_num, hprod_lt.trans htD, htD, hboundary⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hqr.le
    · exact (hqr.trans hrt).le

/-- Pairing a set with the set obtained by adjoining a new least prime produces
the Euler factor `1 - nuq`, apart from the explicit even Rosser boundary. -/
theorem upperRosserSetWeight_pair_eq_euler_add_boundary
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqD : q < D) (hqmin : ∀ p ∈ s, q ≤ p) (nuq : ℝ) :
    upperRosserSetWeight D s +
        nuq * upperRosserSetWeight D (insert q s) =
      (1 - nuq) * upperRosserSetWeight D s +
        if UpperRosserBoundarySet D q s then nuq else 0 := by
  have hcard : (insert q s).card = s.card + 1 :=
    Finset.card_insert_of_notMem hqs
  by_cases hbase :
      s.prod id < D ∧ UpperRosserAdmissibleSet D s
  · by_cases heven : Even s.card
    · have hodd : ¬Even (insert q s).card := by
        rw [hcard, Nat.even_add_one]
        exact not_not_intro heven
      have hsD : (∏ p ∈ s, p) < D := by
        simpa only [id_eq] using hbase.1
      by_cases hins :
          (insert q s).prod id < D ∧
            UpperRosserAdmissibleSet D (insert q s)
      · have hinsD : (∏ p ∈ insert q s, p) < D := by
          simpa only [id_eq] using hins.1
        simp [upperRosserSetWeight, UpperRosserBoundarySet, hsD, hbase.2,
          heven, hinsD, hins.2, hodd]
        ring
      · have hins' :
            ¬((∏ p ∈ insert q s, p) < D ∧
              UpperRosserAdmissibleSet D (insert q s)) := by
          simpa only [id_eq] using hins
        simp [upperRosserSetWeight, UpperRosserBoundarySet, hsD, hbase.2,
          heven, hins']
    · have hinsEven : Even (insert q s).card := by
        rw [hcard, Nat.even_add_one]
        exact heven
      have hins :
          (insert q s).prod id < D ∧
            UpperRosserAdmissibleSet D (insert q s) :=
        ⟨prod_insert_min_lt_of_upperRosserAdmissibleSet_odd
            hqs hqprime hqD hqmin hbase.2 heven,
          upperRosserAdmissibleSet_insert_min_of_odd
            hqs hqmin hbase.2 heven⟩
      have hsD : (∏ p ∈ s, p) < D := by
        simpa only [id_eq] using hbase.1
      have hinsD : (∏ p ∈ insert q s, p) < D := by
        simpa only [id_eq] using hins.1
      simp [upperRosserSetWeight, UpperRosserBoundarySet, hsD, hbase.2,
        heven, hinsD, hins.2, hinsEven]
      ring
  · have hins :
        ¬((insert q s).prod id < D ∧
          UpperRosserAdmissibleSet D (insert q s)) := by
      intro hins
      apply hbase
      refine ⟨?_, upperRosserAdmissibleSet_of_insert_min hqs hqmin hins.2⟩
      exact lt_of_le_of_lt (by
        rw [Finset.prod_insert hqs]
        exact Nat.le_mul_of_pos_left (s.prod id) hqprime.pos) hins.1
    have hbase' :
        ¬((∏ p ∈ s, p) < D ∧ UpperRosserAdmissibleSet D s) := by
      simpa only [id_eq] using hbase
    have hins' :
        ¬((∏ p ∈ insert q s, p) < D ∧
          UpperRosserAdmissibleSet D (insert q s)) := by
      simpa only [id_eq] using hins
    simp [upperRosserSetWeight, UpperRosserBoundarySet, hbase', hins']

/-- Finite Buchstab--Rosser recursion in Euler-factor form.  Removing the least
prime contributes the expected factor `1 - nu q`; the only correction is the
explicit even Rosser boundary where adjoining `q` first violates the cutoff. -/
theorem upperRosserSetDensitySum_insert_eq_euler_add_boundary
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hq : q ∉ P)
    (hqprime : q.Prime) (hqD : q < D) (hqmin : ∀ p ∈ P, q ≤ p) :
    upperRosserSetDensitySum nu D (insert q P) =
      (1 - nu q) * upperRosserSetDensitySum nu D P +
        nu q * ∑ s ∈ P.powerset.filter (UpperRosserBoundarySet D q),
          ∏ p ∈ s, nu p := by
  rw [upperRosserSetDensitySum_insert nu D q P hq]
  unfold upperRosserSetDensitySum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [upperRosserSetWeight_pair_eq_euler_add_boundary
    (fun h ↦ hq (Finset.mem_powerset.mp hs h)) hqprime hqD
    (fun p hp ↦ hqmin p (Finset.mem_powerset.mp hs hp)) (nu q)]
  by_cases hboundary : UpperRosserBoundarySet D q s
  · simp [hboundary]
    ring
  · simp [hboundary]
    ring

/-- Normalized one-prime Rosser recursion.  After division by the finite sieve
product, each peeled prime contributes its boundary mass with coefficient
`nu q / (1 - nu q)`. -/
theorem upperRosserSetDensityRatio_insert
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hq : q ∉ P)
    (hqprime : q.Prime) (hqD : q < D) (hqmin : ∀ p ∈ P, q ≤ p)
    (hqFactor : 1 - nu q ≠ 0)
    (hPFactor : (∏ p ∈ P, (1 - nu p)) ≠ 0) :
    upperRosserSetDensitySum nu D (insert q P) /
          ∏ p ∈ insert q P, (1 - nu p) =
      upperRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) +
        (nu q / (1 - nu q)) *
          ((∑ s ∈ P.powerset.filter (UpperRosserBoundarySet D q),
              ∏ p ∈ s, nu p) /
            ∏ p ∈ P, (1 - nu p)) := by
  rw [upperRosserSetDensitySum_insert_eq_euler_add_boundary nu hq
      hqprime hqD hqmin,
    Finset.prod_insert hq]
  field_simp

/-- Splitting an Euler denominator over a subset and its complement turns a
density monomial into selected prime ratios and unselected inverse factors. -/
theorem prod_nu_div_eulerProduct_eq
    (nu : ℕ → ℝ) {P s : Finset ℕ} (hs : s ⊆ P) :
    (∏ p ∈ s, nu p) / ∏ p ∈ P, (1 - nu p) =
      (∏ p ∈ s, nu p / (1 - nu p)) *
        ∏ p ∈ P \ s, (1 - nu p)⁻¹ := by
  rw [Finset.prod_div_distrib]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
  have hprod := Finset.prod_sdiff (f := fun p => (1 - nu p)⁻¹) hs
  rw [← hprod]
  ring

/-- The normalized boundary sum is a sum of path monomials: selected primes
contribute `nu p / (1 - nu p)`, while unselected tail primes contribute the
inverse Euler factor. -/
theorem upperRosserBoundaryDensity_div_eulerProduct
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) :
    (∑ s ∈ P.powerset.filter (UpperRosserBoundarySet D q),
        ∏ p ∈ s, nu p) / ∏ p ∈ P, (1 - nu p) =
      ∑ s ∈ P.powerset.filter (UpperRosserBoundarySet D q),
        (∏ p ∈ s, nu p / (1 - nu p)) *
          ∏ p ∈ P \ s, (1 - nu p)⁻¹ := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
  rw [← div_eq_mul_inv, prod_nu_div_eulerProduct_eq nu hsub]

/-- Exact path expansion of the normalized upper Rosser density.  The primes
are peeled in increasing order; the tail after `q` is therefore precisely the
set of primes larger than `q`.  Each term is the normalized mass of the cubic
boundary first encountered at that prime. -/
theorem upperRosserSetDensityRatio_eq_one_add_sum_boundary
    (nu : ℕ → ℝ) {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) =
      1 + ∑ q ∈ P,
        (nu q / (1 - nu q)) *
          ((∑ s ∈ (P.filter (fun p => q < p)).powerset.filter
                (UpperRosserBoundarySet D q),
              ∏ p ∈ s, nu p) /
            ∏ p ∈ P.filter (fun p => q < p), (1 - nu p)) := by
  induction P using Finset.induction_on_min with
  | empty => simp [upperRosserSetDensitySum_empty nu hD]
  | @insert q P hqmin ih =>
      have hq : q ∉ P := by
        intro hqP
        have := hqmin q hqP
        omega
      have htail : (insert q P).filter (fun p => q < p) = P := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hp, hlt⟩
          · omega
          · exact hp
        · intro hp
          exact ⟨Or.inr hp, hqmin p hp⟩
      have hfilter (r : ℕ) (hr : r ∈ P) :
          (insert q P).filter (fun p => r < p) =
            P.filter (fun p => r < p) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hp, hlt⟩
          · have := hqmin r hr
            omega
          · exact ⟨hp, hlt⟩
        · rintro ⟨hp, hlt⟩
          exact ⟨Or.inr hp, hlt⟩
      have hrec := upperRosserSetDensityRatio_insert nu hq
        (hprime q (Finset.mem_insert_self q P))
        (hpD q (Finset.mem_insert_self q P))
        (fun p hp => Nat.le_of_lt (hqmin p hp))
        (hfactor q (Finset.mem_insert_self q P))
        (Finset.prod_ne_zero_iff.mpr (fun p hp =>
          hfactor p (Finset.mem_insert_of_mem hp)))
      rw [hrec]
      rw [ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
        (fun p hp => hpD p (Finset.mem_insert_of_mem hp))
        (fun p hp => hfactor p (Finset.mem_insert_of_mem hp))]
      rw [Finset.sum_insert hq, htail]
      have hsum :
          (∑ r ∈ P,
            nu r / (1 - nu r) *
              ((∑ s ∈ ((insert q P).filter (fun p => r < p)).powerset.filter
                    (UpperRosserBoundarySet D r),
                  ∏ p ∈ s, nu p) /
                ∏ p ∈ (insert q P).filter (fun p => r < p), (1 - nu p))) =
          ∑ r ∈ P,
            nu r / (1 - nu r) *
              ((∑ s ∈ (P.filter (fun p => r < p)).powerset.filter
                    (UpperRosserBoundarySet D r),
                  ∏ p ∈ s, nu p) /
                ∏ p ∈ P.filter (fun p => r < p), (1 - nu p)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hfilter r hr]
      rw [hsum]
      ring

/-- The exact normalized upper Rosser density grouped by relative Buchstab pair
depth.  In contrast to a selected-chain majorant, each depth slice still carries
the complete Euler denominator above its distinguished prime. -/
theorem upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
    (nu : ℕ → ℝ) {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) =
      1 + ∑ q ∈ P,
        (nu q / (1 - nu q)) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity nu D q
              (P.filter (fun p => q < p)) k := by
  rw [upperRosserSetDensityRatio_eq_one_add_sum_boundary
    nu P hD hprime hpD hfactor]
  apply congrArg (fun x : ℝ => 1 + x)
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  exact upperRosserBoundaryDensity_div_eulerProduct_eq_sum_fixedDepthRelativeDensity
    nu D q (P.filter (fun p => q < p))

/-- Fully factorized Rosser path expansion.  After choosing the first boundary
prime `q`, every selected tail prime contributes its normalized density and
every skipped tail prime contributes its inverse Euler factor. -/
theorem upperRosserSetDensityRatio_eq_one_add_sum_boundaryPaths
    (nu : ℕ → ℝ) {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) =
      1 + ∑ q ∈ P,
        (nu q / (1 - nu q)) *
          ∑ s ∈ (P.filter (fun p => q < p)).powerset.filter
              (UpperRosserBoundarySet D q),
            (∏ p ∈ s, nu p / (1 - nu p)) *
              ∏ p ∈ (P.filter (fun p => q < p)) \ s,
                (1 - nu p)⁻¹ := by
  rw [upperRosserSetDensityRatio_eq_one_add_sum_boundary
    nu P hD hprime hpD hfactor]
  apply congrArg (fun x : ℝ => 1 + x)
  apply Finset.sum_congr rfl
  intro q hq
  rw [upperRosserBoundaryDensity_div_eulerProduct]

/-- The path expansion with the abstract boundary predicate eliminated.  Thus
the entire excess over the Euler product is a sum over even admissible tails in
the explicit cubic shell `D ≤ (∏ s) q ^ 3`. -/
theorem upperRosserSetDensityRatio_eq_one_add_sum_cubicBoundary
    (nu : ℕ → ℝ) {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) =
      1 + ∑ q ∈ P,
        (nu q / (1 - nu q)) *
          ((∑ u ∈ (P.filter (fun p => q < p)).powerset.filter
                (fun s => Even s.card ∧ s.prod id < D ∧
                  UpperRosserAdmissibleSet D s ∧ D ≤ s.prod id * q ^ 3),
              ∏ p ∈ u, nu p) /
            ∏ p ∈ P.filter (fun p => q < p), (1 - nu p)) := by
  rw [upperRosserSetDensityRatio_eq_one_add_sum_boundary nu P hD hprime hpD hfactor]
  apply congrArg (fun x : ℝ => 1 + x)
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  have hboundary :
      (P.filter (fun p => q < p)).powerset.filter
          (UpperRosserBoundarySet D q) =
        (P.filter (fun p => q < p)).powerset.filter
          (fun s => Even s.card ∧ s.prod id < D ∧
            UpperRosserAdmissibleSet D s ∧ D ≤ s.prod id * q ^ 3) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hs, hboundary⟩
      refine ⟨hs, (upperRosserBoundarySet_iff_cube_le ?_ (hprime q hq) ?_).mp
        hboundary⟩
      · intro hqs
        have hlt := (Finset.mem_filter.mp (hs hqs)).2
        omega
      · intro p hp
        exact Nat.le_of_lt (Finset.mem_filter.mp (hs hp)).2
    · rintro ⟨hs, hboundary⟩
      refine ⟨hs, (upperRosserBoundarySet_iff_cube_le ?_ (hprime q hq) ?_).mpr
        hboundary⟩
      · intro hqs
        have hlt := (Finset.mem_filter.mp (hs hqs)).2
        omega
      · intro p hp
        exact Nat.le_of_lt (Finset.mem_filter.mp (hs hp)).2
  rw [hboundary]

/-- Cardinality-decreasing Euler-factor recursion at the least prime. -/
theorem upperRosserSetDensitySum_min_eq_euler_add_boundary
    (nu : ℕ → ℝ) {D : ℕ} {P : Finset ℕ} (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) (hD : ∀ p ∈ P, p < D) :
    upperRosserSetDensitySum nu D P =
      (1 - nu (P.min' hP)) *
          upperRosserSetDensitySum nu D (P.erase (P.min' hP)) +
        nu (P.min' hP) *
          ∑ s ∈ (P.erase (P.min' hP)).powerset.filter
              (UpperRosserBoundarySet D (P.min' hP)),
            ∏ p ∈ s, nu p := by
  let q := P.min' hP
  let T := P.erase q
  have hqP : q ∈ P := Finset.min'_mem P hP
  have hqT : q ∉ T := by simp [T]
  have hPT : insert q T = P := Finset.insert_erase hqP
  have hqmin : ∀ p ∈ T, q ≤ p := by
    intro p hp
    exact Finset.min'_le P p (Finset.erase_subset q P hp)
  calc
    upperRosserSetDensitySum nu D P =
        upperRosserSetDensitySum nu D (insert q T) := by rw [hPT]
    _ = (1 - nu q) * upperRosserSetDensitySum nu D T +
          nu q * ∑ s ∈ T.powerset.filter (UpperRosserBoundarySet D q),
            ∏ p ∈ s, nu p :=
      upperRosserSetDensitySum_insert_eq_euler_add_boundary nu hqT
        (hprime q hqP) (hD q hqP) hqmin
    _ = (1 - nu (P.min' hP)) *
          upperRosserSetDensitySum nu D (P.erase (P.min' hP)) +
        nu (P.min' hP) *
          ∑ s ∈ (P.erase (P.min' hP)).powerset.filter
              (UpperRosserBoundarySet D (P.min' hP)),
            ∏ p ∈ s, nu p := by rfl

private theorem upperRosserSetWeight_pair_nonneg
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqD : q < D) (hqmin : ∀ p ∈ s, q ≤ p) :
    0 ≤ upperRosserSetWeight D s + upperRosserSetWeight D (insert q s) := by
  -- Specialize the Euler-factor identity to unit density: only the boundary remains.
  have hpair := upperRosserSetWeight_pair_eq_euler_add_boundary
    hqs hqprime hqD hqmin (1 : ℝ)
  simp only [one_mul, sub_self, zero_mul, zero_add] at hpair
  rw [hpair]
  split_ifs <;> norm_num

private theorem sum_upperRosserSetWeight_nonneg
    {D : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) (hD : ∀ p ∈ S, p < D) :
    0 ≤ ∑ s ∈ S.powerset, upperRosserSetWeight D s := by
  let q := S.min' hS
  let T := S.erase q
  have hqS : q ∈ S := Finset.min'_mem S hS
  have hqT : q ∉ T := by simp [T]
  have hST : insert q T = S := Finset.insert_erase hqS
  have hdis : Disjoint T.powerset (T.powerset.image (insert q)) := by
    rw [Finset.disjoint_left]
    intro s hs hsi
    have hqnot : q ∉ s :=
      fun hqs ↦ hqT (Finset.mem_powerset.mp hs hqs)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hsi
    exact hqnot (Finset.mem_insert_self q u)
  have hinj :
      Set.InjOn (insert q) (↑T.powerset : Set (Finset ℕ)) := by
    intro s hs u hu hsu
    have hqs : q ∉ s :=
      fun h ↦ hqT (Finset.mem_powerset.mp hs h)
    have hqu : q ∉ u :=
      fun h ↦ hqT (Finset.mem_powerset.mp hu h)
    have heq := congrArg (fun v : Finset ℕ ↦ v.erase q) hsu
    simpa [Finset.erase_insert, hqs, hqu] using heq
  rw [← hST, Finset.powerset_insert, Finset.sum_union hdis,
    Finset.sum_image hinj, ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro s hs
  have hsubT : s ⊆ T := Finset.mem_powerset.mp hs
  have hqs : q ∉ s := fun h ↦ hqT (hsubT h)
  apply upperRosserSetWeight_pair_nonneg hqs (hprime q hqS) (hD q hqS)
  intro p hp
  exact Finset.min'_le S p (Finset.erase_subset q S (hsubT hp))

/-- The explicit finite upper Rosser coefficient, with the standard odd-position
Rosser admissibility test and strict level support built into its definition. -/
noncomputable def upperRosserWeight (P D d : ℕ) : ℝ :=
  if d ∈ P.divisors ∧ d < D ∧ UpperRosserAdmissible D d then
    if Even d.primeFactors.card then 1 else -1
  else 0

private theorem upperRosserWeight_prod_eq_setWeight {P D : ℕ}
    (hP : Squarefree P) {s : Finset ℕ} (hsub : s ⊆ P.primeFactors) :
    upperRosserWeight P D (s.prod id) = upperRosserSetWeight D s := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (hsub hp)
  have hdiv : s.prod id ∈ P.divisors := by
    rw [Nat.mem_divisors]
    refine ⟨?_, hP.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hP]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s P.primeFactors id hsub
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  unfold upperRosserWeight upperRosserSetWeight UpperRosserAdmissible
  rw [hpf]
  simp only [hdiv, true_and]

/-- The `BoundingSieve.mainSum` of the explicit upper Rosser coefficient is
exactly its finite subset density sum.  This removes divisor arithmetic from
the analytic fundamental-lemma problem and exposes the prime-by-prime
Buchstab recursion `upperRosserSetDensitySum_insert`. -/
theorem mainSum_upperRosserWeight_eq_setDensitySum
    (S : BoundingSieve) (D : ℕ) :
    S.mainSum (upperRosserWeight S.prodPrimes D) =
      upperRosserSetDensitySum S.nu D S.prodPrimes.primeFactors := by
  unfold BoundingSieve.mainSum upperRosserSetDensitySum
  rw [Internal.sum_divisors_eq_sum_primeFactors_powerset S.prodPrimes_squarefree]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ S.prodPrimes.primeFactors :=
    Finset.mem_powerset.mp hs
  have hprime : ∀ p ∈ s, p.Prime :=
    fun p hp ↦ Nat.prime_of_mem_primeFactors (hsub hp)
  have hdiv : s.prod id ∣ S.prodPrimes := by
    rw [← Nat.prod_primeFactors_of_squarefree S.prodPrimes_squarefree]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s S.prodPrimes.primeFactors id hsub
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  rw [upperRosserWeight_prod_eq_setWeight S.prodPrimes_squarefree hsub,
    ← S.prod_primeFactors_nu hdiv, hpf]

theorem abs_upperRosserWeight_le_one (P D d : ℕ) :
    |upperRosserWeight P D d| ≤ 1 := by
  unfold upperRosserWeight
  split
  · split <;> norm_num
  · norm_num

theorem abs_upperRosserWeight_le_threePow (P D d : ℕ) :
    |upperRosserWeight P D d| ≤ (3 : ℝ) ^ d.primeFactors.card :=
  (abs_upperRosserWeight_le_one P D d).trans (one_le_pow₀ (by norm_num))

theorem upperRosserWeight_dvd {P D d : ℕ}
    (h : upperRosserWeight P D d ≠ 0) : d ∣ P := by
  unfold upperRosserWeight at h
  split at h
  · exact (Nat.mem_divisors.mp
      ‹d ∈ P.divisors ∧ d < D ∧ UpperRosserAdmissible D d›.1).1
  · simp at h

theorem upperRosserWeight_lt_level {P D d : ℕ}
    (h : upperRosserWeight P D d ≠ 0) : d < D := by
  unfold upperRosserWeight at h
  split at h
  · exact ‹d ∈ P.divisors ∧ d < D ∧ UpperRosserAdmissible D d›.2.1
  · simp at h

theorem upperRosserWeight_hasUpperLevelSupport (P D : ℕ) :
    HasUpperLevelSupport P D (upperRosserWeight P D) := by
  intro d hd hD
  unfold upperRosserWeight
  simp [hD]

/-- The finite upper Rosser certificate is precisely the upper-Möbius condition
on divisors of the chosen squarefree prime product. -/
def IsUpperRosserCertificate (P D : ℕ) : Prop :=
  IsUpperMoebiusOn P (upperRosserWeight P D)

/-- The explicit upper Rosser weight is a finite upper-Möbius certificate.  The
condition `1 < D` is necessary for any strictly level-supported upper
coefficient, since its coefficient at `1` must be at least one. -/
theorem upperRosserWeight_certificate {P D : ℕ} (hP : Squarefree P)
    (hP0 : P ≠ 0) (hD1 : 1 < D) (hD : ∀ p ∈ P.primeFactors, p < D) :
    IsUpperRosserCertificate P D := by
  intro n hn
  have hnSquarefree : Squarefree n := Squarefree.squarefree_of_dvd hn hP
  rw [Internal.sum_divisors_eq_sum_primeFactors_powerset hnSquarefree]
  by_cases hn1 : n = 1
  · subst n
    simp [upperRosserWeight, UpperRosserAdmissible,
      UpperRosserAdmissibleSet, hP0, hD1]
  · rw [if_neg hn1]
    have hnFactors : n.primeFactors.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rcases Nat.primeFactors_eq_empty.mp hempty with hn0 | hn_one
      · exact hnSquarefree.ne_zero hn0
      · exact hn1 hn_one
    have hsub : n.primeFactors ⊆ P.primeFactors :=
      Nat.primeFactors_mono hn hP0
    calc
      0 ≤ ∑ s ∈ n.primeFactors.powerset, upperRosserSetWeight D s :=
        sum_upperRosserSetWeight_nonneg hnFactors
          (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
          (fun p hp ↦ hD p (hsub hp))
      _ = ∑ s ∈ n.primeFactors.powerset,
          upperRosserWeight P D (s.prod id) := by
        apply Finset.sum_congr rfl
        intro s hs
        symm
        exact upperRosserWeight_prod_eq_setWeight hP
          ((Finset.mem_powerset.mp hs).trans hsub)

theorem upperRosserWeight_divisor_sum {P D n : ℕ}
    (hcert : IsUpperRosserCertificate P D) (hn : n ∣ P) :
    (if n = 1 then 1 else 0) ≤
      ∑ d ∈ n.divisors, upperRosserWeight P D d :=
  hcert n hn

/-- The explicit upper Rosser coefficient gives the finite upper-sieve
inequality with the exact level-restricted remainder sum. -/
theorem siftedSum_le_mainSum_add_upperErrSum_upperRosser
    {S : BoundingSieve} (D : ℕ)
    (hcert : IsUpperRosserCertificate S.prodPrimes D) :
    S.siftedSum ≤
      S.totalMass * S.mainSum (upperRosserWeight S.prodPrimes D) +
        upperErrSum S D (upperRosserWeight S.prodPrimes D) :=
  siftedSum_le_mainSum_add_upperErrSum_of_upperMoebiusOn D
    (upperRosserWeight S.prodPrimes D) hcert
    (upperRosserWeight_hasUpperLevelSupport S.prodPrimes D)


end MathlibNt.SieveTheory.LinearSieve
