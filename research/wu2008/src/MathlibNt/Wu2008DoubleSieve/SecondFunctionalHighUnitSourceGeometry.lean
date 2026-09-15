import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceCore

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open Finset SecondFunctionalUnitPrimeFibre

/-- Structural list reconstruction, not enumeration of prime values. -/
theorem length_five {l : List ℕ} (h : l.length = 5) :
    ∃ p q r s t, l = [p,q,r,s,t] := by
  cases l with
  | nil => simp at h
  | cons p l =>
    have hl : l.length = 4 := by simpa using h
    obtain ⟨q,r,s,t,rfl⟩ := List.length_eq_four.mp hl
    exact ⟨p,q,r,s,t,rfl⟩

theorem length_six {l : List ℕ} (h : l.length = 6) :
    ∃ p q r s t u, l = [p,q,r,s,t,u] := by
  cases l with
  | nil => simp at h
  | cons p l =>
    have hl : l.length = 5 := by simpa using h
    obtain ⟨q,r,s,t,u,rfl⟩ := length_five hl
    exact ⟨p,q,r,s,t,u,rfl⟩

/-- Actual original-window unit atoms map to the accepted labelled closed physical envelope. -/
theorem geometry20 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a2) (hb : b ≤ 1/2)
    (x : Σ _ : List ℕ, ℕ)
    (hx : x ∈ atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word20) :
    ∃ y ∈ (HighUnit.primePrefix20 R a2 a3 b).sigma
        (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R^b)),
      fullList y = x.1 := by
  rcases x with ⟨l,ell⟩
  obtain ⟨hl,hell⟩ := mem_sigma.mp hx
  obtain ⟨htup,hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
  change l.length = 5 at hlen
  obtain ⟨p0,p1,p2,p3,p4,rfl⟩ := length_five hlen
  have hc : secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p0 = 2 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p1 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p2 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p3 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p4 = 3 := by
    simpa [word20] using hcol
  have ho : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 := by
    simp [List.pairwise_cons] at hord
    exact ⟨hord.1.1,hord.2.1.1,hord.2.2.1.1,hord.2.2.2⟩
  have hlo : R^a2 ≤ (p0 : ℝ) := (colour_two hc.1).1
  have hw0 := hm p0 (by simp)
  have hs0 : p0 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw0
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p0 by omega)
  let z0 : primeSlabPrimes R := ⟨p0,hs0⟩
  have hw1 := hm p1 (by simp)
  have hs1 : p1 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw1
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p1 by omega)
  let z1 : primeSlabPrimes R := ⟨p1,hs1⟩
  have hw2 := hm p2 (by simp)
  have hs2 : p2 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw2
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p2 by omega)
  let z2 : primeSlabPrimes R := ⟨p2,hs2⟩
  have hw3 := hm p3 (by simp)
  have hs3 : p3 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw3
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p3 by omega)
  let z3 : primeSlabPrimes R := ⟨p3,hs3⟩
  let g : Fin 4 → primeSlabPrimes R := ![z0,z1,z2,z3]
  have hg : g ∈ HighUnit.primePrefix20 R a2 a3 b := by
    simp only [HighUnit.primePrefix20, mem_filter, mem_univ, true_and]
    change R^a2 ≤ (p0 : ℝ) ∧ (p0 : ℝ) < R^a3 ∧ R^a3 ≤ (p1 : ℝ) ∧ p1 < p2 ∧ p2 < p3 ∧ (p3 : ℝ) < R^b
    exact ⟨hlo,(colour_two hc.1).2,colour_three hc.2.1,ho.2.1,ho.2.2.1,
      (mem_primeWindow.mp hw3).2.2.2⟩
  have hfull : fullList ⟨g,p4⟩ = [p0,p1,p2,p3,p4] := by
    simp [fullList, g, List.ofFn_succ, z0, z1, z2, z3]
  have hwlast := mem_primeWindow.mp (hm p4 (by simp))
  refine ⟨⟨g,p4⟩, mem_sigma.mpr ⟨hg, ?_⟩, hfull⟩
  apply physical_of_unit hd (Real.rpow_nonneg (by linarith) _) g (Fin.last 3)
    hwlast.1 (show p3 < p4 from ho.2.2.2) hwlast.2.2.2.le
  simpa only [hfull] using hell

theorem prefix_le20 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    FourPrimeUnit.prefixTerm true N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word20 ≤
      ∑ g ∈ HighUnit.primePrefix20 R a2 a3 b,
        ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R^b)).card : ℝ) :=
  count_of_geometry _ _ (geometry20 hd hR hlow hb)

/-- Actual original-window unit atoms map to the accepted labelled closed physical envelope. -/
theorem geometry21 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a3) (hb : b ≤ 1/2)
    (x : Σ _ : List ℕ, ℕ)
    (hx : x ∈ atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word21) :
    ∃ y ∈ (HighUnit.primePrefix21 R a3 b).sigma
        (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R^b)),
      fullList y = x.1 := by
  rcases x with ⟨l,ell⟩
  obtain ⟨hl,hell⟩ := mem_sigma.mp hx
  obtain ⟨htup,hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen,hord,hm⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp htup
  change l.length = 6 at hlen
  obtain ⟨p0,p1,p2,p3,p4,p5,rfl⟩ := length_six hlen
  have hc : secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p0 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p1 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p2 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p3 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p4 = 3 ∧ secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) p5 = 3 := by
    simpa [word21] using hcol
  have ho : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ p4 < p5 := by
    simp [List.pairwise_cons] at hord
    exact ⟨hord.1.1,hord.2.1.1,hord.2.2.1.1,hord.2.2.2.1.1,hord.2.2.2.2⟩
  have hlo : R^a3 ≤ (p0 : ℝ) := colour_three hc.1
  have hw0 := hm p0 (by simp)
  have hs0 : p0 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw0
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p0 by omega)
  let z0 : primeSlabPrimes R := ⟨p0,hs0⟩
  have hw1 := hm p1 (by simp)
  have hs1 : p1 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw1
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p1 by omega)
  let z1 : primeSlabPrimes R := ⟨p1,hs1⟩
  have hw2 := hm p2 (by simp)
  have hs2 : p2 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw2
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p2 by omega)
  let z2 : primeSlabPrimes R := ⟨p2,hs2⟩
  have hw3 := hm p3 (by simp)
  have hs3 : p3 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw3
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p3 by omega)
  let z3 : primeSlabPrimes R := ⟨p3,hs3⟩
  have hw4 := hm p4 (by simp)
  have hs4 : p4 ∈ primeSlabPrimes R := by
    apply slab_of_window hR hlow hb hw4
    apply hlo.trans
    exact_mod_cast (show p0 ≤ p4 by omega)
  let z4 : primeSlabPrimes R := ⟨p4,hs4⟩
  let g : Fin 5 → primeSlabPrimes R := ![z0,z1,z2,z3,z4]
  have hg : g ∈ HighUnit.primePrefix21 R a3 b := by
    simp only [HighUnit.primePrefix21, mem_filter, mem_univ, true_and]
    change R^a3 ≤ (p0 : ℝ) ∧ p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ (p4 : ℝ) < R^b
    exact ⟨hlo,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,
      (mem_primeWindow.mp hw4).2.2.2⟩
  have hfull : fullList ⟨g,p5⟩ = [p0,p1,p2,p3,p4,p5] := by
    simp [fullList, g, List.ofFn_succ, z0, z1, z2, z3, z4]
  have hwlast := mem_primeWindow.mp (hm p5 (by simp))
  refine ⟨⟨g,p5⟩, mem_sigma.mpr ⟨hg, ?_⟩, hfull⟩
  apply physical_of_unit hd (Real.rpow_nonneg (by linarith) _) g (Fin.last 4)
    hwlast.1 (show p4 < p5 from ho.2.2.2.2) hwlast.2.2.2.le
  simpa only [hfull] using hell

theorem prefix_le21 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    FourPrimeUnit.prefixTerm true N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word21 ≤
      ∑ g ∈ HighUnit.primePrefix21 R a3 b,
        ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R^b)).card : ℝ) :=
  count_of_geometry _ _ (geometry21 hd hR hlow hb)

/-- Concrete full-label injection, with no geometry or source inequality supplied by the caller. -/
theorem injection20 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    ∃ E : (atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word20) ↪
        ((HighUnit.primePrefix20 R a2 a3 b).sigma (fun g =>
          physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R^b))),
      ∀ x, fullList (E x).val = x.val.1 :=
  injection_of_geometry _ _ (geometry20 hd hR hlow hb)

/-- Concrete full-label injection, with no geometry or source inequality supplied by the caller. -/
theorem injection21 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    ∃ E : (atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word21) ↪
        ((HighUnit.primePrefix21 R a3 b).sigma (fun g =>
          physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R^b))),
      ∀ x, fullList (E x).val = x.val.1 :=
  injection_of_geometry _ _ (geometry21 hd hR hlow hb)

end Wu2008DoubleSieve.HighUnitSource
