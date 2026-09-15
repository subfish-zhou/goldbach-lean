import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherCarriers
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherPairMass

/-! # Arbitrary-length prefix labels inject into the literal source carrier -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_prefix_all {s : Finset ℕ} {l : List ℕ}
    (hl : l ∈ fourthRowMotherPrefixes s l.length) :
    l.Pairwise (· < ·) ∧ ∀ p ∈ l, p ∈ s := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp
  | singleton p =>
      have hp : p ∈ s := by simpa [fourthRowMotherPrefixes] using hl
      simp [hp]
  | cons_cons p q l _ ih =>
      have hl' : p::q::l ∈ fourthRowMotherPrefixes s (l.length+2) := by simpa using hl
      obtain ⟨hp, hm, ht⟩ := fourthRowMother_mem_cons.mp hl'
      have ht' : q::l ∈ fourthRowMotherPrefixes (s.erase p) (q::l).length := ht
      obtain ⟨hord, hall⟩ := ih q ht'
      refine ⟨List.pairwise_cons.mpr ⟨?_, hord⟩, ?_⟩
      · intro t ht
        obtain ⟨hne, hs⟩ := mem_erase.mp (hall t ht)
        exact lt_of_le_of_ne (hm t hs) hne.symm
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hp
        · exact (mem_erase.mp (hall t ht)).2

theorem secondFunctionalMother_prefix_lower {s : Finset ℕ} {l : List ℕ}
    (hl : l ∈ fourthRowMotherPrefixes s l.length) (hlen : 2 ≤ l.length) :
    ∀ q ∈ s, q < l.getD (l.length-2) 0 → q ∈ l.take (l.length-2) := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp at hlen
  | singleton p => simp at hlen
  | cons_cons p q l _ ih =>
      have hl' : p::q::l ∈ fourthRowMotherPrefixes s (l.length+2) := by simpa using hl
      obtain ⟨hp, hm, ht⟩ := fourthRowMother_mem_cons.mp hl'
      cases l with
      | nil =>
          intro t ht hlt
          simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
            Nat.sub_self, List.getD_cons_zero] at hlt
          exact False.elim (not_lt_of_ge (hm t ht) hlt)
      | cons r l =>
          intro t hts hlt
          by_cases he : t = p
          · subst t
            simp
          · have hh := ih q ht (by simp) t (mem_erase.mpr ⟨he, hts⟩)
            have hlt' : t < (q::r::l).getD ((q::r::l).length-2) 0 := by
              simpa [List.length_cons, Nat.add_sub_cancel, List.getD] using hlt
            have hh' := hh hlt'
            simpa [List.length_cons, Nat.add_sub_cancel, List.take] using
              (List.mem_cons_of_mem p hh')

theorem secondFunctionalMother_prefix_in_tuples {P : Finset ℕ} {n r : ℕ} {l : List ℕ}
    (hl : l ∈ fourthRowMotherPrefixes (divisorsIn P n) r) :
    l ∈ secondFunctionalMotherTuples P r := by
  have hlen := fourthRowMother_prefix_length hl
  have hh := secondFunctionalMother_prefix_all (hlen ▸ hl)
  exact (secondFunctionalMother_tuple_mem P r l).mpr
    ⟨hlen, hh.1, fun p hp => (mem_filter.mp (hh.2 p hp)).1⟩

theorem secondFunctionalMother_coprime_prod (p : ℕ) (l : List ℕ)
    (h : ∀ q ∈ l, p.Coprime q) : p.Coprime l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
      exact (h q (by simp)).mul_right (ih (fun t ht => h t (by simp [ht])))

theorem secondFunctionalMother_prod_dvd (l : List ℕ) (n : ℕ)
    (hord : l.Pairwise (· < ·)) (hp : ∀ p ∈ l, p.Prime)
    (hd : ∀ p ∈ l, p ∣ n) : l.prod ∣ n := by
  induction l with
  | nil => simp
  | cons p l ih =>
      obtain ⟨hmin, hord⟩ := List.pairwise_cons.mp hord
      have hp' := hp p (by simp)
      have hcop : p.Coprime l.prod := secondFunctionalMother_coprime_prod p l
        (fun q hq => (Nat.coprime_primes hp' (hp q (by simp [hq]))).mpr
          (ne_of_lt (hmin q hq)))
      exact hcop.mul_dvd_of_dvd_of_dvd (hd p (by simp))
        (ih hord (fun q hq => hp q (by simp [hq])) (fun q hq => hd q (by simp [hq])))

theorem secondFunctionalMother_prefix_source_subset (N d : ℕ) {a f : ℝ}
    {l : List ℕ} (hlen : 2 ≤ l.length) :
    (sieveCarrier N d (d*N) a).filter
      (fun ell => l ∈ fourthRowMotherPrefixes
        (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d)) l.length) ⊆
      secondFunctionalMotherPrefixCarrier N d l := by
  intro ell hell
  obtain ⟨hbase, hl⟩ := mem_filter.mp hell
  obtain ⟨hrange, hprime, hd, hs⟩ := mem_filter.mp hbase
  have hh := secondFunctionalMother_prefix_all hl
  have hmem (p : ℕ) (hp : p ∈ l) := mem_filter.mp (hh.2 p hp)
  have hprod : l.prod ∣ (N-ell)/d := secondFunctionalMother_prod_dvd l _ hh.1
    (fun p hp => (mem_primeWindow.mp (hmem p hp).1).1) (fun p hp => (hmem p hp).2)
  have hcutmem : l.getD (l.length-2) 0 ∈ l := by
    have hi : l.length-2 < l.length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hcut := mem_primeWindow.mp (hmem _ hcutmem).1
  change ell ∈ sourceSieveCarrier N (d*l.prod) (d*(l.take (l.length-2)).prod*N)
    (l.getD (l.length-2) 0)
  apply mem_filter.mpr
  refine ⟨hrange, hprime, (Nat.dvd_div_iff_mul_dvd hd).mp hprod, ?_⟩
  apply (sifted_quotient_iff hd (fun q _ hq _ =>
    hq.of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right d _) N))).mp
  intro q hq hqM hqlt hqn
  have hqbase : q.Coprime (d*N) := hqM.of_dvd_right
    (by exact ⟨(l.take (l.length-2)).prod, by ring⟩)
  by_cases hqa : (q : ℝ) < a
  · exact hs q hq hqbase hqa hqn
  · have hqw : q ∈ primeWindow (d*N) a f := mem_primeWindow.mpr
      ⟨hq, hqbase, le_of_not_gt hqa, hqlt.trans hcut.2.2.2⟩
    have hqp := secondFunctionalMother_prefix_lower hl hlen q
      (mem_filter.mpr ⟨hqw, hqn⟩) (by exact_mod_cast hqlt)
    have hqd : q ∣ (l.take (l.length-2)).prod := List.dvd_prod hqp
    have hself : q.Coprime q := hqM.of_dvd_right
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqd d) N)
    exact hq.ne_one (by simpa [Nat.Coprime] using hself)

end Wu2008DoubleSieve
