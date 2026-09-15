import Wu18938Campaign.M2.TerminalDebits
import Mathlib.Data.List.Sort

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

private theorem upper_spec {N d ell : ℕ} {l : List ℕ}
    (hlen : 2 ≤ l.length) (hell : ell ∈ terminalUpper N d l) :
    ∃ (pre : List ℕ) (q : ℕ), l = pre ++ [q] ∧
      ell ∈ sourceSieveCarrier N (d * l.prod) (d * pre.prod * N) q := by
  obtain ⟨pre, p, q, rfl⟩ := HighNonunit.split_last_two hlen
  refine ⟨pre ++ [p], q, by simp, ?_⟩
  simpa [terminalUpper, terminalMask, List.prod_append, mul_assoc] using hell

private theorem selected_small_mem {N d n q r : ℕ} {pre : List ℕ}
    (hpre : ∀ t ∈ pre, t.Prime) (hr : r.Prime)
    (hrd : r.Coprime d) (hrN : r.Coprime N) (hrn : r ∣ n) (hrq : r < q)
    (hs : Sifted (d * pre.prod * N) n q) : r ∈ pre := by
  by_contra hnot
  have hcop := secondFunctionalMother_coprime_prod r pre
    (fun t ht => (Nat.coprime_primes hr (hpre t ht)).mpr
      (by intro he; exact hnot (he.symm ▸ ht)))
  exact hs r hr ((hrd.mul_right hcop).mul_right hrN) (by exact_mod_cast hrq) hrn

private theorem ordered_eq_of_subset {l k : List ℕ}
    (hl : l.Pairwise (· < ·)) (hk : k.Pairwise (· < ·))
    (hlen : l.length = k.length) (hsub : l.toFinset ⊆ k.toFinset) : l = k := by
  have he : l.toFinset = k.toFinset := eq_of_subset_of_card_le hsub
    (by simpa [List.toFinset_card_of_nodup hl.nodup,
      List.toFinset_card_of_nodup hk.nodup] using hlen.symm.le)
  exact hl.eq_of_mem_iff hk (fun p => by
    simpa only [List.mem_toFinset] using
      (show p ∈ l.toFinset ↔ p ∈ k.toFinset from by rw [he]))

private theorem upper_subset {N d ell q q' : ℕ} {pre pre' : List ℕ}
    (hord : (pre ++ [q]).Pairwise (· < ·))
    (hprime : ∀ p ∈ pre ++ [q], p.Prime ∧ p.Coprime d ∧ p.Coprime N)
    (hprime' : ∀ p ∈ pre', p.Prime)
    (hdiv : d * (pre ++ [q]).prod ∣ N - ell)
    (hs : Sifted (d * pre'.prod * N) (N - ell) q') (hqq : q ≤ q') :
    (pre ++ [q]).toFinset ⊆ (pre' ++ [q']).toFinset := by
  intro p hp
  have hpmem := List.mem_toFinset.mp hp
  have hpq : p ≤ q := by
    rcases List.mem_append.mp hpmem with h | h
    · exact ((List.pairwise_append.mp hord).2.2 p h q (by simp)).le
    · have := List.mem_singleton.mp h
      omega
  have hpdiv : p ∣ N - ell :=
    (List.dvd_prod hpmem).trans ((dvd_mul_left (pre ++ [q]).prod d).trans hdiv)
  rcases lt_or_eq_of_le (hpq.trans hqq) with hlt | rfl
  · exact List.mem_toFinset.mpr (List.mem_append_left _
      (selected_small_mem hprime' (hprime p hpmem).1
        (hprime p hpmem).2.1 (hprime p hpmem).2.2 hpdiv hlt hs))
  · simp

theorem terminal_upper_unique {N d ell : ℕ} {l k : List ℕ}
    (hlen : 2 ≤ l.length) (hsize : l.length = k.length)
    (hl : l.Pairwise (· < ·)) (hk : k.Pairwise (· < ·))
    (hpl : ∀ p ∈ l, p.Prime ∧ p.Coprime d ∧ p.Coprime N)
    (hpk : ∀ p ∈ k, p.Prime ∧ p.Coprime d ∧ p.Coprime N)
    (hell : ell ∈ terminalUpper N d l) (helk : ell ∈ terminalUpper N d k) : l = k := by
  obtain ⟨pre, q, rfl, hleft⟩ := upper_spec hlen hell
  obtain ⟨pre', q', rfl, hright⟩ := upper_spec (l := k) (by omega) helk
  obtain ⟨_, _, hdiv, _⟩ := mem_filter.mp hleft
  obtain ⟨_, _, hdiv', hs'⟩ := mem_filter.mp hright
  rcases le_total q q' with h | h
  · exact ordered_eq_of_subset hl hk hsize
      (upper_subset hl hpl (fun p hp => (hpk p (List.mem_append_left _ hp)).1) hdiv hs' h)
  · have hs := (mem_filter.mp hleft).2.2.2
    exact (ordered_eq_of_subset hk hl hsize.symm
      (upper_subset hk hpk (fun p hp => (hpl p (List.mem_append_left _ hp)).1)
        hdiv' hs h)).symm

private theorem upper_to_first {N d ell p : ℕ} {tail : List ℕ}
    (hlen : 2 ≤ (p :: tail).length) (hord : (p :: tail).Pairwise (· < ·))
    (hprime : ∀ q ∈ p :: tail, q.Prime)
    (hell : ell ∈ terminalUpper N d (p :: tail)) :
    ell ∈ sourceSieveCarrier N (d * p) (d * N) p := by
  obtain ⟨pre, q, he, hsource⟩ := upper_spec hlen hell
  obtain ⟨hbound, hellprime, hdiv, hs⟩ := mem_filter.mp hsource
  have hmin : ∀ t ∈ p :: tail, p ≤ t := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hord).1 t ht).le
  have hpq : p ≤ q := hmin q (by rw [he]; simp)
  refine mem_filter.mpr ⟨hbound, hellprime,
    (Nat.mul_dvd_mul_left d (List.dvd_prod (by simp : p ∈ p :: tail))).trans hdiv, ?_⟩
  intro r hr hrM hrp
  have hrp' : r < p := by exact_mod_cast hrp
  have hrpre := secondFunctionalMother_coprime_prod r pre (fun t ht =>
    (Nat.coprime_primes hr (hprime t (by rw [he]; exact List.mem_append_left _ ht))).mpr
      (ne_of_lt (hrp'.trans_le (hmin t (by rw [he]; exact List.mem_append_left _ ht)))))
  have hrfull : r.Coprime (d * pre.prod * N) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hrM.mul_right hrpre
  exact hs r hr hrfull (by exact_mod_cast hrp'.trans_le hpq)

noncomputable def originalE3 (N d : ℕ) (e f : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N e f, (sourceSieveCount N (d * p) (d * N) p : ℝ)

theorem terminal_upper_family_le_E3 {N d r : ℕ} {e f : ℝ} (L : Finset (List ℕ))
    (hr : 2 ≤ r)
    (hL : L ⊆ secondFunctionalMotherTuples (primeWindow N e f) r)
    (hcop : ∀ p ∈ primeWindow N e f, p.Coprime d) :
    (∑ l ∈ L, ((terminalUpper N d l).card : ℝ)) ≤ originalE3 N d e f := by
  let X := L.sigma (terminalUpper N d)
  let Y := (primeWindow N e f).sigma
    (fun p => sourceSieveCarrier N (d * p) (d * N) p)
  let F : (Σ _ : List ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.1.headD 0, x.2⟩
  have hmap : ∀ x ∈ X, F x ∈ Y := by
    rintro ⟨l, ell⟩ hx
    obtain ⟨hl, hell⟩ := mem_sigma.mp hx
    obtain ⟨hlen, hord, hprime⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp (hL hl)
    cases l with
    | nil => simp at hlen; omega
    | cons p tail =>
      exact mem_sigma.mpr ⟨hprime p (by simp),
        upper_to_first (by simp only [List.length_cons] at hlen ⊢; omega) hord
          (fun q hq => (mem_primeWindow.mp (hprime q hq)).1) hell⟩
  have hinj : Set.InjOn F X := by
    rintro ⟨l, ell⟩ hx ⟨k, ell'⟩ hy he
    have heell : ell = ell' := congrArg Sigma.snd he
    subst ell'
    obtain ⟨hl, hell⟩ := mem_sigma.mp hx
    obtain ⟨hk, helk⟩ := mem_sigma.mp hy
    obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp (hL hl)
    obtain ⟨ksize, kord, kmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp (hL hk)
    have heq := terminal_upper_unique (by omega) (hlen.trans ksize.symm) hord kord
      (fun p hp => ⟨(mem_primeWindow.mp (hmem p hp)).1, hcop p (hmem p hp),
        (mem_primeWindow.mp (hmem p hp)).2.1⟩)
      (fun p hp => ⟨(mem_primeWindow.mp (kmem p hp)).1, hcop p (kmem p hp),
        (mem_primeWindow.mp (kmem p hp)).2.1⟩) hell helk
    change l = k at heq
    subst k
    rfl
  have hcard := card_le_card_of_injOn F hmap hinj
  have hreal : (X.card : ℝ) ≤ Y.card := by exact_mod_cast hcard
  simpa only [X, Y, card_sigma, Nat.cast_sum, originalE3, sourceSieveCount,
    Int.cast_natCast] using hreal

theorem terminal_upper_all_three_le_E3 {N d : ℕ} {a b c e f : ℝ}
    (n : ℕ) (hcop : ∀ p ∈ primeWindow N e f, p.Coprime d) :
    terminalUpperWord N d a b c e f (List.replicate n 3) ≤ originalE3 N d e f := by
  apply terminal_upper_family_le_E3 _ (by omega : 2 ≤ n + 2) _ hcop
  intro l hl
  obtain ⟨hl, hcolour⟩ := mem_filter.mp hl
  obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  apply (secondFunctionalMother_tuple_mem _ _ _).mpr
  refine ⟨by simpa using hlen, hord, ?_⟩
  intro p hp
  obtain ⟨hprime, hpN, _, hpf⟩ := mem_primeWindow.mp (hmem p hp)
  have hc : secondFunctionalMotherColour b c e p = 3 := by
    have hm := List.mem_map_of_mem (f := secondFunctionalMotherColour b c e) hp
    rw [hcolour] at hm
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil] at hm
    tauto
  have hep : e ≤ (p : ℝ) := by
    unfold secondFunctionalMotherColour at hc
    split_ifs at hc <;> first | omega | linarith
  exact mem_primeWindow.mpr ⟨hprime, hpN, hep, hpf⟩

theorem gamma21_original_E3_payment {N d : ℕ} {a b c e f : ℝ}
    (hae : a ≤ e) (hcop : ∀ p ∈ primeWindow N a f, p.Coprime d) :
    secondFunctionalMotherPrefixTerm N d N a b c e f [3, 3, 3, 3] -
        2 * originalE3 N d e f ≤ secondFunctionalMotherGamma N d N a b c e f 21 := by
  have hcop' : ∀ p ∈ primeWindow N e f, p.Coprime d := by
    intro p hp
    obtain ⟨hp, hpN, hpe, hpf⟩ := mem_primeWindow.mp hp
    exact hcop p (mem_primeWindow.mpr ⟨hp, hpN, hae.trans hpe, hpf⟩)
  have h4 := terminal_upper_all_three_le_E3 (a := a) (b := b) (c := c) 2 hcop'
  have h5 := terminal_upper_all_three_le_E3 (a := a) (b := b) (c := c) 3 hcop'
  norm_num only [List.replicate_succ, List.replicate_zero] at h4 h5
  have he := gamma21_two_debits (b := b) (c := c) (e := e) hcop
  linarith

end Wu18938Campaign.M2
