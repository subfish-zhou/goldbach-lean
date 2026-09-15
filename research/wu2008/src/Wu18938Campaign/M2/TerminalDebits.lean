import Wu18938Campaign.M2.SourceBuchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitCore
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPrefixBridge

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def terminalMask (N d : ℕ) (l : List ℕ) : ℕ :=
  d * (l.take (l.length - 2)).prod * l.getD (l.length - 2) 0 * N

noncomputable def terminalWindow (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  primeWindow (terminalMask N d l) (l.getD (l.length - 2) 0)
    (l.getD (l.length - 1) 0)

noncomputable def terminalUpper (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  sourceSieveCarrier N (d * l.prod) (terminalMask N d l) (l.getD (l.length - 1) 0)

def insertTerminal (x : Σ _ : List ℕ, ℕ) : List ℕ :=
  x.1.take (x.1.length - 2) ++
    [x.1.getD (x.1.length - 2) 0, x.2, x.1.getD (x.1.length - 1) 0]

theorem insertTerminal_append (pre : List ℕ) (p q r : ℕ) :
    insertTerminal ⟨pre ++ [p, q], r⟩ = pre ++ [p, r, q] := by
  simp [insertTerminal]

theorem terminal_difference {N d : ℕ} {l : List ℕ}
    (hlen : 2 ≤ l.length) (hord : l.Pairwise (· < ·))
    (hprime : ∀ p ∈ l, p.Prime) :
    ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) -
        ((terminalUpper N d l).card : ℝ) =
      ∑ r ∈ terminalWindow N d l,
        ((secondFunctionalMotherPrefixCarrier N d (insertTerminal ⟨l, r⟩)).card : ℝ) := by
  obtain ⟨pre, p, q, rfl⟩ := HighNonunit.split_last_two hlen
  have hpq : p < q := by simpa using (List.pairwise_append.mp hord).2.1
  have h := penultimate_buchstab N (d * pre.prod) p q
    (hprime p (by simp)) (hprime q (by simp)) hpq.le
  have hreal := congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [terminalUpper, terminalWindow, terminalMask, insertTerminal_append,
    HighNonunit.prefix_carrier, fourthRowMotherPrefixCarrier,
    sourceSieveCount, List.prod_append, mul_assoc] using hreal

noncomputable def terminalBase (N : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset (List ℕ) :=
  (secondFunctionalMotherTuples (primeWindow N a f) (cs.length + 2)).filter
    (fun l => l.map (secondFunctionalMotherColour b c e) = cs ++ [3, 3])

noncomputable def terminalDebit (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ terminalBase N a b c e f cs,
    (((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) -
      ((terminalUpper N d l).card : ℝ))

private theorem terminal_insert_mem {N d : ℕ} {a b c e f : ℝ} {cs l : List ℕ} {r : ℕ}
    (hl : l ∈ terminalBase N a b c e f cs) (hr : r ∈ terminalWindow N d l) :
    insertTerminal ⟨l, r⟩ ∈
      (secondFunctionalMotherTuples (primeWindow N a f) (cs.length + 3)).filter
        (fun l => l.map (secondFunctionalMotherColour b c e) = cs ++ [3, 3, 3]) := by
  obtain ⟨hl, hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  obtain ⟨pre, p, q, rfl⟩ := HighNonunit.split_last_two (l := l) (by omega)
  have hprelen : pre.length = cs.length := by simpa using hlen
  have hpm := mem_primeWindow.mp (hmem p (by simp))
  have hqm := mem_primeWindow.mp (hmem q (by simp))
  have hpq : p < q := by simpa using (List.pairwise_append.mp hord).2.1
  have hr' : r ∈ primeWindow (d * pre.prod * p * N) p q := by
    simpa [terminalWindow, terminalMask] using hr
  have hpr := penultimate_selected_label_absent hpm.1 hr'
  obtain ⟨hrp, hrM, _, hrq⟩ := mem_primeWindow.mp hr'
  have hrq' : r < q := by exact_mod_cast hrq
  simp only [List.map_append, List.map_cons, List.map_nil] at hcol
  have hparts := List.append_inj hcol (by simpa using hprelen)
  have hprecol : pre.map (secondFunctionalMotherColour b c e) = cs := hparts.1
  have htailcol : secondFunctionalMotherColour b c e p = 3 ∧
      secondFunctionalMotherColour b c e q = 3 := by
    simpa using hparts.2
  have hrcol : secondFunctionalMotherColour b c e r = 3 := by
    apply le_antisymm (secondFunctionalMother_colour_le_three b c e r)
    rw [← htailcol.1]
    exact secondFunctionalMother_colour_monotone b c e hpr.le
  have hord' : (pre ++ [p, r, q]).Pairwise (· < ·) := by
    obtain ⟨hpre, _, hcross⟩ := List.pairwise_append.mp hord
    apply List.pairwise_append.mpr
    refine ⟨hpre, by simp; omega, ?_⟩
    intro t ht u hu
    have htp := hcross t ht p (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> omega
  rw [insertTerminal_append]
  apply mem_filter.mpr
  refine ⟨(secondFunctionalMother_tuple_mem _ _ _).mpr
    ⟨by simp [hprelen], hord', ?_⟩, ?_⟩
  · intro t ht
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | rfl | rfl | rfl
    · exact hmem t (List.mem_append_left _ ht)
    · exact mem_primeWindow.mpr hpm
    · exact mem_primeWindow.mpr ⟨hrp,
        hrM.of_dvd_right (dvd_mul_left N (d * pre.prod * p)),
        hpm.2.2.1.trans (by exact_mod_cast hpr.le), hrq.trans hqm.2.2.2⟩
    · exact mem_primeWindow.mpr hqm
  · simp [List.map_append, hprecol, htailcol.1, htailcol.2, hrcol]

private theorem terminal_insert_injective {N d : ℕ} {a b c e f : ℝ} {cs : List ℕ} :
    Set.InjOn insertTerminal
      ((terminalBase N a b c e f cs).sigma (terminalWindow N d)) := by
  rintro ⟨l, r⟩ hx ⟨l', r'⟩ hy he
  have hxlen := ((secondFunctionalMother_tuple_mem _ _ _).mp
    (mem_filter.mp (mem_sigma.mp hx).1).1).1
  have hylen := ((secondFunctionalMother_tuple_mem _ _ _).mp
    (mem_filter.mp (mem_sigma.mp hy).1).1).1
  change l.length = cs.length + 2 at hxlen
  change l'.length = cs.length + 2 at hylen
  obtain ⟨pre, p, q, rfl⟩ := HighNonunit.split_last_two (by omega : 2 ≤ l.length)
  obtain ⟨pre', p', q', rfl⟩ := HighNonunit.split_last_two (by omega : 2 ≤ l'.length)
  have hxpre : pre.length = cs.length := by simpa using hxlen
  have hypre : pre'.length = cs.length := by simpa using hylen
  rw [insertTerminal_append, insertTerminal_append] at he
  have hparts := List.append_inj he (hxpre.trans hypre.symm)
  have hpre : pre = pre' := hparts.1
  have htail : p = p' ∧ r = r' ∧ q = q' := by
    simpa using hparts.2
  rcases htail with ⟨rfl, rfl, rfl⟩
  subst pre'
  rfl

theorem terminal_debit_le_word (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    terminalDebit N d a b c e f cs ≤
      secondFunctionalMotherPrefixTerm N d N a b c e f (cs ++ [3, 3, 3]) := by
  let X := (terminalBase N a b c e f cs).sigma (terminalWindow N d)
  let F := fun l => ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ)
  have hexact : terminalDebit N d a b c e f cs = ∑ x ∈ X, F (insertTerminal x) := by
    unfold terminalDebit
    rw [show (∑ x ∈ X, F (insertTerminal x)) =
      ∑ l ∈ terminalBase N a b c e f cs,
        ∑ r ∈ terminalWindow N d l, F (insertTerminal ⟨l, r⟩) from
          sum_sigma _ _ (fun x => F (insertTerminal x))]
    apply sum_congr rfl
    intro l hl
    obtain ⟨hlen, hord, hprime⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp
      (mem_filter.mp hl).1
    exact terminal_difference (by omega) hord (fun p hp => (mem_primeWindow.mp (hprime p hp)).1)
  rw [hexact, ← sum_image terminal_insert_injective]
  have hsub : X.image insertTerminal ⊆
      (secondFunctionalMotherTuples (primeWindow N a f) (cs.length + 3)).filter
        (fun l => l.map (secondFunctionalMotherColour b c e) = cs ++ [3, 3, 3]) := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hl
    exact terminal_insert_mem (mem_sigma.mp hx).1 (mem_sigma.mp hx).2
  have hbound := sum_le_sum_of_subset_of_nonneg hsub
    (fun l _ _ => (Nat.cast_nonneg (secondFunctionalMotherPrefixCarrier N d l).card : (0 : ℝ) ≤ F l))
  simpa only [secondFunctionalMotherPrefixTerm, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, sum_filter] using hbound

private theorem split_last {l : List ℕ} (h : 0 < l.length) :
    ∃ pre p, l = pre ++ [p] := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => exact ⟨[], a, rfl⟩
    | cons b t =>
      obtain ⟨pre, p, he⟩ := ih (by simp)
      exact ⟨a :: pre, p, by simp [he]⟩

private theorem terminal_insert_surjective {N d : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hcop : ∀ r ∈ primeWindow N a f, r.Coprime d) {l : List ℕ}
    (hl : l ∈
      (secondFunctionalMotherTuples (primeWindow N a f) (cs.length + 3)).filter
        (fun l => l.map (secondFunctionalMotherColour b c e) = cs ++ [3, 3, 3])) :
    l ∈ ((terminalBase N a b c e f cs).sigma (terminalWindow N d)).image insertTerminal := by
  obtain ⟨hl, hcol⟩ := mem_filter.mp hl
  obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  obtain ⟨mid, r, q, rfl⟩ := HighNonunit.split_last_two (l := l) (by omega)
  have hmid : 0 < mid.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  obtain ⟨pre, p, rfl⟩ := split_last hmid
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hlen hord hmem hcol ⊢
  have hprelen : pre.length = cs.length := by simpa using hlen
  have hpm := mem_primeWindow.mp (hmem p (by simp))
  have hrmem := hmem r (by simp)
  have hrm := mem_primeWindow.mp hrmem
  have htail : p < r ∧ p < q ∧ r < q := by
    simpa [List.pairwise_cons, and_assoc] using (List.pairwise_append.mp hord).2.1
  simp only [List.map_append, List.map_cons, List.map_nil] at hcol
  have hparts := List.append_inj hcol (by simpa using hprelen)
  have hprecol : pre.map (secondFunctionalMotherColour b c e) = cs := hparts.1
  have htailcol : secondFunctionalMotherColour b c e p = 3 ∧
      secondFunctionalMotherColour b c e r = 3 ∧
      secondFunctionalMotherColour b c e q = 3 := by
    simpa using hparts.2
  have hbase : pre ++ [p, q] ∈ terminalBase N a b c e f cs := by
    apply mem_filter.mpr
    refine ⟨(secondFunctionalMother_tuple_mem _ _ _).mpr
      ⟨by simp [hprelen], ?_, ?_⟩, ?_⟩
    · obtain ⟨hpre, _, hcross⟩ := List.pairwise_append.mp hord
      apply List.pairwise_append.mpr
      refine ⟨hpre, by simpa using htail.2.1, ?_⟩
      intro t ht u hu
      apply hcross t ht u
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
      tauto
    · intro t ht
      apply hmem t
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
      tauto
    · simp [List.map_append, hprecol, htailcol.1, htailcol.2.2]
  have hrpre : r.Coprime pre.prod :=
    secondFunctionalMother_coprime_prod r pre (fun t ht =>
      (Nat.coprime_primes hrm.1 (mem_primeWindow.mp
        (hmem t (List.mem_append_left _ ht))).1).mpr
          (ne_of_gt ((List.pairwise_append.mp hord).2.2 t ht r (by simp))))
  have hrwindow : r ∈ terminalWindow N d (pre ++ [p, q]) := by
    have hrM := (((hcop r hrmem).mul_right hrpre).mul_right
      ((Nat.coprime_primes hrm.1 hpm.1).mpr (ne_of_gt htail.1))).mul_right hrm.2.1
    have hr' : r ∈ primeWindow (d * pre.prod * p * N) p q :=
      mem_primeWindow.mpr ⟨hrm.1, hrM,
        by exact_mod_cast htail.1.le, by exact_mod_cast htail.2.2⟩
    simpa [terminalWindow, terminalMask] using hr'
  exact mem_image.mpr ⟨⟨pre ++ [p, q], r⟩, mem_sigma.mpr ⟨hbase, hrwindow⟩,
    insertTerminal_append pre p q r⟩

theorem terminal_debit_eq_word {N d : ℕ} {a b c e f : ℝ} (cs : List ℕ)
    (hcop : ∀ r ∈ primeWindow N a f, r.Coprime d) :
    terminalDebit N d a b c e f cs =
      secondFunctionalMotherPrefixTerm N d N a b c e f (cs ++ [3, 3, 3]) := by
  have himage :
      ((terminalBase N a b c e f cs).sigma (terminalWindow N d)).image insertTerminal =
      (secondFunctionalMotherTuples (primeWindow N a f) (cs.length + 3)).filter
        (fun l => l.map (secondFunctionalMotherColour b c e) = cs ++ [3, 3, 3]) := by
    apply Subset.antisymm
    · intro l hl
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hl
      exact terminal_insert_mem (mem_sigma.mp hx).1 (mem_sigma.mp hx).2
    · exact fun _ hl => terminal_insert_surjective hcop hl
  unfold terminalDebit
  have he := sum_congr rfl (fun l (hl : l ∈ terminalBase N a b c e f cs) =>
    terminal_difference (N := N) (d := d)
      (by have := ((secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1).1; omega)
      ((secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1).2.1
      (fun p hp => (mem_primeWindow.mp
        (((secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1).2.2 p hp)).1))
  rw [he, sum_sigma']
  simp only [Sigma.eta]
  rw [← sum_image (f := fun l => ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ))
    (terminal_insert_injective (N := N) (d := d) (a := a) (b := b) (c := c)
      (e := e) (f := f) (cs := cs)), himage]
  simp only [secondFunctionalMotherPrefixTerm, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, sum_filter]

noncomputable def terminalUpperWord (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ terminalBase N a b c e f cs, ((terminalUpper N d l).card : ℝ)

theorem terminal_debit_signed (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    terminalDebit N d a b c e f cs =
      secondFunctionalMotherPrefixTerm N d N a b c e f (cs ++ [3, 3]) -
        terminalUpperWord N d a b c e f cs := by
  simp only [terminalDebit, terminalUpperWord, terminalBase,
    secondFunctionalMotherPrefixTerm, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd, sum_sub_distrib, sum_filter]

theorem gamma21_two_debits {N d : ℕ} {a b c e f : ℝ}
    (hcop : ∀ r ∈ primeWindow N a f, r.Coprime d) :
    secondFunctionalMotherPrefixTerm N d N a b c e f [3, 3, 3, 3] -
        terminalUpperWord N d a b c e f [3, 3] -
        terminalUpperWord N d a b c e f [3, 3, 3] =
      secondFunctionalMotherGamma N d N a b c e f 21 := by
  have h4 := terminal_debit_eq_word (b := b) (c := c) (e := e) [3, 3] hcop
  have h5 := terminal_debit_eq_word (b := b) (c := c) (e := e) [3, 3, 3] hcop
  rw [terminal_debit_signed] at h4 h5
  simpa only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.cons_append, List.nil_append] using
      (show _ - terminalUpperWord N d a b c e f [3, 3, 3] = _ from
        (congrArg (fun x => x - terminalUpperWord N d a b c e f [3, 3, 3]) h4).trans h5)

theorem gamma20_terminal_debit (N d : ℕ) (a b c e f : ℝ) :
    terminalDebit N d a b c e f [2, 3] ≤
      secondFunctionalMotherGamma N d N a b c e f 20 := by
  simpa only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.cons_append, List.nil_append] using terminal_debit_le_word N d a b c e f [2, 3]

theorem gamma21_terminal_debit (N d : ℕ) (a b c e f : ℝ) :
    terminalDebit N d a b c e f [3, 3, 3] ≤
      secondFunctionalMotherGamma N d N a b c e f 21 := by
  simpa only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.cons_append, List.nil_append] using terminal_debit_le_word N d a b c e f [3, 3, 3]

end Wu18938Campaign.M2
