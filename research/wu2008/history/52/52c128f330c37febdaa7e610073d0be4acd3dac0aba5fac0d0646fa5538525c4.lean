import MathlibNt.Wu2008DoubleSieve.NinthSwitchingCofactor

/-!
# Labelled ninth-term carriers and uniform fibre budgets

The sigma coordinates retain both selected primes and the prime index (or
cofactor). In particular the switching carrier imposes neither `b < c` nor
distinctness of `c` from the selected primes.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev NinthLabel := Sigma (fun _ : ℕ × ℕ => ℕ)

noncomputable def ninthPairs (N : ℕ) (w u : ℝ) : Finset (ℕ × ℕ) :=
  (lowerPairs N N w u).filter (fun t => (t.1 : ℝ) < u)

noncomputable def ninthAtoms (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthPairs N w u).sigma (fun t =>
    sieveCarrier N (t.1 * t.2) (N * t.1)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2))))

/-- The actual cutoff-preserving, fully labelled finite switching count. -/
noncomputable def T9 (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthPairs N w u).sigma (fun t =>
    (range (N + 1)).filter (fun c =>
      c.Prime ∧ u ≤ (c : ℝ) ∧ t.1 * t.2 * c < N ∧
        (N - t.1 * t.2 * c).Prime))

/-- The finite window for the cofactor adds no restriction to the source
conditions: the selected primes are positive and their product is at least one. -/
theorem mem_T9 {N : ℕ} {w u : ℝ} {x : NinthLabel} :
    x ∈ T9 N w u ↔ x.1 ∈ ninthPairs N w u ∧
      x.2.Prime ∧ u ≤ (x.2 : ℝ) ∧ x.1.1 * x.1.2 * x.2 < N ∧
        (N - x.1.1 * x.1.2 * x.2).Prime := by
  simp only [T9, mem_sigma, mem_filter, mem_range]
  constructor
  · rintro ⟨ht, _, hc⟩
    exact ⟨ht, hc⟩
  · rintro ⟨ht, hc⟩
    obtain ⟨ha, hb, _⟩ :=
      mem_lowerPairs_source.mp (mem_filter.mp ht).1
    have hab : 1 ≤ x.1.1 * x.1.2 := Nat.succ_le_of_lt (Nat.mul_pos ha.pos hb.pos)
    have hcle : x.2 ≤ x.1.1 * x.1.2 * x.2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right x.2 hab
    exact ⟨ht, by omega, hc⟩

def ninthCofactor (N : ℕ) (x : NinthLabel) : ℕ :=
  (N - x.2) / (x.1.1 * x.1.2)

theorem ninthAtoms_card (N : ℕ) (w u : ℝ) :
    ((ninthAtoms N w u).card : ℝ) = (variableS3Main N w u : ℝ) := by
  simp only [ninthAtoms, card_sigma, Nat.cast_sum, variableS3Main,
    sieveCount, Int.cast_sum, Int.cast_natCast, ninthPairs]

theorem mem_ninthAtoms {N : ℕ} {w u : ℝ} {x : NinthLabel} :
    x ∈ ninthAtoms N w u ↔ x.1 ∈ ninthPairs N w u ∧
      x.2 ∈ sieveCarrier N (x.1.1 * x.1.2) (N * x.1.1)
        (Real.sqrt ((N : ℝ) / ((x.1.1 : ℝ) * x.1.2))) := by
  exact mem_sigma

theorem ninthAtom_index {N : ℕ} {w u : ℝ} {x : NinthLabel}
    (hx : x ∈ ninthAtoms N w u) : x.2 ∈ primeIndices N := by
  obtain ⟨hrange, hp, _⟩ := mem_filter.mp (mem_ninthAtoms.mp hx).2
  exact mem_primeIndices.mpr ⟨by have := mem_range.mp hrange; omega, hp⟩

theorem ninthAtom_dvd {N : ℕ} {w u : ℝ} {x : NinthLabel}
    (hx : x ∈ ninthAtoms N w u) : x.1.1 * x.1.2 ∣ N - x.2 :=
  (mem_filter.mp (mem_ninthAtoms.mp hx).2).2.2.1

theorem ninthAtom_mul_cofactor {N : ℕ} {w u : ℝ} {x : NinthLabel}
    (hx : x ∈ ninthAtoms N w u) :
    x.1.1 * x.1.2 * ninthCofactor N x = N - x.2 :=
  Nat.mul_div_cancel' (ninthAtom_dvd hx)

theorem ninthAtom_pair_divisors {N : ℕ} {w u : ℝ} {x : NinthLabel}
    (hx : x ∈ ninthAtoms N w u) (hn : 0 < N - x.2) :
    x.1 ∈ largePrimeDivisors (N - x.2) w ×ˢ largePrimeDivisors (N - x.2) w := by
  obtain ⟨ht, _⟩ := mem_filter.mp (mem_ninthAtoms.mp hx).1
  obtain ⟨ha, hb, _, hwa, _, hab, _⟩ := mem_lowerPairs_source.mp ht
  have hwb : w ≤ (x.1.2 : ℝ) :=
    hwa.trans (by exact_mod_cast hab.le)
  have hd := ninthAtom_dvd hx
  exact mem_product.mpr
    ⟨mem_largePrimeDivisors.mpr
      ⟨ha, (dvd_mul_right _ _).trans hd, Nat.ne_of_gt hn, hwa⟩,
     mem_largePrimeDivisors.mpr
      ⟨hb, (dvd_mul_left _ _).trans hd, Nat.ne_of_gt hn, hwb⟩⟩

/-- Each positive complement has at most `1 / k^2` ordered pair labels.
No squarefreeness assumption enters this budget. -/
theorem ninth_pair_budget {N n : ℕ} {k : ℝ}
    (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) (hk : 0 < k) :
    ((largePrimeDivisors n ((N : ℝ) ^ k) ×ˢ
      largePrimeDivisors n ((N : ℝ) ^ k)).card : ℝ) ≤ 1 / k ^ 2 := by
  have h := largePrimeDivisors_card_le_inv hN hn hnN hk
  rw [card_product, Nat.cast_mul, ← pow_two]
  simpa only [div_pow, one_pow] using
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 2

/-- Regroup an actual subset of atoms by its prime index, then pay the
ordered pair fibre once. The map only permutes labels. -/
theorem ninth_atoms_card_le_indices {N : ℕ} {k u : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k)
    {A : Finset NinthLabel} (hA : A ⊆ ninthAtoms N ((N : ℝ) ^ k) u)
    {S : Finset ℕ} (hS : S ⊆ primeIndices N)
    (hindex : ∀ x ∈ A, x.2 ∈ S) :
    (A.card : ℝ) ≤ (1 / k ^ 2) * S.card := by
  let F := fun r => largePrimeDivisors (N - r) ((N : ℝ) ^ k)
  have hinj : A.card ≤ (S.sigma (fun r => F r ×ˢ F r)).card := by
    apply card_le_card_of_injOn (fun x : NinthLabel =>
      (⟨x.2, x.1⟩ : Sigma (fun _ : ℕ => ℕ × ℕ)))
    · intro x hx
      have hr := mem_primeIndices.mp (ninthAtom_index (hA hx))
      exact mem_sigma.mpr ⟨hindex x hx,
        ninthAtom_pair_divisors (hA hx) (complement_pos_of_even hN he hr.1 hr.2)⟩
    · intro x _ y _ h
      have hr := congrArg Sigma.fst h
      have ht := congrArg (fun z : Sigma (fun _ : ℕ => ℕ × ℕ) => z.2) h
      exact Sigma.ext ht (heq_of_eq hr)
  calc
    (A.card : ℝ) ≤ ((S.sigma (fun r => F r ×ˢ F r)).card : ℝ) := by
      exact_mod_cast hinj
    _ = ∑ r ∈ S, ((F r ×ˢ F r).card : ℝ) := by
      rw [card_sigma, Nat.cast_sum]
    _ ≤ ∑ _r ∈ S, (1 / k ^ 2 : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hrN, hrp⟩ := mem_primeIndices.mp (hS hr)
      exact ninth_pair_budget (by omega)
        (complement_pos_of_even hN he hrN hrp) (Nat.sub_le N r) hk
    _ = (1 / k ^ 2) * S.card := by
      simp only [sum_const, nsmul_eq_mul, mul_comm]

/-- The complementary version uses the injective map `r -> N-r` on the
bounded prime indices; all pair multiplicities remain intact. -/
theorem ninth_atoms_card_le_complements {N : ℕ} {k u : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k)
    {A : Finset NinthLabel} (hA : A ⊆ ninthAtoms N ((N : ℝ) ^ k) u)
    {E : Finset ℕ} (hcomp : ∀ x ∈ A, N - x.2 ∈ E) :
    (A.card : ℝ) ≤ (1 / k ^ 2) * E.card := by
  have h := ninth_atoms_card_le_indices hN he hk hA
    (S := (primeIndices N).filter (fun r => N - r ∈ E))
    (filter_subset _ _) (fun x hx =>
      mem_filter.mpr ⟨ninthAtom_index (hA hx), hcomp x hx⟩)
  exact h.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast primeComplement_filter_card_le N E) (by positivity))

end Wu2008DoubleSieve
