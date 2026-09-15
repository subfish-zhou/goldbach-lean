import MathlibNt.Wu2008DoubleSieve.NinthSwitchingCount
import MathlibNt.Wu2008DoubleSieve.Omega3R1Layers

/-!
# Exact ninth-term pair-product and prime-profile transport

Ordered prime pairs have unique products. Only after proving this
injectivity do we replace the pair labels by their product support.
Both profile endpoints retain the original strict/non-strict boundaries.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def ninthPairProduct (t : ℕ × ℕ) : ℕ := t.1 * t.2

/-- Strict ordering rules out the exchanged prime factorization. -/
theorem ninth_ordered_prime_product_injective {a b a' b' : ℕ}
    (ha : a.Prime) (hb : b.Prime) (ha' : a'.Prime) (hb' : b'.Prime)
    (hab : a < b) (hab' : a' < b') (h : a * b = a' * b') :
    (a, b) = (a', b') := by
  have hd : a ∣ a' * b' := h ▸ dvd_mul_right a b
  rcases ha.dvd_mul.mp hd with haa | habb
  · have haa' : a = a' := ((Nat.dvd_prime ha').mp haa).resolve_left ha.ne_one
    have hbb' : b = b' := by have := ha.pos; nlinarith
    exact Prod.ext haa' hbb'
  · have hab' : a = b' := ((Nat.dvd_prime hb').mp habb).resolve_left ha.ne_one
    have hba' : b = a' := by have := ha.pos; nlinarith
    have := hb.pos
    omega

theorem ninthPairProduct_injOn (N : ℕ) (w u : ℝ) :
    Set.InjOn ninthPairProduct (ninthPairs N w u) := by
  rintro ⟨a, b⟩ ht ⟨a', b'⟩ ht' h
  obtain ⟨ha, hb, _, _, _, hab, _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  obtain ⟨ha', hb', _, _, _, hab', _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht').1
  exact ninth_ordered_prime_product_injective ha hb ha' hb' hab hab' h

noncomputable def M9 (N : ℕ) (w u : ℝ) : Finset ℕ :=
  (ninthPairs N w u).image ninthPairProduct

noncomputable def ninthProfileLower (u : ℝ) : ℝ := ((⌈u⌉ : ℤ) - 1 : ℤ)

noncomputable def ninthProfileUpper (N m : ℕ) : ℝ := ((N : ℝ) - 1) / m

theorem ninthProfileLower_lt (u : ℝ) : ninthProfileLower u < u := by
  have h := Int.ceil_lt_add_one u
  simp only [ninthProfileLower, Int.cast_sub, Int.cast_one]
  linarith

theorem ninthProfileLower_lt_nat_iff (u : ℝ) (c : ℕ) :
    ninthProfileLower u < (c : ℝ) ↔ u ≤ (c : ℝ) := by
  have h : (⌈u⌉ : ℤ) - 1 < (c : ℤ) ↔ (⌈u⌉ : ℤ) ≤ (c : ℤ) := by omega
  calc
    ninthProfileLower u < (c : ℝ) ↔ (⌈u⌉ : ℤ) - 1 < (c : ℤ) := by
      unfold ninthProfileLower
      norm_cast
    _ ↔ (⌈u⌉ : ℤ) ≤ (c : ℤ) := h
    _ ↔ u ≤ (c : ℝ) := by simpa only [Int.cast_natCast] using (Int.ceil_le (a := u) (z := (c : ℤ)))

theorem ninthProfileUpper_nat_iff {N m c : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (c : ℝ) ≤ ninthProfileUpper N m ↔ m * c < N := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (show 1 ≤ N from hN)
  rw [ninthProfileUpper, le_div_iff₀ hmR, ← hcast]
  have h : c * m ≤ N - 1 ↔ m * c < N := by
    rw [Nat.mul_comm c m]
    omega
  exact_mod_cast h

theorem ninthPair_product_pos {N : ℕ} {w u : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N w u) : 0 < ninthPairProduct t := by
  obtain ⟨ha, hb, _⟩ := mem_lowerPairs_source.mp (mem_filter.mp ht).1
  exact Nat.mul_pos ha.pos hb.pos

theorem ninthPair_N_pos {N : ℕ} {w u : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N w u) : 0 < N := by
  obtain ⟨ha, _, _, _, _, _, hsize⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  have := (lower_pair_size_iff ha.pos).mpr hsize
  omega

/-- Equality of the actual cofactor fibres, including both endpoints and
the output-prime filter. No output condition enters the product support. -/
theorem ninthPair_fibre_eq_profile {N : ℕ} {w u : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N w u) :
    (range (N + 1)).filter (fun c : ℕ =>
      c.Prime ∧ u ≤ (c : ℝ) ∧ t.1 * t.2 * c < N ∧
        (N - t.1 * t.2 * c).Prime) =
      (omega3ProfilePrimes N (ninthProfileLower u)
        (ninthProfileUpper N (ninthPairProduct t))).filter
          (fun c => (N - ninthPairProduct t * c).Prime) := by
  ext c
  simp only [omega3ProfilePrimes, mem_filter, ninthProfileLower_lt_nat_iff]
  rw [ninthProfileUpper_nat_iff (ninthPair_N_pos ht) (ninthPair_product_pos ht)]
  simp only [ninthPairProduct]
  tauto

/-- Exact natural-number cardinality reindexing, with no multiplicity
factor and no boundary error. -/
theorem T9_card_eq_product_profiles (N : ℕ) (w u : ℝ) :
    (T9 N w u).card =
      ∑ m ∈ M9 N w u,
        ((omega3ProfilePrimes N (ninthProfileLower u)
          (ninthProfileUpper N m)).filter (fun c => (N - m * c).Prime)).card := by
  rw [T9, card_sigma, M9, sum_image (ninthPairProduct_injOn N w u)]
  apply sum_congr rfl
  intro t ht
  rw [ninthPair_fibre_eq_profile ht]

end Wu2008DoubleSieve
