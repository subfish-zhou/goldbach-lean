import MathlibNt.ChensTheorem
import MathlibNt.SieveTheory.Chen.Representations
import MathlibNt.Analysis.RationalPower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The literal refined prime count

The carrier filters primes `p`, not a set of representations. The range bound
is redundant: the prime factor `q` makes every complementary product positive.
The unit factor `r = 1` is allowed, but zero and unit complements are not.
-/

namespace Wu2004MeanValue

open Classical Finset
open MathlibNt.ChensTheorem
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

def refinedGood (N : ℕ) (a : ℝ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧
    ∃ r q : ℕ, q.Prime ∧ (r = 1 ∨ r.Prime) ∧
      N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (a - 1))

theorem mem_refinedGood {N p : ℕ} {a : ℝ} :
    p ∈ refinedGood N a ↔ p.Prime ∧
      ∃ r q : ℕ, q.Prime ∧ (r = 1 ∨ r.Prime) ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (a - 1) := by
  simp only [refinedGood, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨r, q, hq, hr, hN, _⟩ := h.2
    have hr0 : 0 < r := hr.elim (fun h => by omega) Nat.Prime.pos
    have hprod := Nat.mul_pos hr0 hq.pos
    exact ⟨by omega, h⟩

/-- Increasing the exponent retains every previously counted prime. -/
theorem refinedGood_mono (N : ℕ) : Monotone (refinedGood N) := by
  intro a b hab p hp
  obtain ⟨hpp, r, q, hq, hr, hN, hpower⟩ := mem_refinedGood.mp hp
  exact mem_refinedGood.mpr ⟨hpp, r, q, hq, hr, hN,
    hpower.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hq.one_lt.le) (sub_le_sub_right hab 1))⟩

/-- The requested 1.894 imbalance written entirely in natural powers.
This equivalence also holds when either input is zero. -/
theorem one894_power_iff (r q : ℕ) :
    r ^ 500 ≤ q ^ 447 ↔ (r : ℝ) ≤ (q : ℝ) ^ ((947 / 500 : ℝ) - 1) := by
  simpa only [Nat.cast_ofNat, show (447 : ℝ) / 500 = (947 / 500 : ℝ) - 1 by norm_num] using
    MathlibNt.nat_pow_le_iff_le_rpow r q 447 500 (by decide)

/-- Exact membership, preserving the original counted prime and both factors. -/
theorem mem_refinedGood_one894_iff {N p : ℕ} :
    p ∈ refinedGood N (947 / 500) ↔ p.Prime ∧
      ∃ r q : ℕ, q.Prime ∧ (r = 1 ∨ r.Prime) ∧
        N = p + r * q ∧ r ^ 500 ≤ q ^ 447 := by
  rw [mem_refinedGood]
  simp_rw [one894_power_iff]

/-- Wu's 1.8938 carrier embeds in the requested 1.894 carrier. -/
theorem source_refinedGood_subset_one894 (N : ℕ) :
    refinedGood N (9469 / 5000) ⊆ refinedGood N (947 / 500) :=
  refinedGood_mono N (by norm_num)

/-- Thus any lower bound for the source count transfers without loss. -/
theorem source_refinedGood_card_le_one894 (N : ℕ) :
    (refinedGood N (9469 / 5000)).card ≤ (refinedGood N (947 / 500)).card :=
  card_le_card (source_refinedGood_subset_one894 N)

/-- Positive source count gives an actual representation with the requested
integer-power constraint. The analytic positivity estimate remains upstream. -/
theorem exists_one894_of_source_count_pos {N : ℕ}
    (h : 0 < (refinedGood N (9469 / 5000)).card) :
    ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
      N = p + r * q ∧ r ^ 500 ≤ q ^ 447 := by
  obtain ⟨p, hp⟩ := card_pos.mp h
  obtain ⟨hpp, r, q, hq, hr, hN, hpower⟩ :=
    mem_refinedGood_one894_iff.mp (source_refinedGood_subset_one894 N hp)
  exact ⟨p, r, q, hpp, hr, hq, hN, hpower⟩

theorem refinedGood_complement_ge_two {N p : ℕ} {a : ℝ}
    (hp : p ∈ refinedGood N a) : 2 ≤ N - p := by
  obtain ⟨_, r, q, hq, hr, hN, _⟩ := mem_refinedGood.mp hp
  have hr1 : 1 ≤ r := hr.elim (fun h => by omega) (fun h => h.one_lt.le)
  have hprod : q ≤ r * q := Nat.le_mul_of_pos_left q hr1
  have hq2 := hq.two_le
  omega

theorem not_mem_refinedGood_of_complement_le_one {N p : ℕ} {a : ℝ}
    (h : N - p ≤ 1) : p ∉ refinedGood N a := by
  intro hp
  have := refinedGood_complement_ge_two hp
  omega

theorem refinedGood_subset_chenGood (N : ℕ) (a : ℝ) :
    refinedGood N a ⊆ chenGoodRepresentations N := by
  intro p hp
  obtain ⟨hpp, r, q, hq, hr, hN, _⟩ := mem_refinedGood.mp hp
  have hs : Semiprime (N - p) := by
    rw [hN, Nat.add_sub_cancel_left]
    rcases hr with rfl | hr
    · simpa only [one_mul] using prime_semiprime hq
    · exact mul_prime_semiprime hr hq
  have hlt : p < N := by have := hs.1; omega
  exact mem_filter.mpr ⟨mem_range.mpr hlt, hpp, hs⟩

theorem prime_complement_mem_refinedGood {N p : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hp : p.Prime) (hq : (N - p).Prime) :
    p ∈ refinedGood N a := by
  have hq2 := hq.two_le
  have hpN : p ≤ N := by omega
  apply mem_refinedGood.mpr
  refine ⟨hp, 1, N - p, hq, Or.inl rfl, ?_, ?_⟩
  · simp only [one_mul]
    omega
  · simpa only [Nat.cast_one] using Real.one_le_rpow
      (by exact_mod_cast hq.one_lt.le) (by linarith : 0 ≤ a - 1)

theorem refined_prime_factor_lt {r q : ℕ} {a : ℝ}
    (hq : q.Prime) (ha : a < 2)
    (hgood : (r : ℝ) ≤ (q : ℝ) ^ (a - 1)) : r < q := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hpow : (q : ℝ) ^ (a - 1) < q :=
    Real.rpow_lt_self_of_one_lt hq1 (by linarith)
  exact_mod_cast hgood.trans_lt hpow

theorem refined_prime_factor_ordered {r q : ℕ} {a : ℝ}
    (hq : q.Prime) (ha : a < 2)
    (hgood : (r : ℝ) ≤ (q : ℝ) ^ (a - 1)) : r ≤ q :=
  (refined_prime_factor_lt hq ha hgood).le

theorem prime_square_is_bad {q : ℕ} {a : ℝ} (hq : q.Prime) (ha : a < 2) :
    (q : ℝ) ^ (a - 1) < q :=
  Real.rpow_lt_self_of_one_lt (by exact_mod_cast hq.one_lt) (by linarith)

/-- Ordered prime factors are unique, including the diagonal. -/
theorem ordered_prime_factors_unique {r q s t : ℕ}
    (hr : r.Prime) (_hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrq : r ≤ q) (hst : s ≤ t) (he : r * q = s * t) :
    r = s ∧ q = t := by
  have hd : r ∣ s * t := he ▸ dvd_mul_right r q
  rcases hr.dvd_mul.mp hd with hds | hdt
  · have hrs := (Nat.prime_dvd_prime_iff_eq hr hs).mp hds
    subst s
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hr.pos he⟩
  · have hrt := (Nat.prime_dvd_prime_iff_eq hr ht).mp hdt
    subst t
    have hqs : q = s := Nat.eq_of_mul_eq_mul_left hr.pos
      (he.trans (Nat.mul_comm s r))
    omega

theorem chenGood_prime_or_ordered_product {N p : ℕ}
    (hp : p ∈ chenGoodRepresentations N) :
    p.Prime ∧ ((N - p).Prime ∨
      ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r ≤ q ∧ N = p + r * q) := by
  obtain ⟨hpN, hpp, hs⟩ := mem_filter.mp hp
  have hpN' : p < N := mem_range.mp hpN
  refine ⟨hpp, ?_⟩
  rcases semiprime_iff.mp hs with hprime | ⟨r, q, hr, hq, he⟩
  · exact Or.inl hprime
  · right
    rcases le_total r q with hrq | hqr
    · exact ⟨r, q, hr, hq, hrq, by omega⟩
    · refine ⟨q, r, hq, hr, hqr, ?_⟩
      rw [Nat.mul_comm q r]
      omega

end
end Wu2004MeanValue
