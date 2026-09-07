import MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount
import Mathlib.NumberTheory.PrimeCounting

/-!
# The exact base range, including prime squares

Below the square of the sieve threshold a rough integer is a unit or a prime.
At the square endpoint there is one additional integer precisely when the
threshold itself is prime.
-/

set_option autoImplicit false

namespace LiLiuPrereqBuchstab

theorem rough_prime_iff {z : ℝ} {p : ℕ} (hp : p.Prime) :
    Rough z p ↔ z ≤ (p : ℝ) := by
  rw [rough_iff_minFac hp.ne_one, hp.minFac_eq]

theorem sq_le_of_rough_composite {z : ℝ} {n : ℕ} (hz : 0 ≤ z)
    (hn0 : 0 < n) (hn1 : n ≠ 1) (hnp : ¬n.Prime) (hr : Rough z n) :
    z ^ 2 ≤ (n : ℝ) := by
  have hmin := (rough_iff_minFac hn1).mp hr
  have hs : (n.minFac : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.minFac_sq_le_self hn0 hnp
  nlinarith

theorem rough_composite_at_sq {x z : ℝ} {n : ℕ} (hz : 0 ≤ z)
    (hx : x ≤ z ^ 2) (hn : n ∈ roughNumbers x z)
    (hn1 : n ≠ 1) (hnp : ¬n.Prime) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) = z ∧ n = p ^ 2 ∧ x = z ^ 2 := by
  obtain ⟨hn0, hnx, hr⟩ := mem_roughNumbers.mp hn
  have hmin := (rough_iff_minFac hn1).mp hr
  have hs : (n.minFac : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.minFac_sq_le_self hn0 hnp
  have hpz : (n.minFac : ℝ) = z := by
    nlinarith [sq_nonneg ((n.minFac : ℝ) - z)]
  have hnz : (n : ℝ) = z ^ 2 := by
    nlinarith
  refine ⟨n.minFac, Nat.minFac_prime hn1, hpz, ?_, by linarith⟩
  exact_mod_cast (show (n : ℝ) = (n.minFac : ℝ) ^ 2 by rw [hpz, hnz])

theorem rough_below_sq_iff {x z : ℝ} (hz : 0 ≤ z) (hx : x < z ^ 2) {n : ℕ} :
    n ∈ roughNumbers x z ↔
      (n = 1 ∧ 1 ≤ x) ∨ (n.Prime ∧ z ≤ (n : ℝ) ∧ (n : ℝ) ≤ x) := by
  constructor
  · intro hn
    by_cases hn1 : n = 1
    · subst n
      exact Or.inl ⟨rfl, one_mem_roughNumbers.mp hn⟩
    · obtain ⟨hn0, hnx, hr⟩ := mem_roughNumbers.mp hn
      have hnp : n.Prime := by
        by_contra h
        have := sq_le_of_rough_composite hz hn0 hn1 h hr
        linarith
      exact Or.inr ⟨hnp, (rough_prime_iff hnp).mp hr, hnx⟩
  · rintro (⟨rfl, hx⟩ | ⟨hnp, hzn, hnx⟩)
    · exact one_mem_roughNumbers.mpr hx
    · exact mem_roughNumbers.mpr ⟨hnp.pos, hnx, (rough_prime_iff hnp).mpr hzn⟩

noncomputable def primeNumbers (x z : ℝ) : Finset ℕ :=
  (roughNumbers x z).filter Nat.Prime

@[simp] theorem mem_primeNumbers {x z : ℝ} {n : ℕ} :
    n ∈ primeNumbers x z ↔ n.Prime ∧ z ≤ (n : ℝ) ∧ (n : ℝ) ≤ x := by
  simp only [primeNumbers, Finset.mem_filter, mem_roughNumbers]
  constructor
  · rintro ⟨⟨_, hnx, hr⟩, hp⟩
    exact ⟨hp, (rough_prime_iff hp).mp hr, hnx⟩
  · rintro ⟨hp, hzn, hnx⟩
    exact ⟨⟨hp.pos, hnx, (rough_prime_iff hp).mpr hzn⟩, hp⟩

/-- This base formula uses actual primes and includes the unit. -/
theorem roughCount_below_sq {x z : ℝ} (hz : 0 ≤ z)
    (hx1 : 1 ≤ x) (hx : x < z ^ 2) :
    roughCount x z = 1 + (primeNumbers x z).card := by
  classical
  have he : roughNumbers x z = insert 1 (primeNumbers x z) := by
    ext n
    rw [rough_below_sq_iff hz hx, Finset.mem_insert, mem_primeNumbers]
    simp [hx1]
  have hn : 1 ∉ primeNumbers x z := by simp [Nat.not_prime_one]
  rw [roughCount, he, Finset.card_insert_of_notMem hn, Nat.add_comm]

/-- The only nonunit, nonprime rough integer at the square endpoint is `p²`. -/
theorem roughNumbers_prime_sq {p : ℕ} (hp : p.Prime) :
    roughNumbers ((p : ℝ) ^ 2) p =
      insert 1 (insert (p ^ 2) (primeNumbers ((p : ℝ) ^ 2) p)) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  ext n
  simp only [Finset.mem_insert, mem_primeNumbers]
  constructor
  · intro hn
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · by_cases hnp : n.Prime
      · obtain ⟨_, hnx, hr⟩ := mem_roughNumbers.mp hn
        exact Or.inr (Or.inr ⟨hnp, (rough_prime_iff hnp).mp hr, hnx⟩)
      · obtain ⟨q, _, hqp, hnq, _⟩ :=
          rough_composite_at_sq hp0 le_rfl hn hn1 hnp
        have hqp' : q = p := by exact_mod_cast hqp
        exact Or.inr (Or.inl (hqp' ▸ hnq))
  · rintro (rfl | rfl | ⟨hnp, hpn, hnx⟩)
    · exact one_mem_roughNumbers.mpr (by nlinarith)
    · refine mem_roughNumbers.mpr ⟨pow_pos hp.pos 2, by simp, ?_⟩
      simpa [pow_two] using rough_mul_prime hp ((rough_prime_iff hp).mpr le_rfl)
    · exact mem_roughNumbers.mpr ⟨hnp.pos, hnx, (rough_prime_iff hnp).mpr hpn⟩

theorem roughCount_prime_sq {p : ℕ} (hp : p.Prime) :
    roughCount ((p : ℝ) ^ 2) p = 2 + (primeNumbers ((p : ℝ) ^ 2) p).card := by
  classical
  have hp1 : p ^ 2 ≠ 1 := by nlinarith [hp.two_le]
  have hnp : ¬(p ^ 2).Prime := by
    intro h
    have hd : p ∣ p ^ 2 := by exact ⟨p, by ring⟩
    have he : p = p ^ 2 := (Nat.dvd_prime h).mp hd |>.resolve_left hp.ne_one
    nlinarith [hp.two_le]
  have hs : p ^ 2 ∉ primeNumbers ((p : ℝ) ^ 2) p := by simp [hnp]
  have h1 : 1 ∉ insert (p ^ 2) (primeNumbers ((p : ℝ) ^ 2) p) := by
    simp [Ne.symm hp1, Nat.not_prime_one]
  rw [roughCount, roughNumbers_prime_sq hp, Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem hs]
  omega

theorem roughCount_le_sq_no_square {x z : ℝ} (hz : 0 ≤ z)
    (hx1 : 1 ≤ x) (hx : x ≤ z ^ 2)
    (hnsq : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) = z ∧ x = z ^ 2) :
    roughCount x z = 1 + (primeNumbers x z).card := by
  classical
  have he : roughNumbers x z = insert 1 (primeNumbers x z) := by
    ext n
    simp only [Finset.mem_insert, mem_primeNumbers]
    constructor
    · intro hn
      by_cases hn1 : n = 1
      · exact Or.inl hn1
      · by_cases hnp : n.Prime
        · obtain ⟨_, hnx, hr⟩ := mem_roughNumbers.mp hn
          exact Or.inr ⟨hnp, (rough_prime_iff hnp).mp hr, hnx⟩
        · obtain ⟨p, hp, hpz, _, hxz⟩ := rough_composite_at_sq hz hx hn hn1 hnp
          exact (hnsq ⟨p, hp, hpz, hxz⟩).elim
    · rintro (rfl | ⟨hnp, hzn, hnx⟩)
      · exact one_mem_roughNumbers.mpr hx1
      · exact mem_roughNumbers.mpr ⟨hnp.pos, hnx, (rough_prime_iff hnp).mpr hzn⟩
  have hn : 1 ∉ primeNumbers x z := by simp [Nat.not_prime_one]
  rw [roughCount, he, Finset.card_insert_of_notMem hn, Nat.add_comm]

noncomputable def squareCorrection (x z : ℝ) : ℕ := by
  classical
  exact if ∃ p : ℕ, p.Prime ∧ (p : ℝ) = z ∧ x = z ^ 2 then 1 else 0

/-- Exact formula on the entire closed base range. The final indicator is
nonzero only at a prime-square endpoint, not at every square endpoint. -/
theorem roughCount_le_sq {x z : ℝ} (hz : 0 ≤ z)
    (hx1 : 1 ≤ x) (hx : x ≤ z ^ 2) :
    roughCount x z = 1 + (primeNumbers x z).card + squareCorrection x z := by
  classical
  unfold squareCorrection
  split_ifs with h
  · obtain ⟨p, hp, rfl, rfl⟩ := h
    rw [roughCount_prime_sq hp]
    omega
  · rw [roughCount_le_sq_no_square hz hx1 hx h, Nat.add_zero]

theorem primeNumbers_eq_sdiff {x z : ℝ} (hx : 0 ≤ x) :
    primeNumbers x z = (⌊x⌋₊ + 1).primesBelow \ (⌈z⌉₊).primesBelow := by
  classical
  ext n
  simp only [mem_primeNumbers, Finset.mem_sdiff, Nat.mem_primesBelow,
    Nat.lt_succ_iff, Nat.le_floor_iff hx, Nat.lt_ceil]
  constructor
  · rintro ⟨hp, hzn, hnx⟩
    exact ⟨⟨hnx, hp⟩, fun h => (not_lt_of_ge hzn) h.1⟩
  · rintro ⟨⟨hnx, hp⟩, h⟩
    exact ⟨hp, le_of_not_gt (fun hnz => h ⟨hnz, hp⟩), hnx⟩

/-- `primeCounting' (ceil z)` counts primes strictly below the real cutoff.
In particular a prime equal to `z` is not subtracted. -/
theorem card_primeNumbers {x z : ℝ} (hx : 0 ≤ x) (hzx : z ≤ x) :
    (primeNumbers x z).card =
      Nat.primeCounting ⌊x⌋₊ - Nat.primeCounting' ⌈z⌉₊ := by
  classical
  have hs : (⌈z⌉₊).primesBelow ⊆ (⌊x⌋₊ + 1).primesBelow := by
    intro p hp
    obtain ⟨hpz, hp⟩ := Nat.mem_primesBelow.mp hp
    have hpx : (p : ℝ) ≤ x := ((Nat.lt_ceil.mp hpz).trans_le hzx).le
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_iff.mpr (Nat.le_floor hpx), hp⟩
  rw [primeNumbers_eq_sdiff hx, Finset.card_sdiff_of_subset hs,
    Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow_card_eq_primeCounting',
    Nat.primeCounting_eq_primeCounting'_succ]

theorem roughCount_le_sq_primeCounting {x z : ℝ} (hz : 0 ≤ z)
    (hx1 : 1 ≤ x) (hzx : z ≤ x) (hx : x ≤ z ^ 2) :
    roughCount x z = 1 +
      (Nat.primeCounting ⌊x⌋₊ - Nat.primeCounting' ⌈z⌉₊) + squareCorrection x z := by
  rw [roughCount_le_sq hz hx1 hx, card_primeNumbers (by linarith) hzx]

end LiLiuPrereqBuchstab