import MathlibNt.Wu2008DoubleSieve.ReboxingEndpoints
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Literal geometric endpoints in Wu04 (3.15)

Wu04 source lines 997--1022, cited by Wu08 Lemma 3.1(iii).
The index is real: in particular `j-i-1` is never a truncated natural
subtraction. The terminal index is a natural number and can be zero.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def reboxingAlpha (q Δ t j : ℝ) : ℝ :=
  q ^ (1 / t) * Δ ^ j

theorem reboxingAlpha_pos {q Δ t j : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) :
    0 < reboxingAlpha q Δ t j :=
  mul_pos (rpow_pos_of_pos hq _) (rpow_pos_of_pos hΔ _)

theorem reboxingAlpha_zero (q Δ t : ℝ) :
    reboxingAlpha q Δ t 0 = q ^ (1 / t) := by
  simp [reboxingAlpha]

theorem reboxingAlpha_step {q Δ t j : ℝ} (hΔ : 0 < Δ) :
    reboxingAlpha q Δ t (j + 1) = reboxingAlpha q Δ t j * Δ := by
  simp [reboxingAlpha, rpow_add hΔ, mul_assoc]

theorem reboxingAlpha_strictMono {q Δ t : ℝ} (hq : 0 < q) (hΔ : 1 < Δ) :
    StrictMono (reboxingAlpha q Δ t) := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (rpow_lt_rpow_of_exponent_lt hΔ hab)
    (rpow_pos_of_pos hq _)

/-- The actual terminal index exists even for equal outer parameters. -/
theorem reboxingAlpha_exists_terminal {q Δ s t : ℝ}
    (hq : 1 ≤ q) (hΔ : 1 < Δ) (hs : 0 < s) (hst : s ≤ t) :
    ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
      q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) := by
  have ha : 0 < q ^ (1 / t) := rpow_pos_of_pos (by linarith) _
  have hle : q ^ (1 / t) ≤ q ^ (1 / s) :=
    rpow_le_rpow_of_exponent_le hq (one_div_le_one_div_of_le hs hst)
  obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near ((one_le_div ha).2 hle) hΔ
  refine ⟨r, ?_, ?_⟩
  · simpa [reboxingAlpha, mul_comm] using (le_div_iff₀ ha).1 hr
  · simpa [reboxingAlpha, rpow_add (by linarith : 0 < Δ), pow_succ,
      mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ ha).1 hr'

theorem reboxingAlpha_terminal_unique {q Δ s t : ℝ} {r n : ℕ}
    (hq : 0 < q) (hΔ : 1 < Δ)
    (hr : reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
      q ^ (1 / s) < reboxingAlpha q Δ t (r + 1))
    (hn : reboxingAlpha q Δ t n ≤ q ^ (1 / s) ∧
      q ^ (1 / s) < reboxingAlpha q Δ t (n + 1)) : r = n := by
  have hm := (reboxingAlpha_strictMono (t := t) hq hΔ).monotone
  have h1 : ¬r < n := by
    intro h
    have hh := hm (show (r : ℝ) + 1 ≤ n by exact_mod_cast h)
    exact (not_lt_of_ge (hh.trans hn.1)) hr.2
  have h2 : ¬n < r := by
    intro h
    have hh := hm (show (n : ℝ) + 1 ≤ r by exact_mod_cast h)
    exact (not_lt_of_ge (hh.trans hr.1)) hn.2
  omega

theorem reboxingAlpha_terminal_equal {q Δ s : ℝ} {r : ℕ}
    (hq : 0 < q) (hΔ : 1 < Δ)
    (hr : reboxingAlpha q Δ s r ≤ q ^ (1 / s) ∧
      q ^ (1 / s) < reboxingAlpha q Δ s (r + 1)) : r = 0 := by
  apply reboxingAlpha_terminal_unique hq hΔ hr
  constructor
  · simp [reboxingAlpha]
  · simpa [reboxingAlpha] using
      mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq (1 / s))

/-- Exact, unique half-open membership. No nonzero-terminal assumption. -/
theorem reboxingAlpha_partition {q Δ t x : ℝ} (hq : 0 < q) (hΔ : 1 < Δ)
    (r : ℕ) :
    reboxingAlpha q Δ t 0 ≤ x ∧ x < reboxingAlpha q Δ t r ↔
      ∃! j : ℕ, j < r ∧ reboxingAlpha q Δ t j ≤ x ∧
        x < reboxingAlpha q Δ t (j + 1) := by
  have hm := reboxingAlpha_strictMono (t := t) hq hΔ
  constructor
  · intro hx
    have ha : 0 < q ^ (1 / t) := rpow_pos_of_pos hq _
    obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near
      ((one_le_div ha).2 (by simpa [reboxingAlpha] using hx.1)) hΔ
    have hlo : reboxingAlpha q Δ t j ≤ x := by
      simpa [reboxingAlpha, mul_comm] using (le_div_iff₀ ha).1 hj
    have hhi : x < reboxingAlpha q Δ t (j + 1) := by
      simpa [reboxingAlpha, rpow_add (by linarith : 0 < Δ), pow_succ,
        mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ ha).1 hj'
    have hjr : j < r := by
      by_contra h
      have := hm.monotone (show (r : ℝ) ≤ j by exact_mod_cast (by omega : r ≤ j))
      linarith [hx.2]
    refine ⟨j, ⟨hjr, hlo, hhi⟩, ?_⟩
    rintro n ⟨_, hnlo, hnhi⟩
    have hnj : ¬n < j := by
      intro h
      have := hm.monotone (show (n : ℝ) + 1 ≤ j by exact_mod_cast h)
      linarith
    have hjn : ¬j < n := by
      intro h
      have := hm.monotone (show (j : ℝ) + 1 ≤ n by exact_mod_cast h)
      linarith
    omega
  · rintro ⟨j, ⟨hjr, hlo, hhi⟩, _⟩
    constructor
    · exact (hm.monotone (by positivity : (0 : ℝ) ≤ j)).trans hlo
    · exact hhi.trans_le (hm.monotone
        (show (j : ℝ) + 1 ≤ r by exact_mod_cast hjr))

/-- Exact finite prime-sum partition, keeping arbitrary signed summands. -/
theorem reboxingAlpha_sum_partition {q Δ t : ℝ} (hq : 0 < q) (hΔ : 1 < Δ)
    (N r : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), f p) =
      ∑ j ∈ range r, ∑ p ∈ primeWindow N
        (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)), f p := by
  induction r with
  | zero =>
    have he : primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t 0) = ∅ := by
      ext p
      simp only [mem_primeWindow, Finset.notMem_empty, iff_false]
      rintro ⟨_, _, hlo, hhi⟩
      linarith
    simp [he]
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    let a := reboxingAlpha q Δ t
    have hm := (reboxingAlpha_strictMono (t := t) hq hΔ).monotone
    have he : primeWindow N (a 0) (a (r + 1)) =
        primeWindow N (a 0) (a r) ∪ primeWindow N (a r) (a (r + 1)) := by
      ext p
      simp only [mem_union, mem_primeWindow]
      have h0 := hm (show (0 : ℝ) ≤ r by positivity)
      have h1 := hm (show (r : ℝ) ≤ r + 1 by linarith)
      constructor
      · rintro ⟨hp, hc, hlo, hhi⟩
        by_cases h : (p : ℝ) < a r
        · exact Or.inl ⟨hp, hc, hlo, h⟩
        · exact Or.inr ⟨hp, hc, le_of_not_gt h, hhi⟩
      · rintro (⟨hp, hc, hlo, hhi⟩ | ⟨hp, hc, hlo, hhi⟩)
        · exact ⟨hp, hc, hlo, hhi.trans_le h1⟩
        · exact ⟨hp, hc, h0.trans hlo, hhi⟩
    have hd : Disjoint (primeWindow N (a 0) (a r))
        (primeWindow N (a r) (a (r + 1))) := by
      apply disjoint_left.mpr
      intro p hp hp'
      have h1 := (mem_primeWindow.mp hp).2.2.2
      have h2 := (mem_primeWindow.mp hp').2.2.1
      linarith
    simp only [Nat.cast_add, Nat.cast_one]
    change (∑ p ∈ primeWindow N (a 0) (a (r + 1)), f p) = _
    rw [he, sum_union hd]

/-- Multiplicities of the old convolution are unchanged by the partition. -/
theorem reboxingAlpha_convolution_sum_partition {i : ℕ} {q Δ t : ℝ}
    (hq : 0 < q) (hΔ : 1 < Δ) (N r : ℕ) (W : Fin i → Finset ℕ)
    (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), f d p) =
      ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j)
          (reboxingAlpha q Δ t (j + 1)), f d p := by
  simp_rw [reboxingAlpha_sum_partition hq hΔ, mul_sum]
  exact sum_comm

end Wu2008DoubleSieve
