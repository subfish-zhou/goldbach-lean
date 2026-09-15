import MathlibNt.Wu2008DoubleSieve.Omega3R1Layers
import MathlibNt.Wu2004MeanValue.PrimeCenteredDistribution

/-!
# The actual switched residual as two closed prime-count prefixes

Wu (2004), arXiv source lines 2085–2213, equations (5.5)–(5.7):
the interval is `a < p ≤ b`, so its discrepancy is the closed prefix
through `b` minus the closed prefix through `a`. The cofactor support and
coefficient are unchanged between the two prefixes. Absolute values are
taken only after the full cofactor sum.

This is a finite counting identity, not a distribution estimate.
-/

namespace Wu2008DoubleSieve

open Finset Wu2004MeanValue
open scoped Classical

/-- The natural range cap is redundant when the real upper endpoint is at most `N`. -/
theorem mem_omega3ProfilePrimes_of_upper_le {N p : ℕ} {a b : ℝ}
    (hbN : b ≤ N) :
    p ∈ omega3ProfilePrimes N a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  constructor
  · intro hp
    exact (mem_filter.mp hp).2
  · intro hp
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, hp⟩
    have hpN : p ≤ N := by exact_mod_cast hp.2.2.trans hbN
    omega

/-- A positive cofactor cancels from the real product cutoff without changing the residue. -/
theorem mem_scaledPrimeSet_product_iff {q r e p : ℕ} {t : ℝ}
    (he : 0 < e) (ht : 0 ≤ t) :
    p ∈ scaledPrimeSet ((e : ℝ) * t) q r e ↔
      p.Prime ∧ (p : ℝ) ≤ t ∧ Nat.ModEq q (e * p) r := by
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  simp only [scaledPrimeSet, mul_div_cancel_left₀ _ he0, mem_filter, mem_range,
    Nat.lt_succ_iff, Nat.le_floor_iff ht]
  tauto

/-- Subtracting two closed prefixes gives exactly the left-open, right-closed AP fibre. -/
theorem omega3ProfilePrimes_filter_eq_prefix_sdiff {N q e : ℕ} {a b : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    (omega3ProfilePrimes N a b).filter (fun p => Nat.ModEq q (e * p) N) =
      scaledPrimeSet ((e : ℝ) * b) q N e \ scaledPrimeSet ((e : ℝ) * a) q N e := by
  ext p
  simp only [mem_filter, mem_omega3ProfilePrimes_of_upper_le hbN, mem_sdiff,
    mem_scaledPrimeSet_product_iff he ha,
    mem_scaledPrimeSet_product_iff he (ha.trans hab)]
  constructor
  · rintro ⟨⟨hp, hpa, hpb⟩, hcong⟩
    exact ⟨⟨hp, hpb, hcong⟩, fun h => (not_le_of_gt hpa) h.2.1⟩
  · rintro ⟨⟨hp, hpb, hcong⟩, hnot⟩
    exact ⟨⟨hp, lt_of_not_ge (fun hpa => hnot ⟨hp, hpa, hcong⟩), hpb⟩, hcong⟩

theorem omega3ProfilePrimes_filter_card_eq_prefix_sub {N q e : ℕ} {a b : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    (((omega3ProfilePrimes N a b).filter (fun p => Nat.ModEq q (e * p) N)).card : ℝ) =
      (scaledPrimeCount ((e : ℝ) * b) q N e : ℝ) -
        (scaledPrimeCount ((e : ℝ) * a) q N e : ℝ) := by
  have hsub : scaledPrimeSet ((e : ℝ) * a) q N e ⊆
      scaledPrimeSet ((e : ℝ) * b) q N e := by
    intro p hp
    obtain ⟨hp, hpa, hcong⟩ := (mem_scaledPrimeSet_product_iff he ha).mp hp
    exact (mem_scaledPrimeSet_product_iff he (ha.trans hab)).mpr
      ⟨hp, hpa.trans hab, hcong⟩
  rw [omega3ProfilePrimes_filter_eq_prefix_sdiff he ha hab hbN,
    card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  rfl

theorem omega3ProfilePrimes_card_eq_primeCount_sub {N : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    ((omega3ProfilePrimes N a b).card : ℝ) = realPrimeCount b - realPrimeCount a := by
  have h := omega3ProfilePrimes_filter_card_eq_prefix_sub
    (N := N) (q := 1) (e := 1) (by omega) ha hab hbN
  rw [realPrimeCount_eq_scaled, realPrimeCount_eq_scaled]
  simpa [scaledPrimeCount, scaledPrimeSet, Nat.ModEq, Nat.mod_one] using h

/-- No reduced-residue hypothesis is needed for this exact finite identity. -/
theorem omega3ProfileError_eq_prefix_sub {N q e : ℕ} {a b : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    omega3ProfileError N q e a b =
      ((scaledPrimeCount ((e : ℝ) * b) q N e : ℝ) - realPrimeCount b / q.totient) -
        ((scaledPrimeCount ((e : ℝ) * a) q N e : ℝ) - realPrimeCount a / q.totient) := by
  unfold omega3ProfileError
  rw [omega3ProfilePrimes_filter_card_eq_prefix_sub he ha hab hbN,
    omega3ProfilePrimes_card_eq_primeCount_sub ha hab hbN]
  ring

/-- Both prefixes keep the same cofactor support, coefficient, modulus, and residue. -/
theorem sum_omega3ProfileError_eq_primeCenteredAPSum_sub
    (S : Finset ℕ) (f a b : ℕ → ℝ) (N q : ℕ)
    (he : ∀ e ∈ S, 0 < e)
    (ha : ∀ e ∈ S, 0 ≤ a e)
    (hab : ∀ e ∈ S, a e ≤ b e)
    (hbN : ∀ e ∈ S, b e ≤ N) :
    (∑ e ∈ S.filter (fun e => e.Coprime q),
      f e * omega3ProfileError N q e (a e) (b e)) =
      primeCenteredAPSum S f b q N - primeCenteredAPSum S f a q N := by
  simp only [primeCenteredAPSum, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e heS
  by_cases heq : e.Coprime q
  · rw [if_pos heq, if_pos heq, if_pos heq,
      omega3ProfileError_eq_prefix_sub (he e heS) (ha e heS) (hab e heS) (hbN e heS)]
    ring
  · simp only [if_neg heq, sub_self]

/-- The triangle inequality is applied after the entire coprime cofactor sum, not termwise. -/
theorem abs_sum_omega3ProfileError_le_primeCenteredAPSum_add
    (S : Finset ℕ) (f a b : ℕ → ℝ) (N q : ℕ)
    (he : ∀ e ∈ S, 0 < e)
    (ha : ∀ e ∈ S, 0 ≤ a e)
    (hab : ∀ e ∈ S, a e ≤ b e)
    (hbN : ∀ e ∈ S, b e ≤ N) :
    |∑ e ∈ S.filter (fun e => e.Coprime q),
      f e * omega3ProfileError N q e (a e) (b e)| ≤
      |primeCenteredAPSum S f b q N| + |primeCenteredAPSum S f a q N| := by
  rw [sum_omega3ProfileError_eq_primeCenteredAPSum_sub S f a b N q he ha hab hbN]
  simpa only [sub_eq_add_neg, abs_neg] using
    abs_add_le (primeCenteredAPSum S f b q N) (-primeCenteredAPSum S f a q N)

end Wu2008DoubleSieve
