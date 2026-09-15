import MathlibNt.Wu2008DoubleSieve.Omega3Labels

/-! # Finite quotient fibres, before and after strengthening -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- The original source carrier in the positive quotient variable. -/
noncomputable def omega3QuotientFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun n =>
    0 < n ∧ omega3Cofactor d p1 p2 n * p3 ≤ N ∧
    (N - omega3Cofactor d p1 p2 n * p3).Prime ∧
    Sifted (d * p1 * N) (omega3Cofactor d p1 p2 n * p3) (p2 : ℝ)

/-- B' retains the original d,p1,p2,p3 labels. No primality condition is
imposed on its output, and each quotient contributes with its fibre weight. -/
noncomputable def omega3SwitchedFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun n =>
    0 < n ∧ omega3Cofactor d p1 p2 n * p3 ≤ N ∧
    Omega3Strengthened N d p1 p2 n

theorem omega3_quotient_mem {N d p1 p2 p3 ell : ℕ}
    (hN : 4 ≤ N) (heven : Even N)
    (hell : ell ∈ sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)) :
    omega3Quotient N d p1 p2 p3 ell ∈ omega3QuotientFibre N d p1 p2 p3 := by
  obtain ⟨hbound, hp, hdiv, hs⟩ := mem_filter.mp hell
  have hlt := omega3_prime_output_lt hN heven hp (by simpa using mem_range.mp hbound)
  obtain ⟨hn, heq, hout, hsize⟩ := omega3_quotient_equation hlt hdiv
  refine mem_filter.mpr ⟨mem_range.mpr ?_, hn, hsize, hout ▸ hp, ?_⟩
  · have := (Nat.div_le_self (N - ell) (d * p1 * p2 * p3)).trans (Nat.sub_le N ell)
    exact Nat.lt_succ_of_le this
  · rwa [heq]

theorem omega3_quotient_inverse {N d p1 p2 p3 n : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3)
    (hsize : omega3Cofactor d p1 p2 n * p3 ≤ N) :
    omega3Quotient N d p1 p2 p3 (N - omega3Cofactor d p1 p2 n * p3) = n := by
  unfold omega3Quotient
  rw [Nat.sub_sub_self hsize]
  have he : omega3Cofactor d p1 p2 n * p3 = (d * p1 * p2 * p3) * n := by
    unfold omega3Cofactor
    ring
  rw [he, Nat.mul_div_cancel_left _ (by positivity)]

theorem omega3_output_mem {N d p1 p2 p3 n : ℕ}
    (hn : n ∈ omega3QuotientFibre N d p1 p2 p3) :
    N - omega3Cofactor d p1 p2 n * p3 ∈
      sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ) := by
  obtain ⟨_, _, hsize, hp, hs⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), hp, ?_, ?_⟩
  · rw [Nat.sub_sub_self hsize]
    exact ⟨n, by unfold omega3Cofactor; ring⟩
  · rwa [Nat.sub_sub_self hsize]

/-- Exact change of variables for any test function of both the output and
the quotient. In particular, divisibility tests preserve all multiplicities. -/
theorem omega3_fibre_sum_identity {A : Type*} [AddCommMonoid A]
    {N d p1 p2 p3 : ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3)
    (f : ℕ → ℕ → A) :
    (∑ ell ∈ sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ),
      f ell (omega3Quotient N d p1 p2 p3 ell)) =
    ∑ n ∈ omega3QuotientFibre N d p1 p2 p3,
      f (N - omega3Cofactor d p1 p2 n * p3) n := by
  apply sum_bij (fun ell _ => omega3Quotient N d p1 p2 p3 ell)
  · exact fun _ h => omega3_quotient_mem hN heven h
  · intro a ha b hb hab
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hla := omega3_prime_output_lt hN heven ha'.2.1 (by
      simpa using mem_range.mp ha'.1)
    have hlb := omega3_prime_output_lt hN heven hb'.2.1 (by
      simpa using mem_range.mp hb'.1)
    have ea := (omega3_quotient_equation hla ha'.2.2.1).2.2.1
    have eb := (omega3_quotient_equation hlb hb'.2.2.1).2.2.1
    rw [ea, eb, hab]
  · intro n hn
    exact ⟨N - omega3Cofactor d p1 p2 n * p3, omega3_output_mem hn,
      omega3_quotient_inverse hd h1 h2 h3 (mem_filter.mp hn).2.2.1⟩
  · intro ell hell
    obtain ⟨hb, hp, hdiv, _⟩ := mem_filter.mp hell
    have hl := omega3_prime_output_lt hN heven hp (by simpa using mem_range.mp hb)
    rw [← (omega3_quotient_equation hl hdiv).2.2.1]

end Wu2008DoubleSieve
