import MathlibNt.Wu2008DoubleSieve.Omega3R1Prefix

#check Wu2008DoubleSieve.mem_omega3ProfilePrimes_of_upper_le
#print axioms Wu2008DoubleSieve.mem_omega3ProfilePrimes_of_upper_le
#check Wu2008DoubleSieve.mem_scaledPrimeSet_product_iff
#print axioms Wu2008DoubleSieve.mem_scaledPrimeSet_product_iff
#check Wu2008DoubleSieve.omega3ProfilePrimes_filter_eq_prefix_sdiff
#print axioms Wu2008DoubleSieve.omega3ProfilePrimes_filter_eq_prefix_sdiff
#check Wu2008DoubleSieve.omega3ProfilePrimes_filter_card_eq_prefix_sub
#print axioms Wu2008DoubleSieve.omega3ProfilePrimes_filter_card_eq_prefix_sub
#check Wu2008DoubleSieve.omega3ProfilePrimes_card_eq_primeCount_sub
#print axioms Wu2008DoubleSieve.omega3ProfilePrimes_card_eq_primeCount_sub
#check Wu2008DoubleSieve.omega3ProfileError_eq_prefix_sub
#print axioms Wu2008DoubleSieve.omega3ProfileError_eq_prefix_sub
#check Wu2008DoubleSieve.sum_omega3ProfileError_eq_primeCenteredAPSum_sub
#print axioms Wu2008DoubleSieve.sum_omega3ProfileError_eq_primeCenteredAPSum_sub
#check Wu2008DoubleSieve.abs_sum_omega3ProfileError_le_primeCenteredAPSum_add
#print axioms Wu2008DoubleSieve.abs_sum_omega3ProfileError_le_primeCenteredAPSum_add

open Finset Wu2008DoubleSieve Wu2004MeanValue
open scoped Classical

example : 2 ∈ omega3ProfilePrimes 2 0 2 := by
  rw [mem_omega3ProfilePrimes_of_upper_le (by norm_num)]
  norm_num

example : 2 ∉ omega3ProfilePrimes 2 2 2 := by
  rw [mem_omega3ProfilePrimes_of_upper_le (by norm_num)]
  norm_num

example : 2 ∈ omega3ProfilePrimes 3 0 (5 / 2) := by
  rw [mem_omega3ProfilePrimes_of_upper_le (by norm_num)]
  norm_num

example : 3 ∉ omega3ProfilePrimes 3 0 (5 / 2) := by
  rw [mem_omega3ProfilePrimes_of_upper_le (by norm_num)]
  norm_num

example (N q e : ℕ) (a : ℝ) (he : 0 < e) (ha : 0 ≤ a) (haN : a ≤ N) :
    omega3ProfileError N q e a a = 0 := by
  rw [omega3ProfileError_eq_prefix_sub he ha le_rfl haN, sub_self]

example (S : Finset ℕ) (f a b : ℕ → ℝ) (N : ℕ)
    (he : ∀ e ∈ S, 0 < e) (ha : ∀ e ∈ S, 0 ≤ a e)
    (hab : ∀ e ∈ S, a e ≤ b e) (hbN : ∀ e ∈ S, b e ≤ N) :
    (∑ e ∈ S.filter (fun e => e.Coprime 1),
      f e * omega3ProfileError N 1 e (a e) (b e)) =
      primeCenteredAPSum S f b 1 N - primeCenteredAPSum S f a 1 N :=
  sum_omega3ProfileError_eq_primeCenteredAPSum_sub S f a b N 1 he ha hab hbN

example (S : Finset ℕ) (f : ℕ → ℝ) (q : ℕ) (he : ∀ e ∈ S, 0 < e) :
    (∑ e ∈ S.filter (fun e => e.Coprime q),
      f e * omega3ProfileError 0 q e 0 0) =
      primeCenteredAPSum S f (fun _ => 0) q 0 -
        primeCenteredAPSum S f (fun _ => 0) q 0 :=
  sum_omega3ProfileError_eq_primeCenteredAPSum_sub S f (fun _ => 0) (fun _ => 0) 0 q
    he (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => by norm_num)
