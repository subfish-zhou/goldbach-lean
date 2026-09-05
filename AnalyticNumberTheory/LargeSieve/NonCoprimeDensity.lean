import AnalyticNumberTheory.LargeSieve.PanTypeIAssembly
import AnalyticNumberTheory.Sieve.PanV1SquareMean

/-! # AnalyticNumberTheory.LargeSieve.NonCoprimeDensity

## Divisor estimates for the non-coprime density term

The non-coprime density term is
`D_q(m) = Σ_{n ≤ m, (n,q) > 1} |vaughanFirst(n,u)|`.
The intended polylogarithmic estimate has the shape
`D_q(m) ≤ C·m·log³(m+2)·(log(q+2)+1)`.

The density argument proceeds as follows:
(i) `panTypeI_nonCoprimeDensity_le_primePartition` reduces `D_q` to prime
divisors of `q`.
(ii) For each prime `p`,
`Σ_{p|n ≤ m}|vf(n)| = Σ_{k ≤ m/p}|vf(pk)| ≤ Σ τ(pk)·log(pk+1)`
by `vaughanFirst_abs_le`, and this is at most
`2·Σ τ(k)·(log(k+1)+log(p+1))` since `τ(pk) ≤ 2τ(k)`.
Cauchy--Schwarz and `divisorCountSq_sum_le` supply the corresponding
`C·(m/p)·(1+log(m+2))³` estimate in the relevant range.
(iii) Sum over prime divisors using
`Σ_{p|q} 1/p ≤ primeReciprocalSum q ≤ C·(log log q + 1)`
from `mertensSecond_nat`.

This module supplies divisor and reindexing components for controlling the
non-coprime part by a density estimate; it does not state the complete
bound on `D_q(m)`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-- `τ(p·k) ≤ 2·τ(k)` for prime `p`: a divisor of `pk` either divides
`k` or is `p` times a divisor of `k`. -/
lemma prime_mul_divisors_card_le {p k : ℕ} (hp : p.Prime) :
    (p * k).divisors.card ≤ 2 * k.divisors.card := by
  have hp0 : 0 < p := hp.pos
  have hsub : (p * k).divisors ⊆ k.divisors ∪ (Finset.image (fun d : ℕ => p * d) k.divisors) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    rcases hd with ⟨hdvd, hpk0⟩
    by_cases hpd : p ∣ d
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_image]
      rcases hpd with ⟨c, hc⟩
      refine ⟨c, ?_, ?_⟩
      · rw [Nat.mem_divisors]
        constructor
        · rw [hc] at hdvd
          exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
        · have hk0 : k ≠ 0 := by
            intro hk0
            apply hpk0
            rw [hk0]
            exact mul_zero p
          exact hk0
      · rw [hc]
    · rw [Finset.mem_union]
      left
      rw [Nat.mem_divisors]
      constructor
      · have hcp : d.Coprime p := (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).2 hpd))
        exact hcp.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdvd)
      · exact (by
          intro hk0
          apply hpk0
          rw [hk0]
          exact mul_zero p)
  have hcard1 : (k.divisors ∪ Finset.image (fun d : ℕ => p * d) k.divisors).card ≤
      k.divisors.card + (Finset.image (fun d : ℕ => p * d) k.divisors).card := by
    exact Finset.card_union_le _ _
  have hcard2 : (Finset.image (fun d : ℕ => p * d) k.divisors).card ≤ k.divisors.card := by
    exact Finset.card_image_le
  calc
    (p * k).divisors.card ≤ (k.divisors ∪ Finset.image (fun d : ℕ => p * d) k.divisors).card := by
          exact Finset.card_le_card hsub
    _ ≤ k.divisors.card + (Finset.image (fun d : ℕ => p * d) k.divisors).card := hcard1
    _ ≤ k.divisors.card + k.divisors.card := by
          omega
    _ = 2 * k.divisors.card := by ring

/-- log(p·k+1) ≤ log(k+1) + log(p+1). -/
lemma log_mul_plus_one_le {p k : ℕ} :
    Real.log ((p * k + 1 : ℕ) : ℝ) ≤ Real.log (k + 1) + Real.log (p + 1) := by
  have hle : ((p * k + 1 : ℕ) : ℝ) ≤ (((k + 1) * (p + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : p * k + 1 ≤ (k + 1) * (p + 1))
  have hpos1 : 0 < ((p * k + 1 : ℕ) : ℝ) := by positivity
  have hpos2 : 0 < (((k + 1) * (p + 1) : ℕ) : ℝ) := by positivity
  calc
    Real.log ((p * k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℝ) * (p + 1 : ℝ)) := by
          have hle' : ((p * k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℝ) * (p + 1 : ℝ)) := by
            simpa [Nat.cast_add, Nat.cast_mul] using hle
          exact Real.log_le_log hpos1 hle'
    _ = Real.log (k + 1) + Real.log (p + 1) := by
          exact Real.log_mul (ne_of_gt (by positivity : 0 < (k + 1 : ℝ)))
            (ne_of_gt (by positivity : 0 < (p + 1 : ℝ)))

/-- Reindexing: `Σ_{p|n ≤ m} f(n) = Σ_{k ≤ m/p} f(p·k)`. -/
lemma sum_multiples_eq_sum_range {p m : ℕ} (hp0 : 0 < p) (f : ℕ → ℝ) :
    (∑ n ∈ (Finset.range (m + 1)).filter (fun n => p ∣ n), f n) =
      ∑ k ∈ Finset.range (m / p + 1), f (p * k) := by
  have himg : (Finset.range (m + 1)).filter (fun n => p ∣ n) =
      (Finset.range (m / p + 1)).image (fun k => p * k) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      rcases h with ⟨hn, hpd⟩
      rcases hpd with ⟨c, hc⟩
      refine ⟨c, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hcm : p * c ≤ m := by
          rw [← hc]
          exact Nat.le_of_lt_succ hn
        have : c ≤ m / p := (Nat.le_div_iff_mul_le hp0).2 (by simpa [mul_comm] using hcm)
        omega
      · exact hc.symm
    · intro h
      rcases h with ⟨k, hk, hpk⟩
      rw [Finset.mem_range] at hk
      constructor
      · have hpk2 : p * k ≤ m := by
          have : k ≤ m / p := Nat.le_of_lt_succ hk
          exact (by simpa [mul_comm] using (Nat.le_div_iff_mul_le hp0).1 this)
        omega
      · exact ⟨k, hpk.symm⟩
  rw [himg]
  have hinj : Set.InjOn (fun k : ℕ => p * k) ↑(Finset.range (m / p + 1)) := by
    intro a ha b hb h
    exact (Nat.mul_left_cancel hp0 h)
  rw [Finset.sum_image hinj]
