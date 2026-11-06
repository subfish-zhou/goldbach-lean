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

set_option maxHeartbeats 4000000



