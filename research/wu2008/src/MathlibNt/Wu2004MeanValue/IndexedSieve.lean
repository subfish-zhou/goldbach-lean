import MathlibNt.Wu2004MeanValue.ManuscriptPairs
import MathlibNt.Wu2004MeanValue.RealSieveSupport
import AnalyticNumberTheory.Sieve.GoldbachDensity

/-! The actual indexed sifted counts and their multiplicity-weighted value sieve.
The value zero is allowed: no positivity assumption on pair values is needed. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.Sieve
noncomputable section

def indexedSiftedCount (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (z : ℝ) : ℕ :=
  (T.filter (fun t => (pairValue N t).Coprime (siftingProduct N z))).card

def tailSiftedCount (N : ℕ) (c τ η z : ℝ) : ℕ :=
  indexedSiftedCount N (tailPairs N c τ η) z

def blockSiftedCount (H : ℝ) (N : ℕ) (a η z : ℝ) : ℕ :=
  indexedSiftedCount N (blockPairs H N a η) z

def indexedValueWeight (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (n : ℕ) : ℝ :=
  ((T.filter (fun t => pairValue N t = n)).card : ℝ)

theorem indexedValueWeight_sum (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (f : ℕ → ℝ) :
    (∑ n ∈ T.image (pairValue N), indexedValueWeight N T n * f n) =
      ∑ t ∈ T, f (pairValue N t) := by
  have h := sum_fiberwise_of_maps_to' (s := T)
    (fun t ht => mem_image_of_mem (pairValue N) ht) f
  simpa [indexedValueWeight, sum_const, nsmul_eq_mul] using
    (h : (∑ n ∈ T.image (pairValue N),
      ∑ t ∈ T with pairValue N t = n, f n) = _)

theorem indexedValueWeight_sum_predicate (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ T.image (pairValue N), if P n then indexedValueWeight N T n else 0) =
      ((T.filter (fun t => P (pairValue N t))).card : ℝ) := by
  simpa [mul_ite, ← sum_filter] using
    indexedValueWeight_sum N T (fun n => if P n then 1 else 0)

theorem prime_gt_two_of_dvd_siftingProduct {N p : ℕ} {z : ℝ}
    (hN : Even N) (hp : p.Prime) (hd : p ∣ siftingProduct N z) : 2 < p := by
  have hnot := ((prime_dvd_siftingProduct_iff hp).mp hd).2
  have htwo : 2 ∣ N := even_iff_two_dvd.mp hN
  have hpne : p ≠ 2 := by
    intro heq
    exact hnot (heq ▸ htwo)
  exact lt_of_le_of_ne hp.two_le (Ne.symm hpne)

def indexedBoundingSieve (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (z X : ℝ)
    (hN : Even N) : BoundingSieve where
  support := T.image (pairValue N)
  prodPrimes := siftingProduct N z
  prodPrimes_squarefree := siftingProduct_squarefree N z
  weights := indexedValueWeight N T
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := X
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd =>
    goldbachNu_lt_one_of_prime hp (prime_gt_two_of_dvd_siftingProduct hN hp hd)

theorem indexedBoundingSieve_weight_sum (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) :
    (∑ n ∈ (indexedBoundingSieve N T z X hN).support,
      (indexedBoundingSieve N T z X hN).weights n) = (T.card : ℝ) := by
  simpa [indexedBoundingSieve] using indexedValueWeight_sum N T (fun _ => 1)

theorem indexedBoundingSieve_multSum (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) (d : ℕ) :
    (indexedBoundingSieve N T z X hN).multSum d =
      (indexedDivisibleCount N T d : ℝ) := by
  simpa [BoundingSieve.multSum, indexedBoundingSieve, indexedDivisibleCount] using
    indexedValueWeight_sum_predicate N T (fun n => d ∣ n)

theorem indexedBoundingSieve_siftedSum (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) :
    (indexedBoundingSieve N T z X hN).siftedSum =
      (indexedSiftedCount N T z : ℝ) := by
  simpa [BoundingSieve.siftedSum, indexedBoundingSieve, indexedSiftedCount,
    Nat.coprime_comm] using
    indexedValueWeight_sum_predicate N T (fun n => (siftingProduct N z).Coprime n)

theorem indexedBoundingSieve_rem (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) {d : ℕ} (hd : d ∣ siftingProduct N z) :
    (indexedBoundingSieve N T z X hN).rem d =
      (indexedDivisibleCount N T d : ℝ) - X / d.totient := by
  rw [BoundingSieve.rem, indexedBoundingSieve_multSum]
  change _ - goldbachNu d * X = _
  rw [goldbachNu_squarefree_eq_inv_totient
    ((siftingProduct_squarefree N z).squarefree_of_dvd hd)]
  ring

theorem indexedBoundingSieve_mainSum (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) (w : ℕ → ℝ) :
    (indexedBoundingSieve N T z X hN).mainSum w =
      ∑ d ∈ (siftingProduct N z).divisors, w d / d.totient := by
  apply sum_congr rfl
  intro d hd
  change w d * goldbachNu d = _
  rw [goldbachNu_squarefree_eq_inv_totient
    ((siftingProduct_squarefree N z).squarefree_of_dvd (Nat.mem_divisors.mp hd).1)]
  ring

theorem siftingProduct_primeFactors (N : ℕ) (z : ℝ) :
    (siftingProduct N z).primeFactors = siftingPrimes N z := by
  exact Nat.primeFactors_prod (fun _ hp => (mem_siftingPrimes.mp hp).2.1)

end
end Wu2004MeanValue
