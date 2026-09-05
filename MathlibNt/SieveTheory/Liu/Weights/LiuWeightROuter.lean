import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral

/-!
# Liu's `eqn-r` distribution majorant

This module formalizes the finite distribution majorant displayed in Liu (2022),
`eqn-r`, for an arbitrary main-term model. The source expression is a sum of
termwise absolute inner errors, not the absolute value of a signed outer sum.
The coprime estimate remains an explicit analytic proposition; the non-coprime
endpoint is supplied by the genuine logarithmic-integral development.

No Selberg remainder `R`, Pan Type I/II estimate, or signed-main-term estimate is
asserted here.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

/-! ## Main-parametric inner sums -/

/-- The unrestricted finite inner distribution sum for an arbitrary main-term
model. -/
noncomputable def liuMainFullSum
    (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1), f a * liuScaledAPError main Y a d l

/-- The coprime finite inner distribution sum for an arbitrary main-term model. -/
noncomputable def liuMainCoprimeSum
    (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1),
    if a.Coprime d then f a * liuScaledAPError main Y a d l else 0

/-- Exact finite partition of the unrestricted sum into its coprime and
non-coprime parts. -/
theorem liuMainFullSum_eq_coprime_add_noncoprime
    (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) :
    liuMainFullSum main Y X d l f =
      liuMainCoprimeSum main Y X d l f +
        liuMainNoncoprimeSum main Y X d l f := by
  classical
  unfold liuMainFullSum liuMainCoprimeSum liuMainNoncoprimeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.Coprime d <;> simp [ha]

/-- **Proxy compatibility.** The unrestricted main-parametric sum specializes
to ANT's historical `x / log x` Pan object. This is not a true-`li` claim. -/
theorem liuMainFullSum_proxy
    (Y X d l : ℕ) (f : ℕ → ℝ) :
    liuMainFullSum AnalyticNumberTheory.Sieve.logarithmicIntegral Y X d l f =
      AnalyticNumberTheory.Sieve.panDistributionFullSum Y X d l f := by
  rfl

/-- **Proxy compatibility.** The coprime main-parametric sum specializes to
ANT's historical `x / log x` Pan object. This is not a true-`li` claim. -/
theorem liuMainCoprimeSum_proxy
    (Y X d l : ℕ) (f : ℕ → ℝ) :
    liuMainCoprimeSum AnalyticNumberTheory.Sieve.logarithmicIntegral Y X d l f =
      AnalyticNumberTheory.Sieve.panDistributionSum Y X d l f := by
  rfl

/-! ## Neutral signed weighted sums -/

/-- The full signed weighted sum with the auxiliary cutoff `D₂`. It is a finite
algebraic object and is not Liu's Selberg remainder `R`. -/
noncomputable def liuPaperQSourceFullSignedWeightedSum
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceD2 N),
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainFullSum main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- The coprime signed weighted sum with the auxiliary cutoff `D₂`. -/
noncomputable def liuPaperQSourceCoprimeSignedWeightedSum
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceD2 N),
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainCoprimeSum main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- The non-coprime signed weighted sum with the auxiliary cutoff `D₂`. -/
noncomputable def liuPaperQSourceNoncoprimeSignedWeightedSum
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceD2 N),
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainNoncoprimeSum main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- Exact partition of the neutral signed weighted sum. -/
theorem liuPaperQSourceFullSignedWeightedSum_eq_coprime_add_noncoprime
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) :
    liuPaperQSourceFullSignedWeightedSum main N ε =
      liuPaperQSourceCoprimeSignedWeightedSum main N ε +
        liuPaperQSourceNoncoprimeSignedWeightedSum main N ε := by
  classical
  unfold liuPaperQSourceFullSignedWeightedSum
    liuPaperQSourceCoprimeSignedWeightedSum
    liuPaperQSourceNoncoprimeSignedWeightedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [liuMainFullSum_eq_coprime_add_noncoprime]
  ring

/-- The neutral non-coprime signed weighted sum is bounded by the existing
termwise `R₁` majorant. -/
theorem abs_liuPaperQSourceNoncoprimeSignedWeightedSum_le_majorant
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) :
    |liuPaperQSourceNoncoprimeSignedWeightedSum main N ε| ≤
      liuPaperQSourceR1Majorant main N ε := by
  classical
  unfold liuPaperQSourceNoncoprimeSignedWeightedSum liuPaperQSourceR1Majorant
  calc
    |∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceD2 N),
        (3 : ℝ) ^ d.primeFactors.card *
          liuMainNoncoprimeSum main N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
        ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceD2 N),
          |(3 : ℝ) ^ d.primeFactors.card *
            liuMainNoncoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceD2 N),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainNoncoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by
      apply Finset.sum_congr rfl
      intro d _
      rw [abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (3 : ℝ) ^ d.primeFactors.card)]
    _ ≤ ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceD2 N),
          (3 : ℝ) ^ d.primeFactors.card *
            liuMainNoncoprimeMajorant main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left
        (abs_liuMainNoncoprimeSum_le main N N d (N % d)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
        (by positivity)

/-! ## The source `eqn-r` absolute majorants -/

/-- Liu's source divisor cutoff `⌊N^(1/2-ε)⌋` from `eqn-r`. -/
noncomputable def liuSourceDEpsilon (N : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 - ε : ℝ))

/-- For nonnegative `ε`, the source cutoff `Dε` is no larger than the auxiliary
cutoff `D₂ = ⌊N^(1/2)⌋`. -/
theorem liuSourceDEpsilon_le_liuSourceD2
    (N : ℕ) (ε : ℝ) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    liuSourceDEpsilon N ε ≤ liuSourceD2 N := by
  unfold liuSourceDEpsilon liuSourceD2
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hN
  · linarith

/-- The exact full distribution majorant on the left side of Liu's `eqn-r`:
the weight `3^ω(d)` multiplies the absolute value of each inner full error. -/
noncomputable def liuPaperQSourceFullDistributionMajorant
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceDEpsilon N ε),
    (3 : ℝ) ^ d.primeFactors.card *
      |liuMainFullSum main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|

/-- The corresponding termwise absolute coprime distribution majorant. -/
noncomputable def liuPaperQSourceCoprimeDistributionMajorant
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceDEpsilon N ε),
    (3 : ℝ) ^ d.primeFactors.card *
      |liuMainCoprimeSum main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|

set_option maxHeartbeats 800000 in
/-- Termwise triangle inequality followed by the nonnegative extension from
`Dε` to `D₂` bounds the exact full `eqn-r` distribution majorant by its coprime
part and the established non-coprime majorant. -/
theorem liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    liuPaperQSourceFullDistributionMajorant main N ε ≤
      liuPaperQSourceCoprimeDistributionMajorant main N ε +
        liuPaperQSourceR1Majorant main N ε := by
  classical
  have hD := liuSourceDEpsilon_le_liuSourceD2 N ε hN hε
  have hnoncop :
      (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainNoncoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
        liuPaperQSourceR1Majorant main N ε := by
    unfold liuPaperQSourceR1Majorant
    calc
      (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainNoncoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
          ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
            (fun d => d ≤ liuSourceDEpsilon N ε),
            (3 : ℝ) ^ d.primeFactors.card *
              liuMainNoncoprimeMajorant main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left
          (abs_liuMainNoncoprimeSum_le main N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
          (by positivity)
      _ ≤ ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
            (fun d => d ≤ liuSourceD2 N),
            (3 : ℝ) ^ d.primeFactors.card *
              liuMainNoncoprimeMajorant main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_filter] at hd ⊢
          exact ⟨hd.1, hd.2.trans hD⟩
        · intro d _ _
          exact mul_nonneg (by positivity)
            ((abs_nonneg _).trans
              (abs_liuMainNoncoprimeSum_le main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))))
  unfold liuPaperQSourceFullDistributionMajorant
    liuPaperQSourceCoprimeDistributionMajorant
  calc
    (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceDEpsilon N ε),
        (3 : ℝ) ^ d.primeFactors.card *
          |liuMainFullSum main N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
        ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            (|liuMainCoprimeSum main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| +
              |liuMainNoncoprimeSum main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) := by
      apply Finset.sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left
      · rw [liuMainFullSum_eq_coprime_add_noncoprime]
        exact abs_add_le _ _
      · positivity
    _ = (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainCoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) +
        ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainNoncoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainCoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) +
        liuPaperQSourceR1Majorant main N ε :=
      add_le_add_right hnoncop _

/-! ## Conditional coprime input and genuine-integral endpoint -/

/-- The remaining coprime Pan estimate for Liu's exact `eqn-r` absolute
majorant. This proposition transparently contains the inverse-log inequality
used by the outer bound. -/
def LiuPaperQCoprimeRBound
    (main : ℝ → ℝ) (N : ℕ) (ε A C : ℝ) : Prop :=
  liuPaperQSourceCoprimeDistributionMajorant main N ε ≤
    C * N / Real.log N ^ A

/-- Liu's exact `eqn-r` distribution majorant for the genuine normalized
logarithmic integral, conditional only on the explicitly retained coprime
inverse-log estimate. The `N^(9/10) log(N)^2` term is not absorbed. -/
theorem liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le
    (κ : ℝ) (N : ℕ) (ε A Cpan : ℝ) (hN : 8 ≤ N) (hε : 0 ≤ ε)
    (hpan : LiuPaperQCoprimeRBound
      (liuLogarithmicIntegral κ) N ε A Cpan) :
    liuPaperQSourceFullDistributionMajorant
        (liuLogarithmicIntegral κ) N ε ≤
      Cpan * N / Real.log N ^ A +
        15 * liuLogarithmicIntegralUpperConstant κ *
          liuSourceR1P₂ReciprocalBound *
          paperQStyleDivisorWeightLogConstant *
          (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  exact (liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1
    (liuLogarithmicIntegral κ) N ε (by omega) hε).trans
      (add_le_add hpan
        (liuLogarithmicIntegral_liuPaperQSourceR1Majorant_le_log_square
          κ N ε hN hε))

end MathlibNt.SieveTheory.LiuWeight
