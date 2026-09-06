import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPanSigned
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanWangDingSource

/-!
# Liu's lambda-pair Selberg remainder

This module represents the actual signed double sum in Liu's `eqn-r`.  Its
lambda coefficients are supported on divisors of the paper modulus at the
paper's `N^(1/4-epsilon/2)` cutoff.  Grouping pairs by their least common
multiple bounds the signed remainder by the already verified
`3^omega(d)` full-distribution majorant.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-- The support and size conditions on Liu's Selberg coefficients needed for
the remainder bound.  No normalization at `d = 1` is needed. -/
def LiuSelbergLambdaAdmissible
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : Prop :=
  (∀ d, lambda d ≠ 0 →
    d ∣ liuPaperQModulus N epsilon ∧ d ≤ paperQSourceCutoff N epsilon) ∧
  ∀ d, |lambda d| ≤ 1

/-- The finite source carrier forced by admissibility. -/
noncomputable def liuSelbergLambdaSourceCarrier
    (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  (liuPaperQModulus N epsilon).divisors.filter
    (fun d => d ≤ paperQSourceCutoff N epsilon)

theorem liuPaperQModulus_squarefree (N : ℕ) (epsilon : ℝ) :
    Squarefree (liuPaperQModulus N epsilon) := by
  rw [liuPaperQModulus_eq_paperQStyleModulus]
  exact paperQStyleModulus_squarefree N (paperQSourceCutoff N epsilon)

theorem mem_liuSelbergLambdaSourceCarrier {N d : ℕ} {epsilon : ℝ} :
    d ∈ liuSelbergLambdaSourceCarrier N epsilon ↔
      d ∣ liuPaperQModulus N epsilon ∧
        d ≤ paperQSourceCutoff N epsilon := by
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  simp [liuSelbergLambdaSourceCarrier, Nat.mem_divisors, hQ0]

theorem LiuSelbergLambdaAdmissible.support_dvd
    {N d : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hd : lambda d ≠ 0) :
    d ∣ liuPaperQModulus N epsilon :=
  (hlambda.1 d hd).1

theorem LiuSelbergLambdaAdmissible.support_le
    {N d : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hd : lambda d ≠ 0) :
    d ≤ paperQSourceCutoff N epsilon :=
  (hlambda.1 d hd).2

theorem LiuSelbergLambdaAdmissible.abs_le_one
    {N : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda) (d : ℕ) :
    |lambda d| ≤ 1 :=
  hlambda.2 d

/-- Admissibility proves that the finite carrier loses no nonzero coefficient. -/
theorem LiuSelbergLambdaAdmissible.eq_zero_of_not_mem_sourceCarrier
    {N d : ℕ} {epsilon : ℝ} {lambda : ℕ → ℝ}
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hd : d ∉ liuSelbergLambdaSourceCarrier N epsilon) :
    lambda d = 0 := by
  by_contra hne
  exact hd (mem_liuSelbergLambdaSourceCarrier.mpr (hlambda.1 d hne))

/-- Liu's Selberg expression after expanding the square and interchanging the
finite sums.  The inner term is the actual weighted prime count in the
progression `a * p ≡ N (mod lcm d₁ d₂)`. -/
noncomputable def liuSelbergSwitchedCount
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
    ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
      lambda d1 * lambda d2 *
        ∑ a ∈ range (N + 1),
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            (AnalyticNumberTheory.Sieve.primesInAPBelow
              N a (Nat.lcm d1 d2) (N % Nat.lcm d1 d2) : ℝ)

/-- The main term paired with `liuSelbergSwitchedCount` for an arbitrary
main-term model. -/
noncomputable def liuSelbergMainTerm
    (main : ℝ → ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
    ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
      lambda d1 * lambda d2 *
        ((1 : ℝ) / Nat.totient (Nat.lcm d1 d2) *
          ∑ a ∈ range (N + 1),
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              main ((N : ℝ) / a))

/-- The actual lambda-pair Selberg remainder from Liu's `eqn-r`, represented on
the finite carrier justified by `LiuSelbergLambdaAdmissible`. -/
noncomputable def liuSelbergRemainder
    (main : ℝ → ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
    ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
      lambda d1 * lambda d2 *
        liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- Exact finite decomposition of the switched Selberg count into its chosen
main term and the actual signed remainder. -/
theorem liuSelbergSwitchedCount_eq_mainTerm_add_remainder
    (main : ℝ → ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergSwitchedCount N epsilon lambda =
      liuSelbergMainTerm main N epsilon lambda +
        liuSelbergRemainder main N epsilon lambda := by
  classical
  unfold liuSelbergSwitchedCount liuSelbergMainTerm liuSelbergRemainder
    liuMainFullSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d2 _
  rw [← mul_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold liuScaledAPError
  ring

/-- Source-facing specialization of the exact decomposition to Liu's genuine
normalized logarithmic-integral family. -/
theorem liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder
    (kappa : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergSwitchedCount N epsilon lambda =
      liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda +
        liuSelbergRemainder (liuLogarithmicIntegral kappa) N epsilon lambda :=
  liuSelbergSwitchedCount_eq_mainTerm_add_remainder
    (liuLogarithmicIntegral kappa) N epsilon lambda

/-- Liu's original finite Selberg expression before expanding the square. -/
noncomputable def liuSelbergSquareCount
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (N + 1),
    liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
      ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ a * p ≤ N),
        (∑ d ∈ (liuSelbergLambdaSourceCarrier N epsilon).filter
            (fun d => d ∣ N - a * p), lambda d) ^ 2

/-- At the canonical residue, the AP convention on `a * p` is exactly
divisibility of the natural-number complement. -/
theorem primesInAPBelow_mod_eq_card_dvd_complement
    (N a q : ℕ) :
    (AnalyticNumberTheory.Sieve.primesInAPBelow N a q (N % q) : ℝ) =
      ((((range (N + 1)).filter (fun p => p.Prime ∧ a * p ≤ N)).filter
        (fun p => q ∣ N - a * p)).card : ℝ) := by
  congr 1
  unfold AnalyticNumberTheory.Sieve.primesInAPBelow
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hpN, hpprime, hapN, hcong⟩
    refine ⟨⟨hpN, hpprime, hapN⟩, ?_⟩
    apply (Nat.modEq_iff_dvd' hapN).mp
    simpa [Nat.ModEq] using hcong
  · rintro ⟨⟨hpN, hpprime, hapN⟩, hdvd⟩
    refine ⟨hpN, hpprime, hapN, ?_⟩
    have hcong := (Nat.modEq_iff_dvd' hapN).mpr hdvd
    simpa [Nat.ModEq] using hcong

private theorem liuSelberg_four_sum_interchange
    (A D : Finset ℕ) (P : ℕ → Finset ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ a ∈ A, ∑ p ∈ P a, ∑ d1 ∈ D, ∑ d2 ∈ D, F a p d1 d2) =
      ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ a ∈ A, ∑ p ∈ P a, F a p d1 d2 := by
  calc
    _ = ∑ a ∈ A, ∑ d1 ∈ D, ∑ p ∈ P a, ∑ d2 ∈ D,
          F a p d1 d2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a ∈ A, ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ p ∈ P a,
          F a p d1 d2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d1 _
      exact Finset.sum_comm
    _ = ∑ d1 ∈ D, ∑ a ∈ A, ∑ d2 ∈ D, ∑ p ∈ P a,
          F a p d1 d2 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d1 _
      exact Finset.sum_comm

/-- Finite square expansion and interchange: Liu's original squared-divisor
expression equals the switched lambda-pair AP count. -/
theorem liuSelbergSquareCount_eq_switchedCount
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergSquareCount N epsilon lambda =
      liuSelbergSwitchedCount N epsilon lambda := by
  classical
  let A := range (N + 1)
  let D := liuSelbergLambdaSourceCarrier N epsilon
  let P : ℕ → Finset ℕ :=
    fun a => (range (N + 1)).filter (fun p => p.Prime ∧ a * p ≤ N)
  unfold liuSelbergSquareCount liuSelbergSwitchedCount
  change
    (∑ a ∈ A, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
      ∑ p ∈ P a, (∑ d ∈ D.filter (fun d => d ∣ N - a * p), lambda d) ^ 2) =
      ∑ d1 ∈ D, ∑ d2 ∈ D, lambda d1 * lambda d2 *
        ∑ a ∈ A, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          (AnalyticNumberTheory.Sieve.primesInAPBelow
            N a (Nat.lcm d1 d2) (N % Nat.lcm d1 d2) : ℝ)
  simp_rw [pow_two, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [liuSelberg_four_sum_interchange]
  apply Finset.sum_congr rfl
  intro d1 _
  apply Finset.sum_congr rfl
  intro d2 _
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ p ∈ P a,
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          ((if d1 ∣ N - a * p then lambda d1 else 0) *
            if d2 ∣ N - a * p then lambda d2 else 0)) =
        ∑ p ∈ (P a).filter
            (fun p => d1 ∣ N - a * p ∧ d2 ∣ N - a * p),
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            lambda d1 * lambda d2 := by
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hd1 : d1 ∣ N - a * p <;>
        by_cases hd2 : d2 ∣ N - a * p <;> simp [hd1, hd2, mul_assoc]
    _ = lambda d1 * lambda d2 *
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
            (AnalyticNumberTheory.Sieve.primesInAPBelow
              N a (Nat.lcm d1 d2) (N % Nat.lcm d1 d2) : ℝ)) := by
      rw [primesInAPBelow_mod_eq_card_dvd_complement]
      have hfilters :
          (P a).filter (fun p => d1 ∣ N - a * p ∧ d2 ∣ N - a * p) =
            (P a).filter (fun p => Nat.lcm d1 d2 ∣ N - a * p) := by
        ext p
        simp [Nat.lcm_dvd_iff]
      rw [← hfilters]
      simp
      ring

/-- Source-facing exact decomposition of Liu's original squared-divisor
expression. -/
theorem liuSelbergSquareCount_eq_logarithmicIntegralMainTerm_add_remainder
    (kappa : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergSquareCount N epsilon lambda =
      liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda +
        liuSelbergRemainder (liuLogarithmicIntegral kappa) N epsilon lambda := by
  rw [liuSelbergSquareCount_eq_switchedCount]
  exact
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder
      kappa N epsilon lambda

/-- The unproved numerical main-term estimate printed in Liu's source.  This is
a transparent proposition, not an asserted analytic theorem. -/
def LiuSelbergMainTermUpperBound
    (kappa : ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) : Prop :=
  liuSelbergMainTerm (liuLogarithmicIntegral kappa) N epsilon lambda ≤
    3.94033 *
      MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
      (N : ℝ) / Real.log N ^ 2

/-- Supported pairs have lcm dividing the squarefree paper modulus; in
particular the lcm itself is squarefree. -/
theorem liuSelberg_lcm_dvd_modulus_and_squarefree
    {N d1 d2 : ℕ} {epsilon : ℝ}
    (hd1 : d1 ∈ liuSelbergLambdaSourceCarrier N epsilon)
    (hd2 : d2 ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    Nat.lcm d1 d2 ∣ liuPaperQModulus N epsilon ∧
      Squarefree (Nat.lcm d1 d2) := by
  have h1 := (mem_liuSelbergLambdaSourceCarrier.mp hd1).1
  have h2 := (mem_liuSelbergLambdaSourceCarrier.mp hd2).1
  have hlcm : Nat.lcm d1 d2 ∣ liuPaperQModulus N epsilon :=
    Nat.lcm_dvd h1 h2
  exact ⟨hlcm,
    (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd hlcm⟩

/-- The elementary lcm-product inequality used in the source cutoff. -/
theorem liuSelberg_lcm_le_mul {d1 d2 : ℕ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) :
    Nat.lcm d1 d2 ≤ d1 * d2 :=
  Nat.le_of_dvd (Nat.mul_pos hd1 hd2) (lcm_dvd_mul d1 d2)

/-- Multiplying two source-cutoff divisors doubles the exponent exactly. -/
theorem paperQSourceCutoff_mul_le_liuSourceDEpsilon
    (N d1 d2 : ℕ) (epsilon : ℝ) (hN : 1 ≤ N)
    (hd1 : d1 ≤ paperQSourceCutoff N epsilon)
    (hd2 : d2 ≤ paperQSourceCutoff N epsilon) :
    d1 * d2 ≤ liuSourceDEpsilon N epsilon := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpow : 0 ≤ (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hNpos) _
  have hd1real :
      (d1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) := by
    exact (by exact_mod_cast hd1 : (d1 : ℝ) ≤
      (paperQSourceCutoff N epsilon : ℝ)).trans
        (Nat.floor_le hpow)
  have hd2real :
      (d2 : ℝ) ≤ (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) := by
    exact (by exact_mod_cast hd2 : (d2 : ℝ) ≤
      (paperQSourceCutoff N epsilon : ℝ)).trans
        (Nat.floor_le hpow)
  apply (Nat.le_floor_iff
    (Real.rpow_nonneg (le_of_lt hNpos) (1 / 2 - epsilon : ℝ))).mpr
  calc
    ((d1 * d2 : ℕ) : ℝ) = (d1 : ℝ) * (d2 : ℝ) := by norm_num
    _ ≤ (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) *
        (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) :=
      mul_le_mul hd1real hd2real (Nat.cast_nonneg d2) hpow
    _ = (N : ℝ) ^ ((1 / 4 - epsilon / 2 : ℝ) +
        (1 / 4 - epsilon / 2 : ℝ)) :=
      (Real.rpow_add hNpos _ _).symm
    _ = (N : ℝ) ^ (1 / 2 - epsilon : ℝ) := by ring_nf

/-- Every pair in the source carrier has lcm inside Liu's `eqn-r` divisor
cutoff.  This records both `lcm ≤ d1*d2` and the doubled-exponent estimate. -/
theorem liuSelberg_lcm_le_sourceDEpsilon_of_mem_sourceCarrier
    {N d1 d2 : ℕ} {epsilon : ℝ} (hN : 1 ≤ N)
    (hd1 : d1 ∈ liuSelbergLambdaSourceCarrier N epsilon)
    (hd2 : d2 ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    Nat.lcm d1 d2 ≤ liuSourceDEpsilon N epsilon := by
  have hQpos : 0 < liuPaperQModulus N epsilon :=
    Nat.pos_of_ne_zero (liuPaperQModulus_squarefree N epsilon).ne_zero
  have h1 := mem_liuSelbergLambdaSourceCarrier.mp hd1
  have h2 := mem_liuSelbergLambdaSourceCarrier.mp hd2
  exact (liuSelberg_lcm_le_mul
      (Nat.pos_of_dvd_of_pos h1.1 hQpos)
      (Nat.pos_of_dvd_of_pos h2.1 hQpos)).trans
    (paperQSourceCutoff_mul_le_liuSourceDEpsilon
      N d1 d2 epsilon hN h1.2 h2.2)

set_option maxHeartbeats 800000 in
/-- The actual signed lambda-pair remainder is bounded by Liu's exact
`3^omega(d)` full-distribution majorant. -/
theorem abs_liuSelbergRemainder_le_fullDistributionMajorant
    (main : ℝ → ℝ) (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ)
    (hN : 1 ≤ N)
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda) :
    |liuSelbergRemainder main N epsilon lambda| ≤
      liuPaperQSourceFullDistributionMajorant main N epsilon := by
  classical
  have hQsq := liuPaperQModulus_squarefree N epsilon
  have hsubset :
      liuSelbergLambdaSourceCarrier N epsilon ⊆
        (liuPaperQModulus N epsilon).divisors := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  unfold liuSelbergRemainder
  calc
    |∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
        ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
          lambda d1 * lambda d2 *
            liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
        ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
          |∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
            lambda d1 * lambda d2 *
              liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
          ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
            |lambda d1 * lambda d2 *
              liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by
      apply Finset.sum_le_sum
      intro d1 hd1
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
          ∑ d2 ∈ liuSelbergLambdaSourceCarrier N epsilon,
            if Nat.lcm d1 d2 ≤ liuSourceDEpsilon N epsilon then
              |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|
            else 0 := by
      apply Finset.sum_le_sum
      intro d1 hd1
      apply Finset.sum_le_sum
      intro d2 hd2
      rw [if_pos (liuSelberg_lcm_le_sourceDEpsilon_of_mem_sourceCarrier
        hN hd1 hd2)]
      simp only [abs_mul]
      calc
        |lambda d1| * |lambda d2| *
            |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
            1 * 1 *
              |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by
          gcongr
          · exact hlambda.abs_le_one d1
          · exact hlambda.abs_le_one d2
        _ = |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| := by ring
    _ ≤ ∑ d1 ∈ liuSelbergLambdaSourceCarrier N epsilon,
          ∑ d2 ∈ (liuPaperQModulus N epsilon).divisors,
            if Nat.lcm d1 d2 ≤ liuSourceDEpsilon N epsilon then
              |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|
            else 0 := by
      apply Finset.sum_le_sum
      intro d1 hd1
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d2 hd2 hd2not
      split <;> positivity
    _ ≤ ∑ d1 ∈ (liuPaperQModulus N epsilon).divisors,
          ∑ d2 ∈ (liuPaperQModulus N epsilon).divisors,
            if Nat.lcm d1 d2 ≤ liuSourceDEpsilon N epsilon then
              |liuMainFullSum main N N (Nat.lcm d1 d2) (N % Nat.lcm d1 d2)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|
            else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d1 hd1 hd1not
      apply Finset.sum_nonneg
      intro d2 hd2
      split <;> positivity
    _ = ∑ d ∈ (liuPaperQModulus N epsilon).divisors,
          (3 : ℝ) ^ d.primeFactors.card *
            (if d ≤ liuSourceDEpsilon N epsilon then
              |liuMainFullSum main N N d (N % d)
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|
            else 0) := by
      symm
      exact AnalyticNumberTheory.Sieve.lcmPairWeightedSum
        (liuPaperQModulus N epsilon) hQsq _
    _ = liuPaperQSourceFullDistributionMajorant main N epsilon := by
      unfold liuPaperQSourceFullDistributionMajorant
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcut : d ≤ liuSourceDEpsilon N epsilon
      · simp [hcut]
      · simp [hcut]

/-- The canonical coprime consumer interface bounds the actual signed Selberg
remainder for every eventually admissible coefficient family. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_abs_liuSelbergRemainder_le
    (hPan : LiuPanCanonicalCoprimeTheorem) (l : Filter ℕ) (hl : l ≤ atTop)
    (epsilon A : ℝ) (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hlambda : ∀ᶠ N : ℕ in l,
      LiuSelbergLambdaAdmissible N epsilon (lambda N)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in l,
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon (lambda N)| ≤
          C * N / Real.log N ^ A := by
  rcases hPan.eventually_liuPaperQSourceFullDistributionMajorant_le
      epsilon A hepsilon hA with ⟨C, hC, N₀, hmajorant⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlambda, (eventually_ge_atTop N₀).filter_mono hl,
      (eventually_ge_atTop (1 : ℕ)).filter_mono hl] with N hlambdaN hN₀ hN
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant
    (liuLogarithmicIntegral 2) N epsilon (lambda N) hN hlambdaN).trans
      (hmajorant N hN₀)

/-- Backward-compatible remainder wrapper for the stronger canonical contract. -/
theorem LiuPanWangDingTheorem.eventually_abs_liuSelbergRemainder_le
    (hPan : LiuPanWangDingTheorem) (l : Filter ℕ) (hl : l ≤ atTop)
    (epsilon A : ℝ) (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hlambda : ∀ᶠ N : ℕ in l,
      LiuSelbergLambdaAdmissible N epsilon (lambda N)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in l,
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon (lambda N)| ≤
          C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_abs_liuSelbergRemainder_le
    l hl epsilon A lambda hepsilon hA hlambda

/-- Source-faithful remainder wrapper from literal Corollary `(2.30)`. -/
theorem LiuPanWangDingCorollary230.eventually_abs_liuSelbergRemainder_le
    (hPan : LiuPanWangDingCorollary230) (l : Filter ℕ) (hl : l ≤ atTop)
    (epsilon A : ℝ) (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hlambda : ∀ᶠ N : ℕ in l,
      LiuSelbergLambdaAdmissible N epsilon (lambda N)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in l,
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon (lambda N)| ≤
          C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_abs_liuSelbergRemainder_le
    l hl epsilon A lambda hepsilon hA hlambda

/-- Eventual bound for the actual Liu remainder.  The lambda admissibility and
the three source-family analytic estimates remain separate explicit inputs. -/
theorem eventually_abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop,
      |liuSelbergRemainder (liuLogarithmicIntegral kappa) N epsilon (lambda N)| ≤
        (C1 + C2 + C3) * N / Real.log N ^ A +
          15 * liuLogarithmicIntegralUpperConstant kappa *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hsource : LiuMainPanSourceFamilyInputs
      (liuLogarithmicIntegral kappa) A B C1 C2 C3 u v := by
    filter_upwards [hI, hII, hresidual] with N hIN hIIN hresidualN
    exact ⟨hIN, hIIN, hresidualN⟩
  have hmajorant :=
    eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_sourceFaithfulSignedInputs
      kappa epsilon A B C1 C2 C3 u v hepsilon hB hsource
  filter_upwards [hlambda, hmajorant, eventually_ge_atTop 1] with
    N hlambdaN hmajorantN hN
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant
    (liuLogarithmicIntegral kappa) N epsilon (lambda N) hN hlambdaN).trans
      hmajorantN

/-- Conditional eventual bound for Liu's switched Selberg count.  The numerical
main-term estimate, lambda admissibility, and the three source-family analytic
estimates are all retained as explicit inputs. -/
theorem eventually_liuSelbergSwitchedCount_le_of_mainTermUpperBound_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hmain : ∀ᶠ N : ℕ in atTop,
      LiuSelbergMainTermUpperBound kappa N epsilon (lambda N))
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop,
      liuSelbergSwitchedCount N epsilon (lambda N) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + C3) * N / Real.log N ^ A +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hR :=
    eventually_abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_sourceInputs
      kappa epsilon A B C1 C2 C3 u v lambda hepsilon hB hlambda hI hII hresidual
  filter_upwards [hmain, hR] with N hmainN hRN
  rw [liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainN (le_trans (le_abs_self _) hRN)

/-- Conditional eventual bound for Liu's original squared-divisor Selberg
expression, obtained from the exact square expansion and switched-count bound. -/
theorem eventually_liuSelbergSquareCount_le_of_mainTermUpperBound_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hmain : ∀ᶠ N : ℕ in atTop,
      LiuSelbergMainTermUpperBound kappa N epsilon (lambda N))
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop,
      liuSelbergSquareCount N epsilon (lambda N) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + C3) * N / Real.log N ^ A +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hM :=
    eventually_liuSelbergSwitchedCount_le_of_mainTermUpperBound_sourceInputs
      kappa epsilon A B C1 C2 C3 u v lambda hepsilon hB
        hmain hlambda hI hII hresidual
  filter_upwards [hM] with N hMN
  rw [liuSelbergSquareCount_eq_switchedCount]
  exact hMN

end MathlibNt.SieveTheory.LiuWeight
