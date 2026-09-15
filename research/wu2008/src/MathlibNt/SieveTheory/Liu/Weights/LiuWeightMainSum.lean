import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral

/-!
# Liu's genuine logarithmic-integral weight sum

This module reindexes the finite characteristic weight by its unique prime-pair
representation and separates Liu's printed reciprocal-log estimate from the
comparison between the genuine logarithmic integral and `x / log x`.
-/

open scoped BigOperators
open Filter Asymptotics

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

/-- The weighted main-model sum in Liu's factored `M₁`. -/
noncomputable def liuWeightMainSum (main : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ range (N + 1),
    liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a * main ((N : ℝ) / a)

/-- Exact finite reindexing of Liu's characteristic weight by its unique
admissible ordered prime pair. -/
theorem liuWeightMainSum_eq_sum_pairs (main : ℝ → ℝ) (N : ℕ) :
    liuWeightMainSum main N =
      ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
        main ((N : ℝ) / (p.1 * p.2)) := by
  unfold liuWeightMainSum
  simpa only [Nat.cast_mul] using
    sum_liuWeight_mul_eq_sum_pairs_of_support N (liuSourceZ10 N) (liuSourceY3 N)
      (fun a => main ((N : ℝ) / a))

/-- The reciprocal-log sum printed in Liu's `lm-mt`, with every quotient taken
in `ℝ`. -/
noncomputable def liuSourceReciprocalLogSum (N : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    1 / (((p.1 : ℝ) * p.2) * Real.log ((N : ℝ) / (p.1 * p.2)))

/-- Transparent statement of the source estimate
`∑ f(a)/(a log(N/a)) ≤ 0.49254/log N`. -/
def LiuSourceReciprocalLogBound (N : ℕ) : Prop :=
  liuSourceReciprocalLogSum N ≤ 0.49254 / Real.log N

/-- The `x / log x` proxy weight sum is exactly `N` times Liu's
reciprocal-log sum. -/
theorem liuWeightMainSum_div_log_eq (N : ℕ) (hN : 8 ≤ N) :
    liuWeightMainSum (fun x : ℝ => x / Real.log x) N =
      (N : ℝ) * liuSourceReciprocalLogSum N := by
  rw [liuWeightMainSum_eq_sum_pairs]
  unfold liuSourceReciprocalLogSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hp
  have hlog : 0 < Real.log ((N : ℝ) / (p.1 * p.2)) := by
    exact Real.log_pos (by
      have hx := two_le_div_of_mem_liuWeightPairs hN hp
      linarith)
  field_simp [ne_of_gt hprod, ne_of_gt hlog]

/-- Liu's reciprocal-log estimate gives the printed proxy main-sum bound
without any natural-number division. -/
theorem liuWeightMainSum_div_log_le (N : ℕ) (hN : 8 ≤ N)
    (hsource : LiuSourceReciprocalLogBound N) :
    liuWeightMainSum (fun x : ℝ => x / Real.log x) N ≤
      0.49254 * (N : ℝ) / Real.log N := by
  rw [liuWeightMainSum_div_log_eq N hN]
  unfold LiuSourceReciprocalLogBound at hsource
  calc
    (N : ℝ) * liuSourceReciprocalLogSum N ≤
        (N : ℝ) * (0.49254 / Real.log N) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = 0.49254 * (N : ℝ) / Real.log N := by ring

/-- The genuine-logarithmic-integral weighted-sum estimate needed for Liu's
`M₁`. -/
def LiuGenuineLiWeightMainSumBound
    (kappa K : ℝ) (N : ℕ) : Prop :=
  0 ≤ liuWeightMainSum (liuLogarithmicIntegral kappa) N ∧
    liuWeightMainSum (liuLogarithmicIntegral kappa) N ≤
      K * (N : ℝ) / Real.log N

/-- The exact summed correction from replacing the source proxy by the genuine
logarithmic integral. -/
noncomputable def liuGenuineLiRemainderSum (kappa : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))

/-- A fixed Mertens bound for the first prime coordinate of Liu's pairs. -/
noncomputable def liuWeightP₁ReciprocalBound : ℝ :=
  Classical.choose (MertensTheorem.prime_reciprocal_sum_bounded
    (1 / 10 : ℝ) 1 (by norm_num) (by norm_num))

/-- The chosen constant uniformly bounds the first-coordinate reciprocal mass. -/
lemma liuWeightP₁ReciprocalBound_spec (N : ℕ) (hN : 2 ≤ N) :
    |liuSourceR1P₁DivisorReciprocalSum N 0| ≤ liuWeightP₁ReciprocalBound := by
  rw [liuSourceR1P₁DivisorReciprocalSum,
    show liuSourceR1RectangularP₁Range N 0 =
      (range (N + 1)).filter (fun p : ℕ => p.Prime ∧
        ((N : ℝ) ^ (1 / 10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ (1 : ℝ))) by
      ext p
      simp [liuSourceR1RectangularP₁Range]
      omega]
  simpa [liuWeightP₁ReciprocalBound] using
    (Classical.choose_spec (MertensTheorem.prime_reciprocal_sum_bounded
      (1 / 10 : ℝ) 1 (by norm_num) (by norm_num)) N hN)

/-- The first-coordinate reciprocal mass is nonnegative. -/
lemma liuSourceR1P₁DivisorReciprocalSum_nonneg (N : ℕ) :
    0 ≤ liuSourceR1P₁DivisorReciprocalSum N 0 := by
  unfold liuSourceR1P₁DivisorReciprocalSum
  apply Finset.sum_nonneg
  intro p _
  exact one_div_nonneg.mpr (Nat.cast_nonneg p)

/-- The uniform first-coordinate Mertens bound is nonnegative. -/
lemma liuWeightP₁ReciprocalBound_nonneg :
    0 ≤ liuWeightP₁ReciprocalBound :=
  (liuSourceR1P₁DivisorReciprocalSum_nonneg 2).trans
    ((le_abs_self _).trans (liuWeightP₁ReciprocalBound_spec 2 (by norm_num)))

/-- The reciprocal mass of the exact Liu pair set. -/
noncomputable def liuWeightPairReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    1 / ((p.1 : ℝ) * p.2)

/-- The exact pair reciprocal mass is uniformly bounded by the two Mertens constants. -/
lemma liuWeightPairReciprocalSum_le (N : ℕ) (hN : 8 ≤ N) :
    liuWeightPairReciprocalSum N ≤
      liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound := by
  have heq : liuWeightPairReciprocalSum N =
      paperQStyleR1PairReciprocalSum N (liuSourceZ10 N) (liuSourceY3 N) 0 := by
    unfold liuWeightPairReciprocalSum
    rw [paperQStyleR1PairReciprocalSum]
    have hfilter : (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).filter
        (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ 0) =
        liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N) := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      exact ⟨liuWeightSupport_le ⟨p, hp, rfl⟩, Nat.dvd_zero _⟩
    rw [hfilter]
  calc
    liuWeightPairReciprocalSum N =
        paperQStyleR1PairReciprocalSum N (liuSourceZ10 N) (liuSourceY3 N) 0 := heq
    _ ≤ liuSourceR1RectangularPairReciprocalSum N 0 :=
      paperQStyleR1PairReciprocalSum_source_le_rectangular N 0
    _ = liuSourceR1P₁DivisorReciprocalSum N 0 *
        liuSourceR1P₂IntervalReciprocalSum N :=
      liuSourceR1RectangularPairReciprocalSum_eq_mul N 0
    _ ≤ liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound := mul_le_mul
      ((le_abs_self _).trans (liuWeightP₁ReciprocalBound_spec N (by omega)))
      (liuSourceR1P₂IntervalReciprocalSum_le N (by omega))
      (liuSourceR1P₂IntervalReciprocalSum_nonneg N)
      liuWeightP₁ReciprocalBound_nonneg

/-- The genuine-minus-proxy remainder is eventually bounded by `x / log(x)^2`.
The additive normalization is absorbed using `log(x)^2 = o(x)`. -/
lemma eventually_abs_liuLogarithmicIntegralRemainder_le (kappa : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, 2 ≤ x →
      |liuLogarithmicIntegralRemainder kappa x| ≤
        C * x / Real.log x ^ 2 := by
  obtain ⟨c, hc⟩ :=
    Asymptotics.isBigO_iff.mp Chebyshev.integral_one_div_log_sq_isBigO
  have hlograw := (Asymptotics.isLittleO_iff.mp
    (Real.isLittleO_pow_log_id_atTop (n := 2))) (by norm_num : (0 : ℝ) < 1)
  have hlog : ∀ᶠ x : ℝ in atTop, |Real.log x ^ 2| ≤ 1 * |x| := by
    filter_upwards [hlograw] with x hx
    simpa [Real.norm_eq_abs] using hx
  refine ⟨max c 0 + |kappa - 2 / Real.log 2|, by positivity, ?_⟩
  filter_upwards [hc, hlog] with x hcx hlogx hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x / Real.log x ^ 2 := by positivity
  have hlogx' : Real.log x ^ 2 ≤ x := by
    simpa [abs_of_nonneg (sq_nonneg (Real.log x)), abs_of_pos hxpos] using hlogx
  have hscale_one : 1 ≤ x / Real.log x ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hlogpos)]
    simpa using hlogx'
  have hcintegral : |∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| ≤
      max c 0 * (x / Real.log x ^ 2) := by
    calc
      |∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| =
          ‖∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2‖ := by rfl
      _ ≤ c * ‖x / Real.log x ^ 2‖ := hcx
      _ ≤ max c 0 * ‖x / Real.log x ^ 2‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ = max c 0 * (x / Real.log x ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hscale]
  have hconstant : |kappa - 2 / Real.log 2| ≤
      |kappa - 2 / Real.log 2| * (x / Real.log x ^ 2) := by
    calc
      |kappa - 2 / Real.log 2| = |kappa - 2 / Real.log 2| * 1 := by ring
      _ ≤ |kappa - 2 / Real.log 2| * (x / Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_left hscale_one (abs_nonneg _)
  rw [liuLogarithmicIntegralRemainder_eq kappa hx]
  calc
    |kappa - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| ≤
        |kappa - 2 / Real.log 2| + |∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2| :=
      abs_add_le _ _
    _ ≤ |kappa - 2 / Real.log 2| + max c 0 * (x / Real.log x ^ 2) :=
      add_le_add (le_refl _) hcintegral
    _ ≤ |kappa - 2 / Real.log 2| * (x / Real.log x ^ 2) +
        max c 0 * (x / Real.log x ^ 2) := add_le_add hconstant (le_refl _)
    _ = (max c 0 + |kappa - 2 / Real.log 2|) * x / Real.log x ^ 2 := by ring

/-- The pair logarithm lower bound converts the pointwise remainder estimate to
an `N / (p₁ p₂ log(N)^2)` estimate. -/
lemma liuLogarithmicIntegralRemainder_pair_le
    (kappa C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 8 ≤ N)
    (p : ℕ × ℕ) (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N))
    (hpoint : |liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| ≤
      C * ((N : ℝ) / (p.1 * p.2)) /
        Real.log ((N : ℝ) / (p.1 * p.2)) ^ 2) :
    |liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| ≤
      9 * C * (N : ℝ) / (((p.1 : ℝ) * p.2) * Real.log N ^ 2) := by
  have hp_pos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hp
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogx : (1 / 3 : ℝ) * Real.log N ≤
      Real.log ((N : ℝ) / (p.1 * p.2)) :=
    one_third_mul_log_le_log_div_of_mem_liuWeightPairs hN hp
  have hlogxpos : 0 < Real.log ((N : ℝ) / (p.1 * p.2)) := by linarith
  have hinv : 1 / Real.log ((N : ℝ) / (p.1 * p.2)) ^ 2 ≤
      9 / Real.log N ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hlogxpos) (sq_pos_of_pos hlogN)]
    nlinarith [sq_nonneg (Real.log ((N : ℝ) / (p.1 * p.2)))]
  calc
    |liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| ≤
        C * ((N : ℝ) / (p.1 * p.2)) /
          Real.log ((N : ℝ) / (p.1 * p.2)) ^ 2 := hpoint
    _ = (C * ((N : ℝ) / (p.1 * p.2))) *
        (1 / Real.log ((N : ℝ) / (p.1 * p.2)) ^ 2) := by ring
    _ ≤ (C * ((N : ℝ) / (p.1 * p.2))) * (9 / Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 9 * C * (N : ℝ) / (((p.1 : ℝ) * p.2) * Real.log N ^ 2) := by
      field_simp [ne_of_gt hp_pos, ne_of_gt hlogN]

/-- The pointwise pair majorant factors through the exact reciprocal pair mass. -/
lemma liuGenuineLiRemainderSum_factor (C : ℝ) (N : ℕ) :
    (∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
      9 * C * (N : ℝ) / (((p.1 : ℝ) * p.2) * Real.log N ^ 2)) =
    (9 * C * (N : ℝ) / Real.log N ^ 2) * liuWeightPairReciprocalSum N := by
  unfold liuWeightPairReciprocalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_pos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hp
  field_simp [ne_of_gt hp_pos]

/-- Exact decomposition of the genuine weight sum into the source proxy and its
summed logarithmic-integral correction. -/
theorem liuWeightMainSum_logarithmicIntegral_eq_proxy_add_remainder
    (kappa : ℝ) (N : ℕ) :
    liuWeightMainSum (liuLogarithmicIntegral kappa) N =
      liuWeightMainSum (fun x : ℝ => x / Real.log x) N +
        liuGenuineLiRemainderSum kappa N := by
  rw [liuWeightMainSum_eq_sum_pairs, liuWeightMainSum_eq_sum_pairs]
  unfold liuGenuineLiRemainderSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold liuLogarithmicIntegralRemainder
  ring

/-- The sole analytic correction estimate needed after exact reindexing. -/
def LiuGenuineLiRemainderSumBound (kappa eta : ℝ) (N : ℕ) : Prop :=
  |liuGenuineLiRemainderSum kappa N| ≤
    eta * (N : ℝ) / Real.log N

/-- Eventual `o(N/log N)` form of the sole remaining correction estimate. -/
def LiuGenuineLiRemainderSumIsLittleO (kappa : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    LiuGenuineLiRemainderSumBound kappa eta N

/-- The summed genuine-logarithmic-integral correction is `o(N / log N)`. -/
theorem liuGenuineLiRemainderSum_isLittleO (kappa : ℝ) :
    LiuGenuineLiRemainderSumIsLittleO kappa := by
  obtain ⟨C, hC, hpoint⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le kappa
  obtain ⟨X, hX⟩ := eventually_atTop.mp hpoint
  let X' : ℝ := max 2 X
  have hX'pos : 0 < X' := by
    dsimp [X']
    linarith [le_max_left (2 : ℝ) X]
  have hlogX : ∀ᶠ n : ℕ in atTop, 3 * Real.log X' ≤ Real.log (n : ℝ) := by
    apply (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    exact eventually_ge_atTop _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlogX
  let B : ℝ := liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound
  intro eta heta
  have hlogeta : ∀ᶠ n : ℕ in atTop, 9 * C * B / eta ≤ Real.log (n : ℝ) := by
    apply (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    exact eventually_ge_atTop _
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hlogeta
  refine ⟨max 8 (max N₁ N₂), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hN₁bound : N₁ ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN₂bound : N₂ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hlogNX : 3 * Real.log X' ≤ Real.log (N : ℝ) := hN₁ N hN₁bound
  have hlogetaN : 9 * C * B / eta ≤ Real.log (N : ℝ) := hN₂ N hN₂bound
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  -- The threshold N₁ makes the pointwise remainder estimate uniform over all pairs.
  have hpair : ∀ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
      |liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| ≤
        9 * C * (N : ℝ) / (((p.1 : ℝ) * p.2) * Real.log N ^ 2) := by
    intro p hp
    apply liuLogarithmicIntegralRemainder_pair_le kappa C hC N hN8 p hp
    have hxp : 0 < (N : ℝ) / ((p.1 : ℝ) * p.2) := by
      have hp_pos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
        exact_mod_cast liuWeightPairs_product_pos hp
      positivity
    have hlogxp : Real.log X' ≤ Real.log ((N : ℝ) / (p.1 * p.2)) := by
      have hpLog := one_third_mul_log_le_log_div_of_mem_liuWeightPairs hN8 hp
      linarith
    have hXxp : X' ≤ (N : ℝ) / (p.1 * p.2) :=
      (Real.log_le_log_iff hX'pos hxp).mp hlogxp
    exact hX ((N : ℝ) / (p.1 * p.2))
      (le_trans (le_max_right 2 X) hXxp)
      (two_le_div_of_mem_liuWeightPairs hN8 hp)
  -- Sum the uniform estimate, then bound the exact reciprocal pair mass.
  have hsum : |liuGenuineLiRemainderSum kappa N| ≤
      9 * C * B * (N : ℝ) / Real.log N ^ 2 := by
    unfold liuGenuineLiRemainderSum
    calc
      |∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| ≤
          ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
            |liuLogarithmicIntegralRemainder kappa ((N : ℝ) / (p.1 * p.2))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          9 * C * (N : ℝ) / (((p.1 : ℝ) * p.2) * Real.log N ^ 2) := by
        exact Finset.sum_le_sum hpair
      _ = (9 * C * (N : ℝ) / Real.log N ^ 2) * liuWeightPairReciprocalSum N :=
        liuGenuineLiRemainderSum_factor C N
      _ ≤ (9 * C * (N : ℝ) / Real.log N ^ 2) * B :=
        mul_le_mul_of_nonneg_left (liuWeightPairReciprocalSum_le N hN8) (by positivity)
      _ = 9 * C * B * (N : ℝ) / Real.log N ^ 2 := by ring
  unfold LiuGenuineLiRemainderSumBound
  have hcoef : 9 * C * B ≤ eta * Real.log (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ heta).mp hlogetaN
  have hnum : 9 * C * B * (N : ℝ) ≤
      (eta * Real.log (N : ℝ)) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef (by positivity)
  calc
    |liuGenuineLiRemainderSum kappa N| ≤
        9 * C * B * (N : ℝ) / Real.log N ^ 2 := hsum
    _ ≤ (eta * Real.log (N : ℝ)) * (N : ℝ) / Real.log N ^ 2 :=
      div_le_div_of_nonneg_right hnum (le_of_lt (sq_pos_of_pos hlogN))
    _ = eta * (N : ℝ) / Real.log N := by
      field_simp [ne_of_gt hlogN]

/-- Under `kappa ≥ 0`, every summand in the genuine weight sum is
nonnegative. -/
theorem liuWeightMainSum_logarithmicIntegral_nonneg
    (kappa : ℝ) (hκ : 0 ≤ kappa) (N : ℕ) (hN : 8 ≤ N) :
    0 ≤ liuWeightMainSum (liuLogarithmicIntegral kappa) N := by
  rw [liuWeightMainSum_eq_sum_pairs]
  apply Finset.sum_nonneg
  intro p hp
  exact liuLogarithmicIntegral_nonneg kappa hκ
    (two_le_div_of_mem_liuWeightPairs hN hp)

/-- The source `0.49254` estimate and one precise remainder-sum bound imply the
genuine logarithmic-integral estimate. -/
theorem liuGenuineLiWeightMainSumBound_of_source_of_remainder
    (kappa eta : ℝ) (hκ : 0 ≤ kappa) (_heta : 0 < eta)
    (N : ℕ) (hN : 8 ≤ N)
    (hsource : LiuSourceReciprocalLogBound N)
    (hremainder : LiuGenuineLiRemainderSumBound kappa eta N) :
    LiuGenuineLiWeightMainSumBound kappa (0.49254 + eta) N := by
  constructor
  · exact liuWeightMainSum_logarithmicIntegral_nonneg kappa hκ N hN
  rw [liuWeightMainSum_logarithmicIntegral_eq_proxy_add_remainder]
  have hproxy := liuWeightMainSum_div_log_le N hN hsource
  have hrem : liuGenuineLiRemainderSum kappa N ≤
      eta * (N : ℝ) / Real.log N :=
    (le_abs_self _).trans hremainder
  calc
    liuWeightMainSum (fun x : ℝ => x / Real.log x) N +
          liuGenuineLiRemainderSum kappa N ≤
        0.49254 * (N : ℝ) / Real.log N +
          eta * (N : ℝ) / Real.log N :=
      add_le_add hproxy hrem
    _ = (0.49254 + eta) * (N : ℝ) / Real.log N := by ring

/-- For a nonnegative normalization, Liu's printed reciprocal-log estimate
eventually implies the genuine logarithmic-integral weight-sum bound. -/
theorem eventually_liuGenuineLiWeightMainSumBound_of_source
    (kappa : ℝ) (hκ : 0 ≤ kappa) :
    ∀ eta : ℝ, 0 < eta → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      LiuSourceReciprocalLogBound N →
        LiuGenuineLiWeightMainSumBound kappa (0.49254 + eta) N := by
  intro eta heta
  obtain ⟨N₀, hN₀⟩ := liuGenuineLiRemainderSum_isLittleO kappa eta heta
  refine ⟨max 8 N₀, fun N hN hsource => ?_⟩
  exact liuGenuineLiWeightMainSumBound_of_source_of_remainder
    kappa eta hκ heta N (le_trans (le_max_left 8 N₀) hN)
    hsource (hN₀ N (le_trans (le_max_right 8 N₀) hN))

end MathlibNt.SieveTheory.LiuWeight
