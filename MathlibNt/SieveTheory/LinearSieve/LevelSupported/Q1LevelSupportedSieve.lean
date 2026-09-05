import MathlibNt.SieveTheory.LinearSieve.LevelSupported.Q1MainTermAbsorption
import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergOptimalWeights
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorConvolution
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergUniformEuler

/-!
# A level-supported upper sieve for the `q¹` count

This file keeps the level restriction in the finite object that is estimated:
we first majorize each corrected candidate fibre by a Selberg square, and only
then expand it into reduced-residue progressions.  Thus the distribution input
below is a cutoff-supported signed aggregate, not the obsolete full positive
sum `q1ErrorTermSum`.

The analytic shape is the one used in Liu 2022, `th-mvt`, lines 137--151, with
the Bombieri--Vinogradov input in lines 81--86: a level-supported Selberg
square is expanded before a signed reduced-residue mean-value estimate is
applied.  The producer contract at the end deliberately separates the sieve
fundamental lemma from the `∀ A ∃ B(A)` weighted Pan/BV theorem; the
non-reduced correction and the floor-safe admissible level are proved
unconditionally in this file.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open scoped Classical

noncomputable section

/-- The q¹ progression discrepancy with a genuine logarithmic integral.
The parameter `κ` records the additive normalization left implicit by Liu's
notation. -/
noncomputable def q1TrueLiAPError (κ : ℝ) (N m : ℕ) : ℝ :=
  (q1APBaseCount N m : ℝ) -
    LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) / Nat.totient m

/-- The new discrepancy is literally the `a = 1` prime-progression error with
the genuine `li` main term. -/
theorem q1TrueLiAPError_eq_primesInAPBelow
    (κ : ℝ) (N m : ℕ) (hN : 2 ≤ N) :
    q1TrueLiAPError κ N m =
      (AnalyticNumberTheory.Sieve.primesInAPBelow (N - 2) 1 m (N % m) : ℝ) -
        LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) / Nat.totient m := by
  unfold q1TrueLiAPError q1APBaseCount
  congr 1
  exact_mod_cast supportAPBaseCount_eq_primesInAPBelow N m hN

/-- The natural distribution cutoff
`⌊N^(1/2) / log(N)^B⌋`.  Keeping this as a natural number makes every later
modulus restriction a finite predicate. -/
noncomputable def q1LevelModulusCutoff (N B : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ B)

/-- The selected fixed q¹ Selberg level.  Taking the natural square root after
dividing the Pan cutoff by the switching range makes the cutoff inequality
floor-safe at the level of natural numbers. -/
noncomputable def q1PanSelbergLevel (B N : ℕ) : ℕ :=
  Nat.sqrt (q1LevelModulusCutoff N B / correctedChenY N)

/-- Divisors of the corrected sifting product which survive the explicit
Selberg level `L`. -/
noncomputable def q1LevelCarrier (N L : ℕ) : Finset ℕ :=
  (correctedChenSiftingProduct N).divisors.filter (fun d => d ≤ L)

/-- Membership in the finite level carrier exposes both its sieve support and
its numerical level. -/
theorem mem_q1LevelCarrier {N L d : ℕ} :
    d ∈ q1LevelCarrier N L ↔
      d ∣ correctedChenSiftingProduct N ∧ d ≤ L := by
  have hP0 : correctedChenSiftingProduct N ≠ 0 :=
    correctedChenSiftingProduct_ne_zero N
  simp [q1LevelCarrier, Nat.mem_divisors, hP0]

/-- The reciprocal-totient bounding sieve on the corrected Chen sifting
product.  Unlike Liu's source sieve, its prime support is exactly the corrected
product used by the q¹ candidate condition. -/
noncomputable def q1LevelBoundingSieve (N : ℕ) :
    BoundingSieve where
  support := ∅
  prodPrimes := correctedChenSiftingProduct N
  prodPrimes_squarefree := correctedChenSiftingProduct_squarefree N
  weights := fun _ => 0
  weights_nonneg := by intro n; simp
  totalMass := 0
  nu := LiuWeight.liuSelbergReciprocalTotient
  nu_mult := LiuWeight.liuSelbergReciprocalTotient_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpP
    have hphi : 0 < (Nat.totient p : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr hp.pos)
    simpa [LiuWeight.liuSelbergReciprocalTotient, hp.ne_zero, one_div] using
      (inv_pos.2 hphi)
  nu_lt_one_of_prime := by
    intro p hp hpP
    have hpgt : 2 < p :=
      ((prime_dvd_correctedChenSiftingProduct hp).mp hpP).2.1
    have hphi_nat : 1 < Nat.totient p := by
      rw [Nat.totient_prime hp]
      omega
    have hphi : 1 < (Nat.totient p : ℝ) := by exact_mod_cast hphi_nat
    have hphi_pos : 0 < (Nat.totient p : ℝ) := by linarith
    simpa [LiuWeight.liuSelbergReciprocalTotient, hp.ne_zero, one_div] using
      (inv_lt_one₀ hphi_pos).2 hphi

/-- The lcm of two level divisors remains below the square level. -/
theorem q1LevelCarrier_lcm_le_square
    {N L d1 d2 : ℕ} (hd1 : d1 ∈ q1LevelCarrier N L)
    (hd2 : d2 ∈ q1LevelCarrier N L) :
    Nat.lcm d1 d2 ≤ L ^ 2 := by
  have hPpos : 0 < correctedChenSiftingProduct N :=
    Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
  have hd1pos : 0 < d1 :=
    Nat.pos_of_dvd_of_pos (mem_q1LevelCarrier.mp hd1).1 hPpos
  have hd2pos : 0 < d2 :=
    Nat.pos_of_dvd_of_pos (mem_q1LevelCarrier.mp hd2).1 hPpos
  calc
    Nat.lcm d1 d2 ≤ d1 * d2 := Nat.lcm_le_mul hd1pos hd2pos
    _ ≤ L * L := Nat.mul_le_mul (mem_q1LevelCarrier.mp hd1).2
      (mem_q1LevelCarrier.mp hd2).2
    _ = L ^ 2 := by ring

/-- A raw Selberg weight supported on `q1LevelCarrier`.  The upper-sieve
majorization itself is supplied below as an analytic input; this structure
records precisely its finite support, normalization, and boundedness. -/
structure Q1LevelSupportedSelbergWeight (N L : ℕ) where
  lambda : ℕ → ℝ
  lambda_one : lambda 1 = 1
  support : ∀ d, lambda d ≠ 0 → d ∈ q1LevelCarrier N L
  abs_le_one : ∀ d, |lambda d| ≤ 1

/-- The cutoff-parameterized optimal Selberg weight on the corrected Chen
sifting product. -/
noncomputable def q1LevelOptimalSelbergWeight
    (N L : ℕ) (hL : 1 ≤ L) : Q1LevelSupportedSelbergWeight N L where
  lambda :=
    LiuWeight.truncatedSelbergOptimalLambda (q1LevelBoundingSieve N) L
  lambda_one :=
    LiuWeight.truncatedSelbergOptimalLambda_one (q1LevelBoundingSieve N) hL
  support := by
    intro d hd
    exact mem_q1LevelCarrier.mpr
      (LiuWeight.truncatedSelbergOptimalLambda_support hd)
  abs_le_one := fun d =>
    LiuWeight.abs_truncatedSelbergOptimalLambda_le_one
      (q1LevelBoundingSieve N) hL

/-- The exact denominator attached to the corrected q¹ level. -/
noncomputable def q1LevelSelbergDenominator (N L : ℕ) : ℝ :=
  LiuWeight.truncatedSelbergDenominator (q1LevelBoundingSieve N) L

private theorem q1LevelSelbergTerm_eq_liuSelbergTerm
    {N d : ℕ} (hd : d ∣ correctedChenSiftingProduct N) :
    (q1LevelBoundingSieve N).selbergTerms d =
      LiuWeight.liuSelbergTerm d := by
  let S := q1LevelBoundingSieve N
  rw [BoundingSieve.selbergTerms_apply, ← S.prod_primeFactors_nu hd,
    ← Finset.prod_mul_distrib]
  unfold LiuWeight.liuSelbergTerm
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hpP : p ∣ correctedChenSiftingProduct N := hpd.trans hd
  have hpgt : 2 < p :=
    ((prime_dvd_correctedChenSiftingProduct hpprime).mp hpP).2.1
  have hnu : S.nu p = ((p : ℝ) - 1)⁻¹ := by
    dsimp [S, q1LevelBoundingSieve,
      LiuWeight.liuSelbergReciprocalTotient]
    rw [if_neg hpprime.ne_zero, Nat.totient_prime hpprime,
      Nat.cast_sub hpprime.one_le]
    simp [one_div]
  rw [hnu]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_trans Nat.one_lt_two hpgt)
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hpgt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hpm2' : -2 + (p : ℝ) ≠ 0 := by linarith
  field_simp [hpm1, hpm2, hpm2']
  rw [show (p : ℝ) - 1 - 1 = (p : ℝ) - 2 by ring, div_self hpm2]

private theorem dvd_correctedChenSiftingProduct_iff_squarefree_coprime
    {N L d : ℕ} (hNeven : Even N) (hLz : L < correctedChenZ N)
    (hdL : d ≤ L) :
    d ∣ correctedChenSiftingProduct N ↔ Squarefree d ∧ Nat.Coprime d N := by
  classical
  constructor
  · intro hd
    refine ⟨(correctedChenSiftingProduct_squarefree N).squarefree_of_dvd hd, ?_⟩
    have hPN : Nat.Coprime (correctedChenSiftingProduct N) N := by
      apply Nat.coprime_of_dvd'
      intro p hp hpP hpN
      exact False.elim
        (((prime_dvd_correctedChenSiftingProduct hp).mp hpP).2.2 hpN)
    exact hPN.coprime_dvd_left hd
  · rintro ⟨hsq, hcop⟩
    have hP0 : correctedChenSiftingProduct N ≠ 0 :=
      correctedChenSiftingProduct_ne_zero N
    have hsub : d.primeFactors ⊆
        (correctedChenSiftingProduct N).primeFactors := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hpz : p < correctedChenZ N := by
        exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) hpd).trans hdL
          |>.trans_lt hLz
      have hpN : ¬ p ∣ N :=
        hpprime.coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_left hpd hcop)
      have hp2 : 2 < p := by
        have hpne2 : p ≠ 2 := by
          intro h
          apply hpN
          rw [h]
          exact hNeven.two_dvd
        exact lt_of_le_of_ne hpprime.two_le (by simpa using hpne2.symm)
      have hpP : p ∣ correctedChenSiftingProduct N :=
        (prime_dvd_correctedChenSiftingProduct hpprime).mpr
          ⟨hpz, hp2, hpN⟩
      exact (Nat.mem_primeFactors_of_ne_zero hP0).mpr ⟨hpprime, hpP⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact (Nat.prod_primeFactors_dvd_iff hP0).mpr hsub

/-- Once the cutoff lies below the corrected prime threshold, the q¹
denominator is exactly the established squarefree-coprime arithmetic sum.  This
is the bridge to the uniform convolution and Euler-error estimates. -/
theorem q1LevelSelbergDenominator_eq_sum_Icc
    {N L : ℕ} (hNeven : Even N)
    (hLz : L < correctedChenZ N) :
    q1LevelSelbergDenominator N L =
      ∑ d ∈ Finset.Icc 1 L, LiuWeight.liuSelbergArithmetic N d := by
  classical
  let S := q1LevelBoundingSieve N
  let C := LiuWeight.truncatedSelbergCarrier S L
  let I := Finset.Icc 1 L
  have hCsub : C ⊆ I := by
    intro d hd
    have hdmem := Finset.mem_filter.mp hd
    have hdP : d ∣ correctedChenSiftingProduct N :=
      (Nat.mem_divisors.mp hdmem.1).1
    have hd0 : d ≠ 0 := Nat.ne_of_gt <|
      Nat.pos_of_dvd_of_pos hdP
        (Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N))
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, hdmem.2⟩
  have hterm : ∀ d ∈ C,
      S.selbergTerms d = LiuWeight.liuSelbergArithmetic N d := by
    intro d hd
    have hdmem := Finset.mem_filter.mp hd
    have hdP : d ∣ correctedChenSiftingProduct N :=
      (Nat.mem_divisors.mp hdmem.1).1
    have hd0 : d ≠ 0 := Nat.ne_of_gt <|
      Nat.pos_of_dvd_of_pos hdP
        (Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N))
    rw [q1LevelSelbergTerm_eq_liuSelbergTerm hdP]
    symm
    exact LiuWeight.liuSelbergArithmetic_eq_prod hd0
      ((correctedChenSiftingProduct_squarefree N).squarefree_of_dvd hdP)
      ((dvd_correctedChenSiftingProduct_iff_squarefree_coprime
        hNeven hLz hdmem.2).mp hdP).2
  have hzero : ∀ d ∈ I, d ∉ C →
      LiuWeight.liuSelbergArithmetic N d = 0 := by
    intro d hdI hdC
    by_contra hne
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      simp at hne
    by_cases hsc : Squarefree d ∧ Nat.Coprime d N
    · apply hdC
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr
            ⟨(dvd_correctedChenSiftingProduct_iff_squarefree_coprime
              hNeven hLz (Finset.mem_Icc.mp hdI).2).mpr hsc,
              correctedChenSiftingProduct_ne_zero N⟩,
          (Finset.mem_Icc.mp hdI).2⟩
    · simp [LiuWeight.liuSelbergArithmetic, hd0, hsc] at hne
  unfold q1LevelSelbergDenominator LiuWeight.truncatedSelbergDenominator
  change (∑ d ∈ C, S.selbergTerms d) =
    ∑ d ∈ I, LiuWeight.liuSelbergArithmetic N d
  calc
    (∑ d ∈ C, S.selbergTerms d) =
        ∑ d ∈ C, LiuWeight.liuSelbergArithmetic N d := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∑ d ∈ I, LiuWeight.liuSelbergArithmetic N d :=
      Finset.sum_subset hCsub (fun d hdI hdC => hzero d hdI hdC)

/-- Uniform denominator reduction at the corrected q¹ level.  The main term
retains the genuine Liu singular series; conversion to the finite truncated
normalization is intentionally deferred. -/
theorem abs_q1LevelSelbergDenominator_sub_log_main_le
    {N L : ℕ} (hNeven : Even N) (hN : 0 < N) (hL : 2 ≤ L)
    (hLz : L < correctedChenZ N) :
    |q1LevelSelbergDenominator N L -
        Real.log L / (2 * SingularSeries.liuSingularSeries N)| ≤
      2 * LiuWeight.liuSelbergAbsoluteLogMoment N +
        LiuWeight.liuSelbergAbsoluteMass N := by
  rw [q1LevelSelbergDenominator_eq_sum_Icc hNeven hLz]
  exact
    LiuWeight.abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le_uniform_reduction
      hNeven hN hL

/-- The finite divisor sum whose square is the upper-sieve majorant. -/
noncomputable def q1LevelDivisorSum
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) (n : ℕ) : ℝ :=
  ∑ d ∈ q1LevelCarrier N L, if d ∣ n then W.lambda d else 0

/-- The pre-sieving fibre for one switching modulus.  It contains all base
primes, before the corrected small-prime sieve is imposed. -/
noncomputable def q1PreSieveFibre (N q : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧ q ∣ N - p)

/-- The Selberg square over the complete pre-sieving `q`-fibre. -/
noncomputable def q1LevelSquareMajorant
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) (q : ℕ) : ℝ :=
  ∑ p ∈ q1PreSieveFibre N q, (q1LevelDivisorSum N L W (N - p)) ^ 2

/-- The double-sum expansion of `q1LevelSquareMajorant`.  The following
theorem proves that this is the literal finite expansion, with no asymptotic
or discarded terms. -/
noncomputable def q1LevelSquareExpanded
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) (q : ℕ) : ℝ :=
  ∑ d1 ∈ q1LevelCarrier N L,
    ∑ d2 ∈ q1LevelCarrier N L,
      W.lambda d1 * W.lambda d2 *
        (q1APBaseCount N (Nat.lcm q (Nat.lcm d1 d2)) : ℝ)

/-- A corrected candidate complement is coprime to the corrected sifting
product. -/
private theorem correctedCandidate_complement_coprime_sifting
    {N p : ℕ} (hp : p ∈ correctedChenCandidates N) :
    Nat.Coprime (correctedChenSiftingProduct N) (N - p) := by
  apply Nat.coprime_of_dvd
  intro r hr hrP
  exact (mem_correctedChenCandidates_iff_coprime_sifting N p).mp hp |>.2 r hr hrP

/-- On a corrected candidate, the level divisor sum is exactly its `d = 1`
term.  This is the finite point at which the upper-sieve square majorizes the
candidate indicator. -/
private theorem q1LevelDivisorSum_eq_one_of_correctedCandidate
    {N L p : ℕ} (W : Q1LevelSupportedSelbergWeight N L)
    (hp : p ∈ correctedChenCandidates N) :
    q1LevelDivisorSum N L W (N - p) = 1 := by
  have hcop : Nat.Coprime (correctedChenSiftingProduct N) (N - p) :=
    correctedCandidate_complement_coprime_sifting hp
  have hOne : 1 ∈ q1LevelCarrier N L := by
    apply W.support 1
    rw [W.lambda_one]
    norm_num
  unfold q1LevelDivisorSum
  rw [Finset.sum_eq_single 1]
  · simp [W.lambda_one]
  · intro d hd hdne
    have hdP : d ∣ correctedChenSiftingProduct N :=
      (mem_q1LevelCarrier.mp hd).1
    have hdnot : ¬ d ∣ N - p := by
      intro hdcomp
      have hdgcd : d ∣ Nat.gcd (correctedChenSiftingProduct N) (N - p) :=
        Nat.dvd_gcd hdP hdcomp
      rw [hcop.gcd_eq_one, Nat.dvd_one] at hdgcd
      exact hdne hdgcd
    simp [hdnot]
  · intro hnot
    exact (hnot hOne).elim

/-- Each corrected candidate in a switching fibre contributes one to the
level-supported Selberg square, while all other pre-sieving points contribute
a nonnegative square. -/
theorem q1CandidateAPCount_le_levelSquareMajorant
    {N L q : ℕ} (W : Q1LevelSupportedSelbergWeight N L)
    (_hq : q ∈ q1SwitchingPrimes N) :
    q1CandidateAPCount N q ≤ q1LevelSquareMajorant N L W q := by
  have hsubset :
      (correctedChenCandidates N).filter (fun p => q ∣ N - p) ⊆
        q1PreSieveFibre N q := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpc, hqdiv⟩
    rcases Finset.mem_filter.mp hpc with ⟨hpN, hpprime, hpcomp⟩
    exact Finset.mem_filter.mpr ⟨hpN, hpprime, hpcomp.1, hqdiv⟩
  unfold q1CandidateAPCount q1LevelSquareMajorant
  calc
    (((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card : ℝ) =
        ∑ p ∈ (correctedChenCandidates N).filter (fun p => q ∣ N - p), (1 : ℝ) := by
          simp
    _ = ∑ p ∈ (correctedChenCandidates N).filter (fun p => q ∣ N - p),
        (q1LevelDivisorSum N L W (N - p)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [q1LevelDivisorSum_eq_one_of_correctedCandidate W
            (Finset.mem_filter.mp hp).1]
          norm_num
    _ ≤ ∑ p ∈ q1PreSieveFibre N q,
        (q1LevelDivisorSum N L W (N - p)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro p _ _
          exact sq_nonneg _

/-- The finite level-supported square expansion. -/
theorem q1LevelSquareMajorant_eq_expanded
    (N L q : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    q1LevelSquareMajorant N L W q = q1LevelSquareExpanded N L W q := by
  classical
  unfold q1LevelSquareMajorant q1LevelSquareExpanded q1LevelDivisorSum
  rw [show (∑ p ∈ q1PreSieveFibre N q,
      (∑ d ∈ q1LevelCarrier N L, if d ∣ N - p then W.lambda d else 0) ^ 2) =
      ∑ p ∈ q1PreSieveFibre N q,
        (∑ d1 ∈ q1LevelCarrier N L, if d1 ∣ N - p then W.lambda d1 else 0) *
          (∑ d2 ∈ q1LevelCarrier N L, if d2 ∣ N - p then W.lambda d2 else 0) by
        apply Finset.sum_congr rfl
        intro p hp
        rw [pow_two]]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d1 hd1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d2 hd2
  have hcount :
      (∑ p ∈ q1PreSieveFibre N q,
        (if d1 ∣ N - p then (1 : ℝ) else 0) *
          (if d2 ∣ N - p then (1 : ℝ) else 0)) =
        (q1APBaseCount N (Nat.lcm q (Nat.lcm d1 d2)) : ℝ) := by
    have hfilter :
        (q1PreSieveFibre N q).filter
            (fun p => d1 ∣ N - p ∧ d2 ∣ N - p) =
          (Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm q (Nat.lcm d1 d2)]) := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_filter] at hp
        rcases hp with ⟨hpq, hd1p, hd2p⟩
        simp only [q1PreSieveFibre, Finset.mem_filter, Finset.mem_range] at hpq
        rcases hpq with ⟨hpN, hpprime, hpcomp, hqcomp⟩
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hpN, hpprime, hpcomp, ?_⟩
        apply (Nat.modEq_iff_dvd' (Nat.le_of_lt hpN)).2
        exact Nat.lcm_dvd hqcomp (Nat.lcm_dvd hd1p hd2p)
      · intro hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        rcases hp with ⟨hpN, hpprime, hpcomp, hpmod⟩
        have hlcm : Nat.lcm q (Nat.lcm d1 d2) ∣ N - p :=
          (Nat.modEq_iff_dvd' (Nat.le_of_lt hpN)).1 hpmod
        have hqcomp : q ∣ N - p := (Nat.lcm_dvd_iff.mp hlcm).1
        have hd12 : Nat.lcm d1 d2 ∣ N - p := (Nat.lcm_dvd_iff.mp hlcm).2
        rw [Finset.mem_filter]
        refine ⟨?_, (Nat.lcm_dvd_iff.mp hd12).1, (Nat.lcm_dvd_iff.mp hd12).2⟩
        simp only [q1PreSieveFibre, Finset.mem_filter, Finset.mem_range]
        exact ⟨hpN, hpprime, hpcomp, hqcomp⟩
    calc
      (∑ p ∈ q1PreSieveFibre N q,
        (if d1 ∣ N - p then (1 : ℝ) else 0) *
          (if d2 ∣ N - p then (1 : ℝ) else 0)) =
          ∑ p ∈ q1PreSieveFibre N q,
            if d1 ∣ N - p ∧ d2 ∣ N - p then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              by_cases h1 : d1 ∣ N - p <;> by_cases h2 : d2 ∣ N - p <;>
                simp [h1, h2]
      _ = (((q1PreSieveFibre N q).filter
          (fun p => d1 ∣ N - p ∧ d2 ∣ N - p)).card : ℝ) := by
            rw [Finset.sum_boole]
      _ = (q1APBaseCount N (Nat.lcm q (Nat.lcm d1 d2)) : ℝ) := by
            rw [hfilter]
            rfl
  calc
    (∑ p ∈ q1PreSieveFibre N q,
      (if d1 ∣ N - p then W.lambda d1 else 0) *
        (if d2 ∣ N - p then W.lambda d2 else 0)) =
        W.lambda d1 * W.lambda d2 *
          ∑ p ∈ q1PreSieveFibre N q,
            (if d1 ∣ N - p then (1 : ℝ) else 0) *
              (if d2 ∣ N - p then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases h1 : d1 ∣ N - p <;> by_cases h2 : d2 ∣ N - p <;>
            simp [h1, h2]
    _ = W.lambda d1 * W.lambda d2 *
        (q1APBaseCount N (Nat.lcm q (Nat.lcm d1 d2)) : ℝ) := by rw [hcount]

/-- Reduced switching moduli whose full Selberg square remains inside the
explicit Pan/Bombieri--Vinogradov cutoff. -/
noncomputable def q1LevelGoodSwitchingPrimes (N B L : ℕ) : Finset ℕ :=
  (q1SwitchingPrimes N).filter
    (fun q => ¬ q ∣ N ∧ q * L ^ 2 ≤ q1LevelModulusCutoff N B)

/-- The non-reduced switching moduli.  They are separated rather than assigned
a fictitious reduced-residue Pan error. -/
noncomputable def q1LevelNonreducedSwitchingPrimes (N _B _L : ℕ) : Finset ℕ :=
  (q1SwitchingPrimes N).filter (fun q => q ∣ N)

/-- Reduced switching moduli for which the selected level would exceed the
distribution cutoff. -/
noncomputable def q1LevelCutoffFailureSwitchingPrimes (N B L : ℕ) : Finset ℕ :=
  (q1SwitchingPrimes N).filter
    (fun q => ¬ q ∣ N ∧ q1LevelModulusCutoff N B < q * L ^ 2)

theorem mem_q1LevelGoodSwitchingPrimes {N B L q : ℕ} :
    q ∈ q1LevelGoodSwitchingPrimes N B L ↔
      q ∈ q1SwitchingPrimes N ∧ ¬ q ∣ N ∧
        q * L ^ 2 ≤ q1LevelModulusCutoff N B := by
  simp [q1LevelGoodSwitchingPrimes]

theorem mem_q1LevelNonreducedSwitchingPrimes {N B L q : ℕ} :
    q ∈ q1LevelNonreducedSwitchingPrimes N B L ↔
      q ∈ q1SwitchingPrimes N ∧ q ∣ N := by
  simp [q1LevelNonreducedSwitchingPrimes]

theorem mem_q1LevelCutoffFailureSwitchingPrimes {N B L q : ℕ} :
    q ∈ q1LevelCutoffFailureSwitchingPrimes N B L ↔
      q ∈ q1SwitchingPrimes N ∧ ¬ q ∣ N ∧
        q1LevelModulusCutoff N B < q * L ^ 2 := by
  simp [q1LevelCutoffFailureSwitchingPrimes]

/-- Every switching modulus is cutoff-safe at the canonical Selberg level.
This exact natural-number inequality needs no asymptotic threshold. -/
theorem q1PanSelbergLevel_modulus_le_cutoff
    (N B q : ℕ) (hq : q ∈ q1SwitchingPrimes N) :
    q * (q1PanSelbergLevel B N) ^ 2 ≤ q1LevelModulusCutoff N B := by
  have hqY : q ≤ correctedChenY N := by
    rw [q1SwitchingPrimes, Finset.mem_filter] at hq
    exact (Finset.mem_range.mp hq.1).le
  have hsq : (q1PanSelbergLevel B N) ^ 2 ≤
      q1LevelModulusCutoff N B / correctedChenY N := by
    simpa [q1PanSelbergLevel, pow_two] using
      Nat.sqrt_le (q1LevelModulusCutoff N B / correctedChenY N)
  calc
    q * (q1PanSelbergLevel B N) ^ 2 ≤
        correctedChenY N * (q1LevelModulusCutoff N B / correctedChenY N) :=
      Nat.mul_le_mul hqY hsq
    _ ≤ q1LevelModulusCutoff N B := Nat.mul_div_le _ _

/-- The canonical level retains a genuine Selberg scale: for each fixed Pan
exponent it eventually dominates `⌊N^(1/13)⌋`.  The exponent `1/13` is chosen
strictly below the limiting `1/12` supplied by `cutoff / Y`. -/
theorem eventually_floor_rpow_one_thirteenth_le_q1PanSelbergLevel (B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Nat.floor ((N : ℝ) ^ (1 / 13 : ℝ)) ≤ q1PanSelbergLevel B N := by
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ B ≤ (1 / 3 : ℝ) * x ^ (1 / 78 : ℝ) := by
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop (B : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 78)).bound
          (show 0 < (1 / 3 : ℝ) by norm_num)
    filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) (B : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) (1 / 78))] at hx
    simpa [Real.rpow_natCast] using hx
  have hnat : ∀ᶠ N : ℕ in Filter.atTop,
      (Real.log (N : ℝ)) ^ B ≤
        (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 78 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop (2 : ℕ)] with N hlog hN
  let R : ℕ := Nat.floor ((N : ℝ) ^ (1 / 13 : ℝ))
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogpowpos : 0 < Real.log (N : ℝ) ^ B := pow_pos hlogpos B
  have hR : (R : ℝ) ≤ (N : ℝ) ^ (1 / 13 : ℝ) := by
    dsimp [R]
    exact Nat.floor_le (Real.rpow_nonneg hNpos.le _)
  have hY := correctedChenY_le_two_mul_root N (by omega)
  have hprod : ((correctedChenY N * R ^ 2 : ℕ) : ℝ) ≤
      2 * (N : ℝ) ^ (19 / 39 : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      (correctedChenY N : ℝ) * (R : ℝ) ^ 2 ≤
          (2 * (N : ℝ) ^ (1 / 3 : ℝ)) *
            ((N : ℝ) ^ (1 / 13 : ℝ)) ^ 2 := by
        gcongr
      _ = 2 * (N : ℝ) ^ (19 / 39 : ℝ) := by
        rw [pow_two, ← Real.rpow_add hNpos]
        rw [mul_assoc, ← Real.rpow_add hNpos]
        norm_num
  have hpowone : (1 : ℝ) ≤ (N : ℝ) ^ (19 / 39 : ℝ) :=
    Real.one_le_rpow hNone (by norm_num)
  have htarget :
      ((correctedChenY N * R ^ 2 : ℕ) : ℝ) + 1 ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ B := by
    rw [le_div_iff₀ hlogpowpos]
    calc
      (((correctedChenY N * R ^ 2 : ℕ) : ℝ) + 1) *
          Real.log (N : ℝ) ^ B ≤
          (2 * (N : ℝ) ^ (19 / 39 : ℝ) + 1) *
            Real.log (N : ℝ) ^ B := by gcongr
      _ ≤ (3 * (N : ℝ) ^ (19 / 39 : ℝ)) *
            Real.log (N : ℝ) ^ B := by
        gcongr
        nlinarith
      _ ≤ (3 * (N : ℝ) ^ (19 / 39 : ℝ)) *
            ((1 / 3 : ℝ) * (N : ℝ) ^ (1 / 78 : ℝ)) := by
        gcongr
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          (3 * (N : ℝ) ^ (19 / 39 : ℝ)) *
              ((1 / 3 : ℝ) * (N : ℝ) ^ (1 / 78 : ℝ)) =
              (N : ℝ) ^ (19 / 39 : ℝ) *
                (N : ℝ) ^ (1 / 78 : ℝ) := by ring
          _ = (N : ℝ) ^ ((19 / 39 : ℝ) + 1 / 78) :=
            Real.rpow_add hNpos _ _ |>.symm
          _ = (N : ℝ) ^ (1 / 2 : ℝ) := by norm_num
  have hfloor :
      correctedChenY N * R ^ 2 + 1 ≤ q1LevelModulusCutoff N B := by
    unfold q1LevelModulusCutoff
    apply Nat.le_floor
    simpa only [Nat.cast_add, Nat.cast_one] using htarget
  have hYpos : 0 < correctedChenY N := by
    unfold correctedChenY
    positivity
  change R ≤ q1PanSelbergLevel B N
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le hYpos).mpr
  have hmul : correctedChenY N * R ^ 2 ≤ q1LevelModulusCutoff N B := by omega
  simpa [mul_comm] using hmul

/-- The cutoff-failure carrier is identically empty at the canonical level. -/
theorem q1LevelCutoffFailureSwitchingPrimes_panSelbergLevel_eq_empty
    (N B : ℕ) :
    q1LevelCutoffFailureSwitchingPrimes N B (q1PanSelbergLevel B N) = ∅ := by
  ext q
  constructor
  · intro hq
    rcases mem_q1LevelCutoffFailureSwitchingPrimes.mp hq with
      ⟨hqSwitch, _, hqLarge⟩
    exact (Nat.not_lt_of_ge
      (q1PanSelbergLevel_modulus_le_cutoff N B q hqSwitch) hqLarge).elim
  · simp

/-- The three switching carriers form an exact finite partition. -/
theorem q1LevelSwitchingPrimes_partition (N B L : ℕ) :
    (q1LevelGoodSwitchingPrimes N B L ∪
      q1LevelNonreducedSwitchingPrimes N B L) ∪
        q1LevelCutoffFailureSwitchingPrimes N B L =
      q1SwitchingPrimes N := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_union.mp hq with hq | hq
      · exact (mem_q1LevelGoodSwitchingPrimes.mp hq).1
      · exact (mem_q1LevelNonreducedSwitchingPrimes.mp hq).1
    · exact (mem_q1LevelCutoffFailureSwitchingPrimes.mp hq).1
  · intro hq
    by_cases hqN : q ∣ N
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr <|
          mem_q1LevelNonreducedSwitchingPrimes.mpr ⟨hq, hqN⟩
    · by_cases hcut : q * L ^ 2 ≤ q1LevelModulusCutoff N B
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            mem_q1LevelGoodSwitchingPrimes.mpr ⟨hq, hqN, hcut⟩
      · exact Finset.mem_union.mpr <| Or.inr <|
          mem_q1LevelCutoffFailureSwitchingPrimes.mpr
            ⟨hq, hqN, Nat.lt_of_not_ge hcut⟩

/-- The three finite switching carriers are pairwise disjoint. -/
theorem q1LevelSwitchingCarriers_pairwise_disjoint (N B L : ℕ) :
    Disjoint (q1LevelGoodSwitchingPrimes N B L)
      (q1LevelNonreducedSwitchingPrimes N B L) ∧
    Disjoint (q1LevelGoodSwitchingPrimes N B L)
      (q1LevelCutoffFailureSwitchingPrimes N B L) ∧
    Disjoint (q1LevelNonreducedSwitchingPrimes N B L)
      (q1LevelCutoffFailureSwitchingPrimes N B L) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hgood hnonred
    exact (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.1
      (mem_q1LevelNonreducedSwitchingPrimes.mp hnonred).2
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hgood hfail
    exact (Nat.not_lt_of_ge (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.2)
      (mem_q1LevelCutoffFailureSwitchingPrimes.mp hfail).2.2
  · apply Finset.disjoint_left.mpr
    intro q hnonred hfail
    exact (mem_q1LevelCutoffFailureSwitchingPrimes.mp hfail).2.1
      (mem_q1LevelNonreducedSwitchingPrimes.mp hnonred).2

/-- Every progression modulus in the good square lies below the explicit
cutoff. -/
theorem q1LevelGood_modulus_le_cutoff
    {N B L q d1 d2 : ℕ} (hq : q.Prime)
    (hgood : q ∈ q1LevelGoodSwitchingPrimes N B L)
    (hd1 : d1 ∈ q1LevelCarrier N L) (hd2 : d2 ∈ q1LevelCarrier N L) :
    Nat.lcm q (Nat.lcm d1 d2) ≤ q1LevelModulusCutoff N B := by
  have hPpos : 0 < correctedChenSiftingProduct N :=
    Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
  have hd1P : d1 ∣ correctedChenSiftingProduct N :=
    (mem_q1LevelCarrier.mp hd1).1
  have hd2P : d2 ∣ correctedChenSiftingProduct N :=
    (mem_q1LevelCarrier.mp hd2).1
  have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1P hPpos
  have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2P hPpos
  have hlcmpos : 0 < Nat.lcm d1 d2 := Nat.lcm_pos hd1pos hd2pos
  have hinner : Nat.lcm d1 d2 ≤ L ^ 2 := by
    calc
      Nat.lcm d1 d2 ≤ d1 * d2 := Nat.lcm_le_mul hd1pos hd2pos
      _ ≤ L * L := Nat.mul_le_mul (mem_q1LevelCarrier.mp hd1).2
        (mem_q1LevelCarrier.mp hd2).2
      _ = L ^ 2 := by ring
  calc
    Nat.lcm q (Nat.lcm d1 d2) ≤ q * Nat.lcm d1 d2 :=
      Nat.lcm_le_mul hq.pos hlcmpos
    _ ≤ q * L ^ 2 := Nat.mul_le_mul_left q hinner
    _ ≤ q1LevelModulusCutoff N B :=
      (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.2

/-- Every good progression has the reduced residue `N mod m` required by the
Pan distribution error. -/
theorem q1LevelGood_residue_coprime
    {N B L q d1 d2 : ℕ} (hq : q.Prime)
    (hqz : correctedChenZ N ≤ q)
    (hgood : q ∈ q1LevelGoodSwitchingPrimes N B L)
    (hd1 : d1 ∈ q1LevelCarrier N L) (hd2 : d2 ∈ q1LevelCarrier N L) :
    (N % Nat.lcm q (Nat.lcm d1 d2)).Coprime
      (Nat.lcm q (Nat.lcm d1 d2)) := by
  let l := Nat.lcm d1 d2
  let m := Nat.lcm q l
  have hlP : l ∣ correctedChenSiftingProduct N := by
    dsimp [l]
    exact Nat.lcm_dvd (mem_q1LevelCarrier.mp hd1).1
      (mem_q1LevelCarrier.mp hd2).1
  have hlN : l.Coprime N :=
    Nat.Coprime.coprime_dvd_left hlP (coprime_siftingProduct_N N)
  have hqN : q.Coprime N :=
    hq.coprime_iff_not_dvd.mpr (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.1
  have hql : q.Coprime l :=
    Nat.Coprime.coprime_dvd_right hlP (coprime_q_siftingProduct hq hqz)
  have hmN : m.Coprime N := by
    dsimp [m]
    rw [Nat.Coprime.lcm_eq_mul hql]
    exact Nat.coprime_mul_iff_left.mpr ⟨hqN, hlN⟩
  change (N % m).Coprime m
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec m N]
  exact hmN.gcd_eq_one

/-- Good switching moduli are exactly the moduli to which the reduced-residue
cutoff-supported Pan aggregate applies. -/
theorem q1LevelGood_modulus_admissible
    {N B L q d1 d2 : ℕ}
    (hgood : q ∈ q1LevelGoodSwitchingPrimes N B L)
    (hd1 : d1 ∈ q1LevelCarrier N L) (hd2 : d2 ∈ q1LevelCarrier N L) :
    Nat.lcm q (Nat.lcm d1 d2) ≤ q1LevelModulusCutoff N B ∧
      (N % Nat.lcm q (Nat.lcm d1 d2)).Coprime
        (Nat.lcm q (Nat.lcm d1 d2)) := by
  have hswitch : q ∈ q1SwitchingPrimes N :=
    (mem_q1LevelGoodSwitchingPrimes.mp hgood).1
  rw [q1SwitchingPrimes, Finset.mem_filter] at hswitch
  rcases hswitch with ⟨_, hqprime, hqz⟩
  exact ⟨q1LevelGood_modulus_le_cutoff hqprime hgood hd1 hd2,
    q1LevelGood_residue_coprime hqprime hqz hgood hd1 hd2⟩

/-- Every nonzero term in the divisor-weighted Pan majorant has a reduced
residue and final modulus below the advertised cutoff. -/
theorem q1LevelWeightedBV_modulus_admissible
    {N B L q m : ℕ} (hgood : q ∈ q1LevelGoodSwitchingPrimes N B L)
    (hm : m ∈ (correctedChenSiftingProduct N).divisors)
    (hmL : m ≤ L ^ 2) :
    Nat.lcm q m ≤ q1LevelModulusCutoff N B ∧
      (N % Nat.lcm q m).Coprime (Nat.lcm q m) := by
  have hswitch : q ∈ q1SwitchingPrimes N :=
    (mem_q1LevelGoodSwitchingPrimes.mp hgood).1
  rw [q1SwitchingPrimes, Finset.mem_filter] at hswitch
  rcases hswitch with ⟨_, hqprime, hqz⟩
  have hmP : m ∣ correctedChenSiftingProduct N :=
    (Nat.mem_divisors.mp hm).1
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmP
    (Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N))
  have hqm : q.Coprime m :=
    Nat.Coprime.coprime_dvd_right hmP (coprime_q_siftingProduct hqprime hqz)
  have hqN : q.Coprime N := hqprime.coprime_iff_not_dvd.mpr
    (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.1
  have hmN : m.Coprime N :=
    Nat.Coprime.coprime_dvd_left hmP (coprime_siftingProduct_N N)
  constructor
  · calc
      Nat.lcm q m ≤ q * m := Nat.lcm_le_mul hqprime.pos hmpos
      _ ≤ q * L ^ 2 := Nat.mul_le_mul_left q hmL
      _ ≤ q1LevelModulusCutoff N B :=
        (mem_q1LevelGoodSwitchingPrimes.mp hgood).2.2
  · have hlcmN : (Nat.lcm q m).Coprime N := by
      rw [Nat.Coprime.lcm_eq_mul hqm]
      exact Nat.coprime_mul_iff_left.mpr ⟨hqN, hmN⟩
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec (Nat.lcm q m) N]
    exact hlcmN.gcd_eq_one

/-- The good portion of the q¹ count is bounded by the corresponding
level-supported squares. -/
noncomputable def q1LevelGoodSquareAggregate
    (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L, q1LevelSquareMajorant N L W q

/-- The signed reduced-residue Pan aggregate.  Absolute value is intentionally
outside the complete weighted aggregate in the analytic input below. -/
noncomputable def q1LevelSignedPanAggregate
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
    ∑ d1 ∈ q1LevelCarrier N L,
      ∑ d2 ∈ q1LevelCarrier N L,
        W.lambda d1 * W.lambda d2 *
          q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))

/-- The source-shaped weighted Pan/BV majorant: absolute values are taken after
the complete lambda-pair sum for each switching prime, and only then summed.
In particular, the analytic input cannot use cancellation between distinct
switching fibres. -/
noncomputable def q1LevelWeightedPanMajorant
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
    |∑ d1 ∈ q1LevelCarrier N L,
      ∑ d2 ∈ q1LevelCarrier N L,
        W.lambda d1 * W.lambda d2 *
          q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))|

/-- The source-shaped majorant controls the absolute value of the total signed
Pan contribution without assuming cancellation between switching primes. -/
theorem abs_q1LevelSignedPanAggregate_le_weightedPanMajorant
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    |q1LevelSignedPanAggregate κ N B L W| ≤
      q1LevelWeightedPanMajorant κ N B L W := by
  unfold q1LevelSignedPanAggregate q1LevelWeightedPanMajorant
  exact Finset.abs_sum_le_sum_abs _ _

/-- The cutoff-supported divisor-weighted Pan majorant.  The factor
`3 ^ ω(m)` is exactly the lcm-fibre multiplicity for two divisors of the
squarefree sifting product.  This is the standard weighted form supplied by
Pan's weighted mean-value theorem; unlike the old
diagnostic sum, every final modulus is level-supported. -/
noncomputable def q1LevelReducedResiduePanMajorant
    (κ : ℝ) (N B L : ℕ) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
    ∑ m ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ m.primeFactors.card *
        if m ≤ L ^ 2 then
          |q1TrueLiAPError κ N (Nat.lcm q m)|
        else 0

/-- Bounded level weights reduce the source-shaped lambda-pair error to the
canonical `3 ^ ω(m)` divisor-weighted Pan majorant. -/
theorem q1LevelWeightedPanMajorant_le_reducedResiduePanMajorant
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    q1LevelWeightedPanMajorant κ N B L W ≤
      q1LevelReducedResiduePanMajorant κ N B L := by
  classical
  unfold q1LevelWeightedPanMajorant q1LevelReducedResiduePanMajorant
  apply Finset.sum_le_sum
  intro q hq
  let P := correctedChenSiftingProduct N
  let f : ℕ → ℝ := fun m =>
    if m ≤ L ^ 2 then
      |q1TrueLiAPError κ N (Nat.lcm q m)|
    else 0
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact correctedChenSiftingProduct_ne_zero N
  have hPsq : Squarefree P := by
    dsimp [P]
    exact correctedChenSiftingProduct_squarefree N
  have hsub : q1LevelCarrier N L ⊆ P.divisors := by
    intro d hd
    dsimp [P]
    exact (Finset.mem_filter.mp hd).1
  have hpair :
      (∑ d1 ∈ q1LevelCarrier N L,
        ∑ d2 ∈ q1LevelCarrier N L, f (Nat.lcm d1 d2)) ≤
        ∑ m ∈ P.divisors, (3 : ℝ) ^ m.primeFactors.card * f m := by
    calc
      (∑ d1 ∈ q1LevelCarrier N L,
          ∑ d2 ∈ q1LevelCarrier N L, f (Nat.lcm d1 d2)) ≤
          ∑ d1 ∈ q1LevelCarrier N L,
            ∑ d2 ∈ P.divisors, f (Nat.lcm d1 d2) := by
        apply Finset.sum_le_sum
        intro d1 hd1
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro d2 hd2P hd2L
        dsimp [f]
        positivity
      _ ≤ ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, f (Nat.lcm d1 d2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro d1 hd1P hd1L
        exact Finset.sum_nonneg fun d2 hd2 => by
          dsimp [f]
          positivity
      _ = ∑ m ∈ P.divisors, (3 : ℝ) ^ m.primeFactors.card * f m :=
        (AnalyticNumberTheory.Sieve.lcmPairWeightedSum P hPsq f).symm
  calc
    |∑ d1 ∈ q1LevelCarrier N L,
        ∑ d2 ∈ q1LevelCarrier N L,
          W.lambda d1 * W.lambda d2 *
            q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))| ≤
        ∑ d1 ∈ q1LevelCarrier N L,
          |∑ d2 ∈ q1LevelCarrier N L,
            W.lambda d1 * W.lambda d2 *
              q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ q1LevelCarrier N L,
        ∑ d2 ∈ q1LevelCarrier N L,
          |W.lambda d1 * W.lambda d2 *
            q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))| := by
      apply Finset.sum_le_sum
      intro d1 hd1
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ q1LevelCarrier N L,
        ∑ d2 ∈ q1LevelCarrier N L,
          |q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))| := by
      apply Finset.sum_le_sum
      intro d1 hd1
      apply Finset.sum_le_sum
      intro d2 hd2
      rw [abs_mul, abs_mul]
      have hprod : |W.lambda d1| * |W.lambda d2| ≤ 1 := by
        nlinarith [W.abs_le_one d1, W.abs_le_one d2, abs_nonneg (W.lambda d1),
          abs_nonneg (W.lambda d2)]
      exact mul_le_of_le_one_left (abs_nonneg _) hprod
    _ = ∑ d1 ∈ q1LevelCarrier N L,
       ∑ d2 ∈ q1LevelCarrier N L, f (Nat.lcm d1 d2) := by
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      rw [show f (Nat.lcm d1 d2) =
       |q1TrueLiAPError κ N (Nat.lcm q (Nat.lcm d1 d2))| by
       simp [f, q1LevelCarrier_lcm_le_square hd1 hd2]]
    _ ≤ ∑ m ∈ P.divisors, (3 : ℝ) ^ m.primeFactors.card * f m := hpair
    _ = ∑ m ∈ (correctedChenSiftingProduct N).divisors,
       (3 : ℝ) ^ m.primeFactors.card *
         if m ≤ L ^ 2 then
           |q1TrueLiAPError κ N (Nat.lcm q m)|
         else 0 := by
      rfl

/-- The genuine `li(N-2)/φ(m)` main term paired with the good
level-supported square. -/
noncomputable def q1LevelMainAggregate
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
    ∑ d1 ∈ q1LevelCarrier N L,
      ∑ d2 ∈ q1LevelCarrier N L,
        W.lambda d1 * W.lambda d2 *
          (LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) /
            Nat.totient (Nat.lcm q (Nat.lcm d1 d2)))

/-- The level-truncated Selberg quadratic form occurring after the switching
prime is split from the Euler totient. -/
noncomputable def q1LevelSelbergQuadratic
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) : ℝ :=
  ∑ d1 ∈ q1LevelCarrier N L,
    ∑ d2 ∈ q1LevelCarrier N L,
      W.lambda d1 * W.lambda d2 /
        Nat.totient (Nat.lcm d1 d2)

private theorem q1FullTotientQuadratic_eq_mainSum
    (N : ℕ) (lambda : ℕ → ℝ) :
    (∑ d1 ∈ (correctedChenSiftingProduct N).divisors,
      ∑ d2 ∈ (correctedChenSiftingProduct N).divisors,
        lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2)) =
      (q1LevelBoundingSieve N).mainSum
        (BoundingSieve.lambdaSquared lambda) := by
  let S := q1LevelBoundingSieve N
  have hPpos : 0 < correctedChenSiftingProduct N :=
    Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
  symm
  calc
    S.mainSum (BoundingSieve.lambdaSquared lambda) =
        ∑ d1 ∈ (correctedChenSiftingProduct N).divisors,
          ∑ d2 ∈ (correctedChenSiftingProduct N).divisors,
            S.nu d1 * lambda d1 * S.nu d2 * lambda d2 *
              (S.nu (Nat.gcd d1 d2))⁻¹ := by
      simpa [S, q1LevelBoundingSieve] using
        (BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul
          (s := S) lambda)
    _ = ∑ d1 ∈ (correctedChenSiftingProduct N).divisors,
          ∑ d2 ∈ (correctedChenSiftingProduct N).divisors,
            lambda d1 * lambda d2 / Nat.totient (Nat.lcm d1 d2) := by
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      have hd1P : d1 ∣ correctedChenSiftingProduct N :=
        (Nat.mem_divisors.mp hd1).1
      have hd2P : d2 ∣ correctedChenSiftingProduct N :=
        (Nat.mem_divisors.mp hd2).1
      have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1P hPpos
      have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2P hPpos
      have hgcdP : Nat.gcd d1 d2 ∣ correctedChenSiftingProduct N :=
        (Nat.gcd_dvd_left d1 d2).trans hd1P
      have hnuGcd : S.nu (Nat.gcd d1 d2) ≠ 0 :=
        (S.nu_pos_of_dvd_prodPrimes hgcdP).ne'
      have hnuLcm :
          S.nu (Nat.lcm d1 d2) =
            S.nu d1 * S.nu d2 / S.nu (Nat.gcd d1 d2) :=
        S.nu_mult.map_lcm hnuGcd
      have hlcm0 : Nat.lcm d1 d2 ≠ 0 :=
        Nat.lcm_ne_zero hd1pos.ne' hd2pos.ne'
      have hrecip :
          S.nu (Nat.lcm d1 d2) =
            1 / Nat.totient (Nat.lcm d1 d2) := by
        simp [S, q1LevelBoundingSieve,
          LiuWeight.liuSelbergReciprocalTotient, hlcm0]
      calc
        S.nu d1 * lambda d1 * S.nu d2 * lambda d2 *
              (S.nu (Nat.gcd d1 d2))⁻¹ =
            lambda d1 * lambda d2 *
              (S.nu d1 * S.nu d2 / S.nu (Nat.gcd d1 d2)) := by ring
        _ = lambda d1 * lambda d2 * S.nu (Nat.lcm d1 d2) := by
          rw [← hnuLcm]
        _ = lambda d1 * lambda d2 /
              Nat.totient (Nat.lcm d1 d2) := by
          simp [hrecip, div_eq_mul_inv, mul_assoc, mul_comm]

private theorem q1FullTotientQuadratic_eq_levelQuadratic
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    (∑ d1 ∈ (correctedChenSiftingProduct N).divisors,
      ∑ d2 ∈ (correctedChenSiftingProduct N).divisors,
        W.lambda d1 * W.lambda d2 / Nat.totient (Nat.lcm d1 d2)) =
      q1LevelSelbergQuadratic N L W := by
  classical
  unfold q1LevelSelbergQuadratic q1LevelCarrier
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d1 hd1
  by_cases h1 : d1 ≤ L
  · simp only [h1, if_true]
    apply Finset.sum_congr rfl
    intro d2 hd2
    by_cases h2 : d2 ≤ L
    · simp [h2]
    · have hzero : W.lambda d2 = 0 := by
        by_contra hne
        exact h2 (mem_q1LevelCarrier.mp (W.support d2 hne)).2
      simp [h2, hzero]
  · have hzero : W.lambda d1 = 0 := by
      by_contra hne
      exact h1 (mem_q1LevelCarrier.mp (W.support d1 hne)).2
    simp [h1, hzero]

/-- The q¹ quadratic is exactly the abstract Selberg main sum, with no change of
carrier or local normalization. -/
theorem q1LevelSelbergQuadratic_eq_mainSum
    (N L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    q1LevelSelbergQuadratic N L W =
      (q1LevelBoundingSieve N).mainSum
        (BoundingSieve.lambdaSquared W.lambda) := by
  rw [← q1FullTotientQuadratic_eq_mainSum]
  exact (q1FullTotientQuadratic_eq_levelQuadratic N L W).symm

/-- The corrected-product optimal weight attains the reciprocal of the exact
truncated denominator. -/
theorem q1LevelSelbergQuadratic_optimal
    (N L : ℕ) (hL : 1 ≤ L) :
    q1LevelSelbergQuadratic N L (q1LevelOptimalSelbergWeight N L hL) =
      1 / q1LevelSelbergDenominator N L := by
  rw [q1LevelSelbergQuadratic_eq_mainSum]
  simpa [q1LevelOptimalSelbergWeight, q1LevelSelbergDenominator] using
    LiuWeight.mainSum_truncatedSelbergOptimalLambda
      (q1LevelBoundingSieve N) hL

/-- The exact reciprocal switching-prime factor in the q¹ main term. -/
noncomputable def q1LevelSwitchingReciprocalSum (N B L : ℕ) : ℝ :=
  ∑ q ∈ q1LevelGoodSwitchingPrimes N B L, 1 / ((q : ℝ) - 1)

private theorem q1_totient_lcm_switching_mul
    {N B L q d1 d2 : ℕ}
    (hq : q ∈ q1LevelGoodSwitchingPrimes N B L)
    (hd1 : d1 ∈ q1LevelCarrier N L)
    (hd2 : d2 ∈ q1LevelCarrier N L) :
    Nat.totient (Nat.lcm q (Nat.lcm d1 d2)) =
      (q - 1) * Nat.totient (Nat.lcm d1 d2) := by
  have hswitch := (mem_q1LevelGoodSwitchingPrimes.mp hq).1
  rw [q1SwitchingPrimes, Finset.mem_filter] at hswitch
  have hqprime : q.Prime := hswitch.2.1
  have hqz : correctedChenZ N ≤ q := hswitch.2.2
  have hd1P : d1 ∣ correctedChenSiftingProduct N :=
    (mem_q1LevelCarrier.mp hd1).1
  have hd2P : d2 ∣ correctedChenSiftingProduct N :=
    (mem_q1LevelCarrier.mp hd2).1
  have hlcmP : Nat.lcm d1 d2 ∣ correctedChenSiftingProduct N :=
    Nat.lcm_dvd hd1P hd2P
  have hcop : Nat.Coprime q (Nat.lcm d1 d2) :=
    (coprime_q_siftingProduct hqprime hqz).coprime_dvd_right hlcmP
  rw [hcop.lcm_eq_mul, Nat.totient_mul hcop, Nat.totient_prime hqprime]

/-- Exact main-factor algebra.  No asymptotic replacement is made: the genuine
`li_kappa(N - 2)`, the finite switching-prime reciprocal sum, and the truncated
Selberg quadratic remain separate factors. -/
theorem q1LevelMainAggregate_eq_li_mul_reciprocalSum_mul_quadratic
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    q1LevelMainAggregate κ N B L W =
      LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) *
        q1LevelSwitchingReciprocalSum N B L *
          q1LevelSelbergQuadratic N L W := by
  classical
  let li := LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ)
  let Q := ∑ d1 ∈ q1LevelCarrier N L,
    ∑ d2 ∈ q1LevelCarrier N L,
      W.lambda d1 * W.lambda d2 / Nat.totient (Nat.lcm d1 d2)
  have hfibre : ∀ q ∈ q1LevelGoodSwitchingPrimes N B L,
      (∑ d1 ∈ q1LevelCarrier N L,
        ∑ d2 ∈ q1LevelCarrier N L,
          W.lambda d1 * W.lambda d2 *
            (li / Nat.totient (Nat.lcm q (Nat.lcm d1 d2)))) =
        (li * (1 / ((q : ℝ) - 1))) * Q := by
    intro q hq
    dsimp [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d1 hd1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d2 hd2
    rw [q1_totient_lcm_switching_mul hq hd1 hd2]
    have hqprime : q.Prime := by
      have hswitch := (mem_q1LevelGoodSwitchingPrimes.mp hq).1
      rw [q1SwitchingPrimes, Finset.mem_filter] at hswitch
      exact hswitch.2.1
    have hqsub : (q : ℝ) - 1 = (q - 1 : ℕ) := by
      rw [Nat.cast_sub hqprime.one_le, Nat.cast_one]
    have hqm1 : (q : ℝ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hqprime.ne_one)
    have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos
      (mem_q1LevelCarrier.mp hd1).1
      (Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N))
    have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos
      (mem_q1LevelCarrier.mp hd2).1
      (Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N))
    have hlcmpos : 0 < Nat.lcm d1 d2 := Nat.lcm_pos hd1pos hd2pos
    have hphi : (Nat.totient (Nat.lcm d1 d2) : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hlcmpos)
    rw [Nat.cast_mul, ← hqsub]
    field_simp [hqm1, hphi]
  unfold q1LevelMainAggregate q1LevelSwitchingReciprocalSum
    q1LevelSelbergQuadratic
  change (∑ q ∈ q1LevelGoodSwitchingPrimes N B L, _) =
    li * (∑ q ∈ q1LevelGoodSwitchingPrimes N B L, 1 / ((q : ℝ) - 1)) * Q
  calc
    (∑ q ∈ q1LevelGoodSwitchingPrimes N B L, _) =
        ∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
          (li * (1 / ((q : ℝ) - 1))) * Q := by
            apply Finset.sum_congr rfl
            exact hfibre
    _ = li * (∑ q ∈ q1LevelGoodSwitchingPrimes N B L,
          1 / ((q : ℝ) - 1)) * Q := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- For the explicit corrected-product optimizer, the q¹ main aggregate is the
exact switching-prime factor divided by the truncated Selberg denominator. -/
theorem q1LevelMainAggregate_optimal
    (κ : ℝ) (N B L : ℕ) (hL : 1 ≤ L) :
    q1LevelMainAggregate κ N B L (q1LevelOptimalSelbergWeight N L hL) =
      LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) *
        q1LevelSwitchingReciprocalSum N B L /
          q1LevelSelbergDenominator N L := by
  rw [q1LevelMainAggregate_eq_li_mul_reciprocalSum_mul_quadratic,
    q1LevelSelbergQuadratic_optimal]
  ring

/-- The good square is exactly its `li(N-2)/φ(m)` aggregate plus the signed
Pan aggregate. -/
theorem q1LevelGoodSquare_eq_main_add_signedPan
    (κ : ℝ) (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) (_hN : 2 ≤ N) :
    q1LevelGoodSquareAggregate N B L W =
      q1LevelMainAggregate κ N B L W + q1LevelSignedPanAggregate κ N B L W := by
  unfold q1LevelGoodSquareAggregate q1LevelMainAggregate q1LevelSignedPanAggregate
  simp_rw [q1LevelSquareMajorant_eq_expanded]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d1 hd1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d2 hd2
  rw [← mul_add]
  congr 1
  unfold q1TrueLiAPError
  ring

/-- The non-reduced residual is a sum of the actual candidate AP counts, not a
truncation obtained by deleting terms from `q1ErrorTermSum`. -/
noncomputable def q1LevelNonreducedResidual (N B L : ℕ) : ℝ :=
  ∑ q ∈ q1LevelNonreducedSwitchingPrimes N B L, q1CandidateAPCount N q

/-- A non-reduced switching fibre contains at most the single prime `p = q`:
from `q ∣ N` and `q ∣ N - p` one gets `q ∣ p`, and both are prime. -/
theorem q1CandidateAPCount_le_one_of_prime_dvd
    {N q : ℕ} (hqprime : q.Prime) (hqN : q ∣ N) :
    q1CandidateAPCount N q ≤ 1 := by
  unfold q1CandidateAPCount
  have hcard :
      ((correctedChenCandidates N).filter (fun p => q ∣ N - p)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp r hr
    have hpprime : p.Prime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hrprime : r.Prime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1
    have hpN : p < N :=
      Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    have hrN : r < N :=
      Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
    have hqp : q ∣ p := by
      have h := Nat.dvd_sub hqN (Finset.mem_filter.mp hp).2
      have heq : N - (N - p) = p := by omega
      rw [heq] at h
      exact h
    have hqr : q ∣ r := by
      have h := Nat.dvd_sub hqN (Finset.mem_filter.mp hr).2
      have heq : N - (N - r) = r := by omega
      rw [heq] at h
      exact h
    exact ((Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hqp).symm.trans
      ((Nat.prime_dvd_prime_iff_eq hqprime hrprime).mp hqr)
  exact_mod_cast hcard

/-- The complete non-reduced residual is bounded by the number of non-reduced
switching primes.  This records the exact elementary correction before any
asymptotic estimate of that cardinality. -/
theorem q1LevelNonreducedResidual_le_card (N B L : ℕ) :
    q1LevelNonreducedResidual N B L ≤
      (q1LevelNonreducedSwitchingPrimes N B L).card := by
  unfold q1LevelNonreducedResidual
  calc
    (∑ q ∈ q1LevelNonreducedSwitchingPrimes N B L,
        q1CandidateAPCount N q) ≤
        ∑ q ∈ q1LevelNonreducedSwitchingPrimes N B L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hswitch := (mem_q1LevelNonreducedSwitchingPrimes.mp hq).1
      rw [q1SwitchingPrimes, Finset.mem_filter] at hswitch
      exact q1CandidateAPCount_le_one_of_prime_dvd hswitch.2.1
        (mem_q1LevelNonreducedSwitchingPrimes.mp hq).2
    _ = (q1LevelNonreducedSwitchingPrimes N B L).card := by simp

/-- The non-reduced residual is already power-saving: it has at most as many
terms as the switching range, and `Y ≤ 2 N^(1/3)`. -/
theorem q1LevelNonreducedResidual_le_two_mul_rpow_one_third
    (N B L : ℕ) (hN : 1 ≤ N) :
    q1LevelNonreducedResidual N B L ≤
      2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hcard :
      (q1LevelNonreducedSwitchingPrimes N B L).card ≤ correctedChenY N := by
    calc
      (q1LevelNonreducedSwitchingPrimes N B L).card ≤
          (q1SwitchingPrimes N).card := by
        unfold q1LevelNonreducedSwitchingPrimes
        exact Finset.card_filter_le _ _
      _ ≤ correctedChenY N := by
        unfold q1SwitchingPrimes
        exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    q1LevelNonreducedResidual N B L ≤
        ((q1LevelNonreducedSwitchingPrimes N B L).card : ℝ) :=
      q1LevelNonreducedResidual_le_card N B L
    _ ≤ (correctedChenY N : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) :=
      correctedChenY_le_two_mul_root N hN

/-- The cutoff-failure residual is likewise an actual q¹ candidate count. -/
noncomputable def q1LevelCutoffResidual (N B L : ℕ) : ℝ :=
  ∑ q ∈ q1LevelCutoffFailureSwitchingPrimes N B L, q1CandidateAPCount N q

/-- The corrected q¹ count is bounded by the good Selberg square plus the two
honest residual count sums. -/
theorem correctedChenQ1Count_le_levelSquare_add_residuals
    (N B L : ℕ) (W : Q1LevelSupportedSelbergWeight N L) :
    correctedChenQ1Count N ≤
      q1LevelGoodSquareAggregate N B L W +
        q1LevelNonreducedResidual N B L + q1LevelCutoffResidual N B L := by
  classical
  have hpair := q1LevelSwitchingCarriers_pairwise_disjoint N B L
  have hgood_nonred := hpair.1
  have hgood_failure := hpair.2.1
  have hnonred_failure := hpair.2.2
  have hunion_failure :
      Disjoint
        (q1LevelGoodSwitchingPrimes N B L ∪
          q1LevelNonreducedSwitchingPrimes N B L)
        (q1LevelCutoffFailureSwitchingPrimes N B L) := by
    apply Finset.disjoint_left.mpr
    intro q hq hfailure
    rcases Finset.mem_union.mp hq with hgood | hnonred
    · exact (Finset.disjoint_left.mp hgood_failure) hgood hfailure
    · exact (Finset.disjoint_left.mp hnonred_failure) hnonred hfailure
  rw [correctedChenQ1Count_eq_reindexed]
  change (∑ q ∈ q1SwitchingPrimes N, q1CandidateAPCount N q) ≤
    q1LevelGoodSquareAggregate N B L W +
      q1LevelNonreducedResidual N B L + q1LevelCutoffResidual N B L
  rw [← q1LevelSwitchingPrimes_partition N B L,
    Finset.sum_union hunion_failure, Finset.sum_union hgood_nonred]
  unfold q1LevelGoodSquareAggregate q1LevelNonreducedResidual q1LevelCutoffResidual
  apply add_le_add
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro q hq
      exact q1CandidateAPCount_le_levelSquareMajorant W
        (mem_q1LevelGoodSwitchingPrimes.mp hq).1
    · exact le_rfl
  · exact le_rfl

/-- The exact final-margin budget for the q¹ Selberg main coefficient after the
printed `3.94033 / 2` contribution and the two half-unit residual allowances are
reserved. -/
noncomputable def q1FinalSelbergMainCoefficientBudget : ℝ :=
  20 / 3 - 3.94033 / 2 - 1

lemma q1FinalSelbergMainCoefficientBudget_pos :
    0 < q1FinalSelbergMainCoefficientBudget := by
  norm_num [q1FinalSelbergMainCoefficientBudget]

/-- A concrete sharp coefficient strictly inside the final numerical budget. -/
noncomputable def q1TargetSelbergMainCoefficient : ℝ := 3.69

lemma q1TargetSelbergMainCoefficient_pos :
    0 < q1TargetSelbergMainCoefficient := by
  norm_num [q1TargetSelbergMainCoefficient]

lemma q1TargetSelbergMainCoefficient_lt_budget :
    q1TargetSelbergMainCoefficient <
      q1FinalSelbergMainCoefficientBudget := by
  norm_num [q1TargetSelbergMainCoefficient,
    q1FinalSelbergMainCoefficientBudget]

/-- The coefficient forced by the fixed Pan level after normalizing by the
truncated singular series.  Indeed, `log (q1PanSelbergLevel B N) / log N`
tends to `1 / 12`, while the switching-prime reciprocal sum tends to
`log (10 / 3)`; the exact optimal denominator therefore contributes their
ratio. -/
noncomputable def q1PanFixedLevelAsymptoticCoefficient : ℝ :=
  12 * Real.log (10 / 3)

/-- The coefficient forced by the fixed Pan level is already larger than the
entire final main-term budget.  Consequently the `3.69` target cannot be
proved for `q1PanSelbergLevel`; a different level or switching architecture is
required. -/
theorem q1FinalSelbergMainCoefficientBudget_lt_panFixedLevel :
    q1FinalSelbergMainCoefficientBudget <
      q1PanFixedLevelAsymptoticCoefficient := by
  have hlog : 1 < Real.log (10 / 3) := by
    rw [← Real.exp_lt_exp]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 10 / 3)]
    exact Real.exp_one_lt_three.trans (by norm_num)
  norm_num [q1FinalSelbergMainCoefficientBudget,
    q1PanFixedLevelAsymptoticCoefficient] at *
  linarith

/-- In particular, the explicit sharp target is smaller than the coefficient
forced by the fixed Pan level. -/
theorem q1TargetSelbergMainCoefficient_lt_panFixedLevel :
    q1TargetSelbergMainCoefficient <
      q1PanFixedLevelAsymptoticCoefficient :=
  q1TargetSelbergMainCoefficient_lt_budget.trans
    q1FinalSelbergMainCoefficientBudget_lt_panFixedLevel

/-- The sole scalar estimate still required after the explicit optimal weight
construction.  It keeps `li_kappa`, the exact finite reciprocal prime sum, the
corrected denominator, and the truncated singular-series normalization in their
native forms. -/
def Q1SharpLevelSelbergMainBound
    (κ : ℝ) (B : ℕ) (level : ℕ → ℕ) (cMain : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ hL : 1 ≤ level N,
      LiuWeight.liuLogarithmicIntegral κ (N - 2 : ℝ) *
          q1LevelSwitchingReciprocalSum N B (level N) /
            q1LevelSelbergDenominator N (level N) ≤
        cMain * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

/-- The finite upper-sieve input: after selecting a level-supported Selberg
weight, its main aggregate has the expected q¹-scale upper bound.  The theorem
above shows that only the named scalar estimate remains; weight existence and
finite minimization are unconditional. -/
def Q1LevelSupportedUpperSieveInput
    (κ : ℝ) (B : ℕ) (level : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ W : Q1LevelSupportedSelbergWeight N (level N),
      q1LevelMainAggregate κ N B (level N) W ≤
        C * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

/-- The scalar sharp bound supplies the original upper-sieve producer with the
canonical corrected-product optimizer and the same named coefficient. -/
theorem Q1SharpLevelSelbergMainBound.to_upperSieveInput
    {κ cMain : ℝ} {B : ℕ} {level : ℕ → ℕ}
    (hcMain : 0 < cMain)
    (hMain : Q1SharpLevelSelbergMainBound κ B level cMain) :
    Q1LevelSupportedUpperSieveInput κ B level := by
  obtain ⟨N₀, hN₀⟩ := hMain
  refine ⟨cMain, hcMain, N₀, ?_⟩
  intro N hN hNeven
  obtain ⟨hL, hMainN⟩ := hN₀ N hN hNeven
  refine ⟨q1LevelOptimalSelbergWeight N (level N) hL, ?_⟩
  rw [q1LevelMainAggregate_optimal]
  exact hMainN

/-- The sole published distributional input in this reduction: the
`a = 1` specialization of Pan's `3 ^ ω` mean-value theorem, with reduced
residues and cutoff-supported final moduli.  Its quantifiers have the published
order `∀ A > 0, ∃ B = B(A)` (Liu 2022, `th-mvt`, lines 137--151).  The finite
theorem above proves that this is exactly the weight needed for the Selberg
lambda-pair expansion; no unrestricted positive error sum is truncated. -/
def Q1ReducedResidueWeightedPanInput (κ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ∀ L : ℕ,
      q1LevelReducedResiduePanMajorant κ N B L ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A

/-- The separate non-reduced correction required because a switching prime may
divide `N`; it is deliberately not set to zero in the Pan aggregate. -/
def Q1NonreducedResidualInput (B : ℕ) (level : ℕ → ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      q1LevelNonreducedResidual N B (level N) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A

/-- The non-reduced input is unconditional, uniformly in the chosen level:
the elementary `N^(1/3)` bound is smaller than every `N / log(N)^A` scale. -/
theorem q1NonreducedResidualInput (B : ℕ) (level : ℕ → ℕ) :
    Q1NonreducedResidualInput B level := by
  intro A _hA
  refine ⟨2, by norm_num, ?_⟩
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ A ≤ x ^ (2 / 3 : ℝ) := by
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop A
        (by norm_num : (0 : ℝ) < 2 / 3)).bound
          (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) A),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) (2 / 3)),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ A ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases Filter.eventually_atTop.mp hnat with ⟨N₁, hN₁⟩
  refine ⟨max N₁ 2, ?_⟩
  intro N hN _hEven
  have hgrowth := hN₁ N (by omega)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdenom : 0 < Real.log (N : ℝ) ^ A :=
    Real.rpow_pos_of_pos hlogpos A
  have hcombine :
      (N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ A ≤ N := by
    calc
      (N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ A ≤
          (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (1 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      _ = N := Real.rpow_one _
  calc
    q1LevelNonreducedResidual N B (level N) ≤
        2 * (N : ℝ) ^ (1 / 3 : ℝ) :=
      q1LevelNonreducedResidual_le_two_mul_rpow_one_third N B (level N) (by omega)
    _ ≤ 2 * N / Real.log N ^ A := by
      rw [le_div_iff₀ hdenom]
      calc
        (2 * (N : ℝ) ^ (1 / 3 : ℝ)) * Real.log N ^ A =
            2 * ((N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ A) := by ring
        _ ≤ 2 * N := mul_le_mul_of_nonneg_left hcombine (by norm_num)

/-- A valid level selection keeps every reduced switching fibre inside the
distribution range.  Thus the cutoff-failure residual is eventually empty,
rather than assumed small after discarding whole fibres. -/
def Q1CutoffAdmissibleLevel (B : ℕ) (level : ℕ → ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∀ q ∈ q1SwitchingPrimes N, ¬ q ∣ N →
      q * (level N) ^ 2 ≤ q1LevelModulusCutoff N B

/-- The selected fixed q¹ Selberg level is Pan-admissible for every exponent `B`. -/
theorem q1PanSelbergLevel_cutoffAdmissible (B : ℕ) :
    Q1CutoffAdmissibleLevel B (q1PanSelbergLevel B) := by
  refine ⟨0, ?_⟩
  intro N _hN _hEven q hq _hqN
  exact q1PanSelbergLevel_modulus_le_cutoff N B q hq

/-- An admissible level makes the actual cutoff-failure count vanish. -/
theorem q1LevelCutoffResidual_eq_zero_of_admissible
    {B : ℕ} {level : ℕ → ℕ} (hlevel : Q1CutoffAdmissibleLevel B level) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      q1LevelCutoffResidual N B (level N) = 0 := by
  rcases hlevel with ⟨N₀, hlevel⟩
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  unfold q1LevelCutoffResidual
  apply Finset.sum_eq_zero
  intro q hq
  exfalso
  rcases mem_q1LevelCutoffFailureSwitchingPrimes.mp hq with
    ⟨hqSwitch, hqN, hqLarge⟩
  exact (Nat.not_lt_of_ge (hlevel N hN hEven q hqSwitch hqN)) hqLarge

/-- The level-supported weighted q¹ aggregate theorem contains exactly the two
genuine analytic inputs.  The explicit level is cutoff-admissible and its
non-reduced residual is power-saving by the unconditional theorems above. -/
def Q1WeightedAggregateTheorem : Prop :=
  ∃ κ : ℝ,
    (∀ B : ℕ, Q1LevelSupportedUpperSieveInput κ B (q1PanSelbergLevel B)) ∧
    Q1ReducedResidueWeightedPanInput κ

abbrev Q1LevelSupportedWeightedAggregateTheorem : Prop :=
  Q1WeightedAggregateTheorem

/-- Package the two genuine analytic producer inputs. -/
theorem q1LevelSupportedWeightedAggregate_of_inputs
    (κ : ℝ)
    (hSieve : ∀ B : ℕ,
      Q1LevelSupportedUpperSieveInput κ B (q1PanSelbergLevel B))
    (hPan : Q1ReducedResidueWeightedPanInput κ) :
    Q1WeightedAggregateTheorem :=
  ⟨κ, hSieve, hPan⟩

/-- The source-faithful producer contract implies exactly the q¹ count estimate
used downstream.  The proof uses the finite square expansion, the
`∀ A ∃ B(A)` reduced-residue majorant, the exact non-reduced count, and an
eventually empty cutoff-failure carrier. -/
theorem hq1_of_weightedAggregate
    (hAggregate : Q1WeightedAggregateTheorem) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  rcases hAggregate with ⟨κ, hSieve, hPan⟩
  let level : ℕ → ℕ → ℕ := q1PanSelbergLevel
  have hSieve' : ∀ B : ℕ,
      Q1LevelSupportedUpperSieveInput κ B (level B) := by
    simpa [level] using hSieve
  have hNonreduced : ∀ B : ℕ, Q1NonreducedResidualInput B (level B) :=
    fun B => q1NonreducedResidualInput B (level B)
  have hCutoff : ∀ B : ℕ, Q1CutoffAdmissibleLevel B (level B) := by
    intro B
    simpa [level] using q1PanSelbergLevel_cutoffAdmissible B
  rcases hPan 3 (by norm_num : (0 : ℝ) < 3) with
    ⟨B, CPan, hCPan, NPan, hPan⟩
  rcases hSieve' B with ⟨Cmain, hCmain, Nmain, hmain⟩
  rcases hNonreduced B 3 (by norm_num : (0 : ℝ) < 3) with
    ⟨CNonreduced, hCNonreduced, NNonreduced, hNonreduced⟩
  rcases q1LevelCutoffResidual_eq_zero_of_admissible (hCutoff B) with
    ⟨NCutoff, hCutoff⟩
  let Cerr : ℝ := CPan + CNonreduced
  rcases errLogCube_negligible Cerr with ⟨Nerr, hNerr⟩
  refine ⟨Cmain + 1 / 2, by positivity,
    max (max Nmain (max NPan (max NNonreduced (max NCutoff Nerr)))) 59049, ?_⟩
  intro N hN hEven
  have hNmain : Nmain ≤ N := by omega
  have hNPan : NPan ≤ N := by omega
  have hNNonreduced : NNonreduced ≤ N := by omega
  have hNCutoff : NCutoff ≤ N := by omega
  have hNerr' : Nerr ≤ N := by omega
  have hNlarge : 59049 ≤ N := by omega
  have hNtwo : 2 ≤ N := by omega
  rcases hmain N hNmain hEven with ⟨W, hmainN⟩
  have hPanRawN : q1LevelReducedResiduePanMajorant κ N B (level B N) ≤
      CPan * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 :=
    by simpa [Real.rpow_natCast] using hPan N hNPan hEven (level B N)
  have hPanN : |q1LevelSignedPanAggregate κ N B (level B N) W| ≤
      CPan * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 :=
    (abs_q1LevelSignedPanAggregate_le_weightedPanMajorant
      κ N B (level B N) W).trans <|
      (q1LevelWeightedPanMajorant_le_reducedResiduePanMajorant
        κ N B (level B N) W).trans hPanRawN
  have hNonreducedN : q1LevelNonreducedResidual N B (level B N) ≤
      CNonreduced * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 :=
    by simpa [Real.rpow_natCast] using hNonreduced N hNNonreduced hEven
  have hCutoffN : q1LevelCutoffResidual N B (level B N) = 0 :=
    hCutoff N hNCutoff hEven
  let 𝔖 : ℝ :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  let X : ℝ := (N : ℝ) / (Real.log (N : ℝ)) ^ 2
  have hmainN' : q1LevelMainAggregate κ N B (level B N) W ≤ Cmain * 𝔖 * X := by
    rw [show Cmain * 𝔖 * X =
      Cmain * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 by
      dsimp [𝔖, X]
      ring]
    exact hmainN
  have hresidualN :
      |q1LevelSignedPanAggregate κ N B (level B N) W| +
          q1LevelNonreducedResidual N B (level B N) +
            q1LevelCutoffResidual N B (level B N) ≤
        Cerr * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    rw [hCutoffN, add_zero]
    calc
      |q1LevelSignedPanAggregate κ N B (level B N) W| +
          q1LevelNonreducedResidual N B (level B N) ≤
          CPan * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 +
            CNonreduced * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 :=
        add_le_add hPanN hNonreducedN
      _ = Cerr * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
        dsimp [Cerr]
        ring
  have hErrCube : Cerr * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤
      (1 / 4 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
    hNerr N hNerr' hEven
  have h𝔖 : (1 / 2 : ℝ) ≤ 𝔖 := by
    dsimp [𝔖]
    exact singularSeriesTruncated_ge_half
      (correctedChenZ_sub_one_ge_two_of_large hNlarge)
  have hErrAbsorb : (1 / 4 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (1 / 2 : ℝ) * 𝔖 * X := by
    have hcoef : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 := by
      nlinarith [h𝔖]
    dsimp [X]
    calc
      (1 / 4 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 =
          (1 / 4 : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * 𝔖 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hcountN : correctedChenQ1Count N ≤
      q1LevelMainAggregate κ N B (level B N) W +
        |q1LevelSignedPanAggregate κ N B (level B N) W| +
          q1LevelNonreducedResidual N B (level B N) +
            q1LevelCutoffResidual N B (level B N) := by
    calc
      correctedChenQ1Count N ≤
          q1LevelGoodSquareAggregate N B (level B N) W +
            q1LevelNonreducedResidual N B (level B N) +
              q1LevelCutoffResidual N B (level B N) :=
        correctedChenQ1Count_le_levelSquare_add_residuals N B (level B N) W
      _ = (q1LevelMainAggregate κ N B (level B N) W +
          q1LevelSignedPanAggregate κ N B (level B N) W) +
            q1LevelNonreducedResidual N B (level B N) +
              q1LevelCutoffResidual N B (level B N) := by
        rw [q1LevelGoodSquare_eq_main_add_signedPan κ N B (level B N) W hNtwo]
      _ ≤ q1LevelMainAggregate κ N B (level B N) W +
          |q1LevelSignedPanAggregate κ N B (level B N) W| +
            q1LevelNonreducedResidual N B (level B N) +
              q1LevelCutoffResidual N B (level B N) := by
        gcongr
        exact le_abs_self _
  calc
    correctedChenQ1Count N ≤
        q1LevelMainAggregate κ N B (level B N) W +
          |q1LevelSignedPanAggregate κ N B (level B N) W| +
            q1LevelNonreducedResidual N B (level B N) +
              q1LevelCutoffResidual N B (level B N) := hcountN
    _ = q1LevelMainAggregate κ N B (level B N) W +
        (|q1LevelSignedPanAggregate κ N B (level B N) W| +
          q1LevelNonreducedResidual N B (level B N) +
            q1LevelCutoffResidual N B (level B N)) := by ring
    _ ≤ Cmain * 𝔖 * X + Cerr * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 :=
      add_le_add hmainN' hresidualN
    _ ≤ Cmain * 𝔖 * X + (1 / 2 : ℝ) * 𝔖 * X :=
      add_le_add le_rfl (hErrCube.trans hErrAbsorb)
    _ = (Cmain + 1 / 2) * 𝔖 * X := by ring
    _ = (Cmain + 1 / 2) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
      dsimp [𝔖, X]
      ring

/-- The strongest honest downstream consumer. -/
theorem q1LevelSupportedWeightedAggregate_consumer
    (h : Q1LevelSupportedWeightedAggregateTheorem) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
  hq1_of_weightedAggregate h

/-- A designated q¹ constant extracted from the level-supported route. -/
noncomputable def q1WeightedAggregateConstant
    (hAggregate : Q1WeightedAggregateTheorem) : ℝ :=
  Classical.choose (hq1_of_weightedAggregate hAggregate)

/-- Positivity and the eventual q¹ estimate for the designated constant. -/
theorem q1WeightedAggregateConstant_spec
    (hAggregate : Q1WeightedAggregateTheorem) :
    0 < q1WeightedAggregateConstant hAggregate ∧
      ∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
        correctedChenQ1Count N ≤
          q1WeightedAggregateConstant hAggregate *
            AnalyticNumberTheory.Sieve.singularSeriesTruncated N
              (correctedChenZ N - 1) * (N : ℝ) /
                (Real.log (N : ℝ)) ^ 2 :=
  Classical.choose_spec (hq1_of_weightedAggregate hAggregate)

end

end MathlibNt.SieveTheory.SwitchingPrinciple
