import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryPrimeMass
import MathlibNt.Wu2008DoubleSieve.PhiEndpoint

/-!
# Literal boundary counts and same-fibre Theta payment

Wu04 (3.17), source lines 1113--1127. The sum retains every original
convolution multiplicity. Its normalization uses the same support and
the actual `C(d*N)/(phi(d)*log(Q/d))`, through the finite same-fibre
comparison `boxTheta_lower_of_support`; no global box-mass bound is used.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

/-- Counting positive divisible complements, with arbitrary sifting
modulus and cutoff. Evenness rules out the zero complement. -/
theorem reboxing_source_count_le_divisor {N d : ℕ} (M : ℕ) (z : ℝ)
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) :
    (sourceSieveCount N d M z : ℝ) ≤ (N : ℝ) / d := by
  have hcard : (sourceSieveCarrier N d M z).card ≤ (Ioc 0 (N / d)).card := by
    apply card_le_card_of_injOn (fun p => (N - p) / d)
    · intro p hp
      obtain ⟨hpN, hp, hdp, _⟩ := mem_filter.mp hp
      have hpN' : p ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hpN)
      have hn := complement_pos_of_even hN he hpN' hp
      exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn hdp) hd,
        Nat.div_le_div_right (Nat.sub_le N p)⟩
    · intro p hp q hq hpq
      obtain ⟨hpN, _, hdp, _⟩ := mem_filter.mp hp
      obtain ⟨hqN, _, hdq, _⟩ := mem_filter.mp hq
      have hpN' := Nat.lt_succ_iff.mp (mem_range.mp hpN)
      have hqN' := Nat.lt_succ_iff.mp (mem_range.mp hqN)
      have heq := congrArg (fun n : ℕ => d * n) hpq
      dsimp at heq
      rw [Nat.mul_div_cancel' hdp, Nat.mul_div_cancel' hdq] at heq
      omega
  have hh : (sourceSieveCarrier N d M z).card ≤ N / d := by simpa using hcard
  calc
    _ = ((sourceSieveCarrier N d M z).card : ℝ) := by simp [sourceSieveCount]
    _ ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hh
    _ ≤ _ := Nat.cast_div_le

/-- The literal unscaled strict boundary sum, with fibre-dependent
endpoints and the source modulus `d*N`, not `(d*p)*N`. -/
noncomputable def reboxingBoundaryCount {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (Y Z : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ primeWindow N (Y d) (Z d),
      (sourceSieveCount N (d * p) (d * N) (p : ℝ) : ℝ)

theorem reboxingBoundaryCount_nonneg {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (Y Z : ℕ → ℝ) : 0 ≤ reboxingBoundaryCount N W Y Z := by
  unfold reboxingBoundaryCount
  apply sum_nonneg
  intro d _
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro p _
  simp only [sourceSieveCount, Int.cast_natCast]
  positivity

theorem reboxingBoundaryCount_le_mass {i N : ℕ} (W : Fin i → Finset ℕ)
    (Y Z : ℕ → ℝ) {B : ℝ} (hN : 4 ≤ N) (he : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hmass : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ primeWindow N (Y d) (Z d), (1 : ℝ) / p) ≤ B) :
    reboxingBoundaryCount N W Y Z ≤
      (N : ℝ) * B * boxConvolutionReciprocalMass W := by
  unfold reboxingBoundaryCount boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hmem
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd d hmem
  calc
    _ ≤ (convolutionCoeff W d : ℝ) *
        ∑ p ∈ primeWindow N (Y d) (Z d), (N : ℝ) / ((d : ℝ) * p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro p hp
      simpa only [Nat.cast_mul] using reboxing_source_count_le_divisor (d * N) (p : ℝ)
        hN he (Nat.mul_pos (hd d hmem) (mem_primeWindow.mp hp).1.pos)
    _ = (convolutionCoeff W d : ℝ) * ((N : ℝ) / d) *
        ∑ p ∈ primeWindow N (Y d) (Z d), (1 : ℝ) / p := by
      simp_rw [show ∀ p : ℕ, (N : ℝ) / ((d : ℝ) * p) =
        ((N : ℝ) / d) * (1 / (p : ℝ)) by intro p; ring]
      rw [← mul_sum, mul_assoc]
    _ ≤ (convolutionCoeff W d : ℝ) * ((N : ℝ) / d) * B :=
      mul_le_mul_of_nonneg_left (hmass d hmem) (by positivity)
    _ = _ := by ring

/-- Finite same-fibre payment. The local reciprocal-prime bound is proved
uniformly below; this algebraic step never replaces Theta by a global
`N/log(N)^(5k+2)` lower bound. -/
theorem reboxingBoundaryCount_le_theta {i N : ℕ} {Q B : ℝ}
    (W : Fin i → Finset ℕ) (Y Z : ℕ → ℝ)
    (hN : 4 ≤ N) (he : Even N) (hB : 0 ≤ B)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < Q / d ∧ Q / d ≤ N)
    (hmass : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ primeWindow N (Y d) (Z d), (1 : ℝ) / p) ≤
        B / log (N : ℝ) ^ (5 : ℕ)) :
    reboxingBoundaryCount N W Y Z ≤
      (B / (2 * liuUniversalProduct) / log (N : ℝ) ^ (3 : ℕ)) * boxTheta N Q W := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hU := liuUniversalProduct_pos
  have hfinite := reboxingBoundaryCount_le_mass W Y Z hN he hd hmass
  have hTheta := boxTheta_lower_of_support W hN hd hQ
  calc
    _ ≤ (N : ℝ) * (B / log (N : ℝ) ^ (5 : ℕ)) *
        boxConvolutionReciprocalMass W := hfinite
    _ = (B / (2 * liuUniversalProduct) / log (N : ℝ) ^ (3 : ℕ)) *
        (2 * liuUniversalProduct * (N : ℝ) / log (N : ℝ) ^ (2 : ℕ) *
          boxConvolutionReciprocalMass W) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hTheta (by positivity)

/-- One threshold is chosen before the depth, the finite windows, the
support fibres and both fibre-dependent boundary endpoints. -/
theorem reboxing_boundary_relative {α K ε : ℝ}
    (hα : 0 < α) (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Q : ℝ) (W : Fin i → Finset ℕ) (Y Z : ℕ → ℝ),
      (∀ d ∈ boxConvolutionSupport W, 0 < d) →
      (∀ d ∈ boxConvolutionSupport W, 1 < Q / d ∧ Q / d ≤ N) →
      (∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ α ≤ Y d ∧
        Y d ≤ Z d ∧ log (Z d / Y d) ≤ K / log (N : ℝ) ^ (4 : ℕ)) →
      reboxingBoundaryCount N W Y Z ≤ ε * boxTheta N Q W := by
  obtain ⟨T, hT⟩ := reboxing_short_prime_mass hα hK
  let B := 2 * K / α + 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hU := liuUniversalProduct_pos
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbudget : ∀ᶠ N : ℕ in atTop,
      B / (2 * liuUniversalProduct) / ε ≤ log (N : ℝ) ^ (3 : ℕ) :=
    ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hlogt).eventually
      (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (4 : ℕ), hbudget]
    with N hN hN4 hbud
  intro he i Q W Y Z hd hQ hw
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ primeWindow N (Y d) (Z d), (1 : ℝ) / p) ≤ B / log (N : ℝ) ^ (5 : ℕ) := by
    intro d hmem
    exact hT N hN (Y d) (Z d) (hw d hmem).1 (hw d hmem).2.1 (hw d hmem).2.2
  have hθ : 0 ≤ boxTheta N Q W := by
    apply le_trans _ (boxTheta_lower_of_support W hN4 hd hQ)
    apply mul_nonneg (by positivity)
    unfold boxConvolutionReciprocalMass
    exact sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hpay : B / (2 * liuUniversalProduct) / log (N : ℝ) ^ (3 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := (div_le_iff₀ hε).1 hbud
    nlinarith
  exact (reboxingBoundaryCount_le_theta W Y Z hN4 he hB.le hd hQ hm).trans
    (mul_le_mul_of_nonneg_right hpay hθ)

end Wu2008DoubleSieve
