import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection14LegalDomainBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerDepthFourCarrier
import MathlibNt.SieveTheory.LinearSieve

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

/-- The depth-four lower-Rosser boundary mass: three stored decreasing primes,
followed by the terminal least prime.  The two displayed inequalities are
exactly the active even-prefix test and terminal odd-boundary crossing. -/
noncomputable def lowerRosserDepthFourSourceMass
    (S : BoundingSieve) (D z : ℕ) : ℝ :=
  ∑ p₀ ∈ suzukiSupportedBelow S z,
    S.nu p₀ * ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
        (fun p₁ => p₀ * p₁ ^ 3 < D),
      S.nu p₁ * ∑ p₂ ∈ suzukiSupportedBelow S p₁,
        S.nu p₂ * ∑ q ∈ (suzukiSupportedBelow S p₂).filter
            (fun q => D ≤ p₀ * p₁ * p₂ * q ^ 3),
          S.nu q * sourceDiscreteEuler S q

private theorem supportedBelow_pos {S : BoundingSieve} {z p : ℕ}
    (hp : p ∈ suzukiSupportedBelow S z) : 0 < p := by
  have hpP : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hp).1
  exact (Nat.prime_of_mem_primeFactors hpP).pos

private theorem source_depthFour_terminal_iff
    {D p₀ p₁ p₂ q : ℕ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    (((D ⌈/⌉ p₀) ⌈/⌉ p₁) ⌈/⌉ p₂ ≤ q ^ 3) ↔
      D ≤ p₀ * p₁ * p₂ * q ^ 3 := by
  rw [ceilDiv_le_iff_le_mul hp₂, ceilDiv_le_iff_le_mul hp₁,
    ceilDiv_le_iff_le_mul hp₀]
  simp only [mul_assoc]

private theorem source_depthFour_prefix_iff
    {D p₀ p₁ : ℕ} (hp₀ : 0 < p₀) :
    p₁ ^ 3 < D ⌈/⌉ p₀ ↔ p₀ * p₁ ^ 3 < D := by
  rw [← not_le, ceilDiv_le_iff_le_mul hp₀, not_le]

/-- At every odd outer depth, the source lower cutoff is redundant: whenever
it fails, the remaining even layer vanishes.  The odd cubic upper cutoff is the
only active outer condition. -/
theorem suzukiSourceV_odd_succ_eq_upper_only
    (S : BoundingSieve) {n D z : ℕ} (hn : 0 < n) (hodd : Odd (n + 1)) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D),
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p := by
  rw [suzukiSourceV_succ_of_pos S hn]
  apply Finset.sum_subset
  · intro p hp
    simp only [suzukiSourceOuterCarrier, Finset.mem_filter] at hp ⊢
    refine ⟨?_, hp.2.2 hodd⟩
    simpa [suzukiSupportedBelow] using hp.1
  · intro p hpUpper hpNotCarrier
    have hpSupport : p ∈ suzukiSupportedBelow S z :=
      (Finset.mem_filter.mp hpUpper).1
    have hpPos := supportedBelow_pos hpSupport
    have hUpper : p ^ 3 < D := (Finset.mem_filter.mp hpUpper).2
    have hLowerFails : ¬ D ≤ p ^ ((n + 1) + 2) := by
      intro hLower
      apply hpNotCarrier
      simp only [suzukiSourceOuterCarrier, Finset.mem_filter]
      exact ⟨Finset.mem_filter.mp hpSupport, hLower, fun _ => hUpper⟩
    have hvanish : p ^ (n + 2) ≤ D ⌈/⌉ p := by
      by_contra h
      have hceil : D ⌈/⌉ p < p ^ (n + 2) := Nat.lt_of_not_ge h
      have hmul : p * (D ⌈/⌉ p) < p * p ^ (n + 2) :=
        (Nat.mul_lt_mul_left hpPos).2 hceil
      have hDceil : D ≤ p * (D ⌈/⌉ p) :=
        (ceilDiv_le_iff_le_mul hpPos).1 le_rfl
      have hpowsucc : p * p ^ (n + 2) = p ^ ((n + 1) + 2) := by
        calc
          p * p ^ (n + 2) = p ^ (n + 2) * p := Nat.mul_comm _ _
          _ = p ^ ((n + 2) + 1) := (pow_succ _ _).symm
          _ = p ^ ((n + 1) + 2) := rfl
      rw [hpowsucc] at hmul
      exact hLowerFails (hDceil.trans hmul.le)
    rw [suzukiSourceV_eq_zero_of_pow_le S hn hvanish, mul_zero]

/-- Suzuki's complete even layer `V₄` is exactly the depth-four lower-Rosser
boundary mass.  The proof follows the exact recurrence: even source lower
cutoffs vanish, the depth-three lower cutoff is killed by the residual `V₂`,
and the remaining divided inequalities clear to the prefix and terminal tests. -/
theorem suzukiSourceV_four_eq_lowerRosserDepthFourSourceMass
    (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 4 D z = lowerRosserDepthFourSourceMass S D z := by
  rw [suzukiSourceV_succ_eq_unrestricted S (by omega : 0 < 3)
    (by norm_num)]
  simp_rw [suzukiSourceV_odd_succ_eq_upper_only S (by omega : 0 < 2)
    (by norm_num)]
  simp_rw [suzukiSourceV_succ_eq_unrestricted S (by omega : 0 < 1) (by norm_num)]
  simp_rw [suzukiSourceV_one]
  unfold lowerRosserDepthFourSourceMass
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  have hp₀pos := supportedBelow_pos hp₀
  apply congrArg (fun x : ℝ => S.nu p₀ * x)
  apply Finset.sum_congr
  · ext p₁
    simp only [Finset.mem_filter]
    exact and_congr_right fun hp₁ => source_depthFour_prefix_iff hp₀pos
  · intro p₁ hp₁
    have hp₁support : p₁ ∈ suzukiSupportedBelow S p₀ :=
      (Finset.mem_filter.mp hp₁).1
    have hp₁pos := supportedBelow_pos hp₁support
    apply congrArg (fun x : ℝ => S.nu p₁ * x)
    apply Finset.sum_congr rfl
    intro p₂ hp₂
    have hp₂pos := supportedBelow_pos hp₂
    apply congrArg (fun x : ℝ => S.nu p₂ * x)
    apply Finset.sum_congr
    · ext q
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ =>
        source_depthFour_terminal_iff hp₀pos hp₁pos hp₂pos
    · intro q hq
      rfl

/-- The finite even Suzuki aggregate truncated at depth four is the depth-two
layer plus the newly identified lower-Rosser depth-four boundary mass.  This is
the explicit depth-four truncation of the general even-layer correspondence. -/
theorem suzukiActualT_four_eq_two_add_lowerRosserDepthFourSourceMass
    (S : BoundingSieve) (D z : ℕ) :
    suzukiActualT S 4 D z =
      suzukiSourceV S 2 D z + lowerRosserDepthFourSourceMass S D z := by
  rw [show suzukiActualT S 4 D z =
      suzukiSourceV S 4 D z + suzukiSourceV S 2 D z by
        simp [suzukiActualT],
    suzukiSourceV_four_eq_lowerRosserDepthFourSourceMass]
  ring

/-- Equivalently, the literal finite parity sum at truncation depth four splits
into its depth-two layer and the lower-Rosser depth-four boundary mass. -/
theorem suzukiEvenParitySum_four_eq_two_add_lowerRosserDepthFourSourceMass
    (S : BoundingSieve) (D z : ℕ) :
    (∑ n ∈ suzukiActualParityCarrier 4, suzukiSourceV S n D z) =
      suzukiSourceV S 2 D z + lowerRosserDepthFourSourceMass S D z := by
  rw [← suzukiActualT_eq_parity_sum]
  exact suzukiActualT_four_eq_two_add_lowerRosserDepthFourSourceMass S D z

/-- The depth-six lower-Rosser boundary mass.  Its two interior tests occur
at the odd prefixes, followed by the terminal boundary crossing. -/
noncomputable def lowerRosserDepthSixSourceMass
    (S : BoundingSieve) (D z : ℕ) : ℝ :=
  ∑ p₀ ∈ suzukiSupportedBelow S z,
    S.nu p₀ * ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
        (fun p₁ => p₀ * p₁ ^ 3 < D),
      S.nu p₁ * ∑ p₂ ∈ suzukiSupportedBelow S p₁,
        S.nu p₂ * ∑ p₃ ∈ (suzukiSupportedBelow S p₂).filter
            (fun p₃ => p₀ * p₁ * p₂ * p₃ ^ 3 < D),
          S.nu p₃ * ∑ p₄ ∈ suzukiSupportedBelow S p₃,
            S.nu p₄ * ∑ q ∈ (suzukiSupportedBelow S p₄).filter
                (fun q => D ≤ p₀ * p₁ * p₂ * p₃ * p₄ * q ^ 3),
              S.nu q * sourceDiscreteEuler S q

private theorem source_depthSix_second_prefix_iff
    {D p₀ p₁ p₂ p₃ : ℕ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    p₃ ^ 3 < ((D ⌈/⌉ p₀) ⌈/⌉ p₁) ⌈/⌉ p₂ ↔
      p₀ * p₁ * p₂ * p₃ ^ 3 < D := by
  rw [← not_le, ceilDiv_le_iff_le_mul hp₂, ceilDiv_le_iff_le_mul hp₁,
    ceilDiv_le_iff_le_mul hp₀, not_le]
  simp only [mul_assoc]

private theorem source_depthSix_terminal_iff
    {D p₀ p₁ p₂ p₃ p₄ q : ℕ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hp₃ : 0 < p₃) (hp₄ : 0 < p₄) :
    (((((D ⌈/⌉ p₀) ⌈/⌉ p₁) ⌈/⌉ p₂) ⌈/⌉ p₃) ⌈/⌉ p₄ ≤ q ^ 3) ↔
      D ≤ p₀ * p₁ * p₂ * p₃ * p₄ * q ^ 3 := by
  rw [ceilDiv_le_iff_le_mul hp₄, ceilDiv_le_iff_le_mul hp₃,
    ceilDiv_le_iff_le_mul hp₂, ceilDiv_le_iff_le_mul hp₁,
    ceilDiv_le_iff_le_mul hp₀]
  simp only [mul_assoc]

/-- Suzuki's complete even layer `V₆` is exactly the depth-six lower-Rosser
boundary mass.  This is the next case of the alternating odd-prefix pattern. -/
theorem suzukiSourceV_six_eq_lowerRosserDepthSixSourceMass
    (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 6 D z = lowerRosserDepthSixSourceMass S D z := by
  rw [suzukiSourceV_succ_eq_unrestricted S (by omega : 0 < 5)
    (by norm_num)]
  simp_rw [suzukiSourceV_odd_succ_eq_upper_only S (by omega : 0 < 4)
    (by norm_num)]
  simp_rw [suzukiSourceV_succ_eq_unrestricted S (by omega : 0 < 3)
    (by norm_num)]
  simp_rw [suzukiSourceV_odd_succ_eq_upper_only S (by omega : 0 < 2)
    (by norm_num)]
  simp_rw [suzukiSourceV_succ_eq_unrestricted S (by omega : 0 < 1)
    (by norm_num)]
  simp_rw [suzukiSourceV_one]
  unfold lowerRosserDepthSixSourceMass
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  have hp₀pos := supportedBelow_pos hp₀
  apply congrArg (fun x : ℝ => S.nu p₀ * x)
  apply Finset.sum_congr
  · ext p₁
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => source_depthFour_prefix_iff hp₀pos
  · intro p₁ hp₁
    have hp₁support : p₁ ∈ suzukiSupportedBelow S p₀ :=
      (Finset.mem_filter.mp hp₁).1
    have hp₁pos := supportedBelow_pos hp₁support
    apply congrArg (fun x : ℝ => S.nu p₁ * x)
    apply Finset.sum_congr rfl
    intro p₂ hp₂
    have hp₂pos := supportedBelow_pos hp₂
    apply congrArg (fun x : ℝ => S.nu p₂ * x)
    apply Finset.sum_congr
    · ext p₃
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ =>
        source_depthSix_second_prefix_iff hp₀pos hp₁pos hp₂pos
    · intro p₃ hp₃
      have hp₃support : p₃ ∈ suzukiSupportedBelow S p₂ :=
        (Finset.mem_filter.mp hp₃).1
      have hp₃pos := supportedBelow_pos hp₃support
      apply congrArg (fun x : ℝ => S.nu p₃ * x)
      apply Finset.sum_congr rfl
      intro p₄ hp₄
      have hp₄pos := supportedBelow_pos hp₄
      apply congrArg (fun x : ℝ => S.nu p₄ * x)
      apply Finset.sum_congr
      · ext q
        simp only [Finset.mem_filter]
        exact and_congr_right fun _ =>
          source_depthSix_terminal_iff hp₀pos hp₁pos hp₂pos hp₃pos hp₄pos
      · intro q hq
        rfl

/-- The finite even Suzuki aggregate truncated at depth six is its depth-four
aggregate plus the newly identified depth-six boundary mass. -/
theorem suzukiActualT_six_eq_four_add_lowerRosserDepthSixSourceMass
    (S : BoundingSieve) (D z : ℕ) :
    suzukiActualT S 6 D z =
      suzukiActualT S 4 D z + lowerRosserDepthSixSourceMass S D z := by
  rw [show suzukiActualT S 6 D z =
      suzukiSourceV S 6 D z + suzukiActualT S 4 D z by
        simp [suzukiActualT],
    suzukiSourceV_six_eq_lowerRosserDepthSixSourceMass]
  ring

/-- The boundary layer at arbitrary recursion depth.  Depth one is the terminal
odd crossing.  Every later odd layer records the active cubic upper test, while
every even layer only extends the decreasing prime chain.  Thus a layer carries
exactly the alternating-prefix invariant visible at depths four and six. -/
noncomputable def lowerRosserBoundaryLayerMass (S : BoundingSieve) :
    ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, D, z =>
      ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => D ≤ q ^ 3),
        S.nu q * sourceDiscreteEuler S q
  | n + 2, D, z =>
      ∑ p ∈ if Odd (n + 2) then
          (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D)
        else suzukiSupportedBelow S z,
        S.nu p * lowerRosserBoundaryLayerMass S (n + 1) (D ⌈/⌉ p) p

/-- General Suzuki/lower-Rosser layer correspondence.  The inductive invariant
is that the current divided level is retained literally; odd outer depths add
`p³ < D`, even outer depths add no test, and depth one closes with `D ≤ q³`. -/
theorem suzukiSourceV_eq_lowerRosserBoundaryLayerMass
    (S : BoundingSieve) (n D z : ℕ) (hn : 0 < n) :
    suzukiSourceV S n D z = lowerRosserBoundaryLayerMass S n D z := by
  induction n using Nat.strong_induction_on generalizing D z with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero => simp [lowerRosserBoundaryLayerMass, suzukiSourceV_one]
          | succ n =>
              have hstep (prime : ℕ) :
                  suzukiSourceV S (n + 1) (D ⌈/⌉ prime) prime =
                    lowerRosserBoundaryLayerMass S (n + 1) (D ⌈/⌉ prime) prime :=
                ih (n + 1) (by omega) (D ⌈/⌉ prime) prime (by omega)
              by_cases hodd : Odd (n + 2)
              · rw [suzukiSourceV_odd_succ_eq_upper_only S (by omega) hodd]
                simp only [lowerRosserBoundaryLayerMass, if_pos hodd, hstep]
              · rw [suzukiSourceV_succ_eq_unrestricted S (by omega)
                    (fun h => (hodd h).elim)]
                simp only [lowerRosserBoundaryLayerMass, if_neg hodd, hstep]

/-- The `m`-th (one-indexed mathematically, zero-indexed here) even boundary
layer has Suzuki depth `2(m+1)`. -/
noncomputable def lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) : ℝ :=
  lowerRosserBoundaryLayerMass S (2 * (m + 1)) D z

/-- Every positive even Suzuki layer is the corresponding lower-Rosser boundary
layer. -/
theorem suzukiSourceV_even_eq_lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) :
    suzukiSourceV S (2 * (m + 1)) D z =
      lowerRosserEvenBoundaryLayerMass S m D z := by
  unfold lowerRosserEvenBoundaryLayerMass
  exact suzukiSourceV_eq_lowerRosserBoundaryLayerMass S _ D z (by omega)

/-- The general layer specializes to the previously expanded depth-four mass. -/
theorem lowerRosserBoundaryLayerMass_four_eq_depthFour
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserBoundaryLayerMass S 4 D z =
      lowerRosserDepthFourSourceMass S D z := by
  rw [← suzukiSourceV_four_eq_lowerRosserDepthFourSourceMass]
  symm
  exact suzukiSourceV_eq_lowerRosserBoundaryLayerMass S 4 D z (by omega)

/-- The general layer specializes to the previously expanded depth-six mass. -/
theorem lowerRosserBoundaryLayerMass_six_eq_depthSix
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserBoundaryLayerMass S 6 D z =
      lowerRosserDepthSixSourceMass S D z := by
  rw [← suzukiSourceV_six_eq_lowerRosserDepthSixSourceMass]
  symm
  exact suzukiSourceV_eq_lowerRosserBoundaryLayerMass S 6 D z (by omega)

/-- At arbitrary even truncation, `suzukiActualT` is exactly the finite sum of
all lower-Rosser boundary layers through depth `2m`. -/
theorem suzukiActualT_even_eq_sum_lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) :
    suzukiActualT S (2 * m) D z =
      ∑ k ∈ Finset.range m, lowerRosserEvenBoundaryLayerMass S k D z := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega,
        suzukiActualT_add_two,
        show 2 * m + 2 = 2 * (m + 1) by omega,
        suzukiSourceV_even_eq_lowerRosserEvenBoundaryLayerMass,
        ih]
      simp [Finset.sum_range_succ, add_comm]

/-- The part of the full one-prime lower-Rosser boundary accumulator not yet
represented by the even layers through depth `2m`.  This definition keeps the
remaining combinatorial issue explicit rather than identifying it silently. -/
noncomputable def lowerRosserBoundaryAfterEvenDepth
    (S : BoundingSieve) (D z : ℕ) (P : Finset ℕ) (qs : List ℕ) (m : ℕ) : ℝ :=
  LinearSieve.lowerRosserBoundaryAccum S.nu D P qs -
    ∑ k ∈ Finset.range m, lowerRosserEvenBoundaryLayerMass S k D z

/-- Exact connection between the finite Suzuki even-layer sum and the existing
`lowerRosserBoundaryAccum`: the latter is the truncation plus its explicit
post-depth remainder. -/
theorem lowerRosserBoundaryAccum_eq_suzukiActualT_even_add_remainder
    (S : BoundingSieve) (D z : ℕ) (P : Finset ℕ) (qs : List ℕ) (m : ℕ) :
    LinearSieve.lowerRosserBoundaryAccum S.nu D P qs =
      suzukiActualT S (2 * m) D z +
        lowerRosserBoundaryAfterEvenDepth S D z P qs m := by
  rw [suzukiActualT_even_eq_sum_lowerRosserEvenBoundaryLayerMass]
  unfold lowerRosserBoundaryAfterEvenDepth
  ring

/-- Consequently, identifying the finite Suzuki truncation with the complete
boundary accumulator is exactly the assertion that the explicit remainder
vanishes. -/
theorem suzukiActualT_even_eq_lowerRosserBoundaryAccum_iff
    (S : BoundingSieve) (D z : ℕ) (P : Finset ℕ) (qs : List ℕ) (m : ℕ) :
    suzukiActualT S (2 * m) D z =
        LinearSieve.lowerRosserBoundaryAccum S.nu D P qs ↔
      lowerRosserBoundaryAfterEvenDepth S D z P qs m = 0 := by
  rw [lowerRosserBoundaryAccum_eq_suzukiActualT_even_add_remainder]
  constructor <;> intro h <;> linarith


end MathlibNt.SieveTheory
