import MathlibNt.SieveTheory.Switching.BoundaryDensity

/-!
# Residual boundary comparisons and support screens

Recursive residual-comparison predicates, ceil-division identities, and lower
logarithmic screens reduce boundary densities to continuous residual masses.
Partition faces and paired residual errors retain quantitative bounds.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- A pointwise comparison interface for a residual upper Rosser chain inside a
fixed bounding sieve.  Besides the altered real level, it retains both
invariants created by pair removal: the residual carrier stays in the ambient
prime carrier and all of its logarithmic coordinates lie strictly below the
inherited upper endpoint. -/
def UpperRosserBoundaryResidualComparison
    (S : BoundingSieve) (z : ℝ) (q k : ℕ) (ε : ℝ) : Prop :=
  ∀ ⦃Δ s b : ℝ⦄ ⦃P : Finset ℕ⦄,
    1 < Δ →
    s = Real.log Δ / Real.log z →
    P ⊆ S.prodPrimes.primeFactors →
    q ∉ P →
    q.Prime →
    (∀ p ∈ P, p.Prime) →
    (∀ p ∈ P, q ≤ p) →
    (∀ p ∈ P, Real.log p / Real.log z < b) →
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q P k ≤
      LinearSieve.upperRosserBoundaryMassAux k s
        (Real.log q / Real.log z) b + ε

/-- The residual comparison restricted to the screen and bounded level range
that are preserved by pair removal.  Unlike
`UpperRosserBoundaryResidualComparison`, this is closed under the fixed-depth
induction: a residual level is positive and no larger than its parent level,
while its inherited upper face remains at most one. -/
def UpperRosserBoundaryScreenedResidualComparison
    (S : BoundingSieve) (z : ℝ) (q k : ℕ) (ε c s₁ : ℝ) : Prop :=
  ∀ ⦃Δ s b : ℝ⦄ ⦃P : Finset ℕ⦄,
    1 < Δ →
    s = Real.log Δ / Real.log z →
    s ≤ s₁ →
    P ⊆ S.prodPrimes.primeFactors →
    q ∉ P →
    q.Prime →
    (∀ p ∈ P, p.Prime) →
    (∀ p ∈ P, q ≤ p) →
    (∀ p ∈ P, Real.log p / Real.log z < b) →
    c ≤ Real.log q / Real.log z →
    b ≤ 1 →
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q P k ≤
      LinearSieve.upperRosserBoundaryMassAux k s
        (Real.log q / Real.log z) b + ε

/-- A global residual comparison restricts to every screened bounded range. -/
theorem UpperRosserBoundaryResidualComparison.screened
    {S : BoundingSieve} {z : ℝ} {q k : ℕ} {ε c s₁ : ℝ}
    (hcomparison : UpperRosserBoundaryResidualComparison S z q k ε) :
    UpperRosserBoundaryScreenedResidualComparison S z q k ε c s₁ := by
  intro Δ s b P hΔ hs _hsUpper hP hqs hqprime hprime hqmin hupper
    _hqscreen _hb
  exact hcomparison hΔ hs hP hqs hqprime hprime hqmin hupper

/-- Increasing the lower-screen requirement only restricts the instances of a
screened residual comparison. -/
theorem UpperRosserBoundaryScreenedResidualComparison.mono
    {S : BoundingSieve} {z : ℝ} {q k : ℕ} {ε c d s₁ : ℝ}
    (hdc : d ≤ c)
    (hcomparison :
      UpperRosserBoundaryScreenedResidualComparison S z q k ε d s₁) :
    UpperRosserBoundaryScreenedResidualComparison S z q k ε c s₁ := by
  intro Δ s b P hΔ hs hsUpper hP hqs hqprime hprime hqmin hupper hqscreen hb
  exact hcomparison hΔ hs hsUpper hP hqs hqprime hprime hqmin hupper
    (hdc.trans hqscreen) hb

/-- The residual comparison interface holds at depth zero with no error, for
every altered real level and every ambiently supported carrier below its
inherited upper endpoint. -/
theorem upperRosserBoundaryResidualComparison_zero
    (S : BoundingSieve) {z : ℝ} {q : ℕ} (hz : 1 < z) :
    UpperRosserBoundaryResidualComparison S z q 0 0 := by
  intro Δ s b P hΔ hs _hP hqs hqprime _hprime hqmin _hupper
  rw [add_zero]
  apply
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux
      (fun p => S.nu p / (1 - S.nu p))
      hz (by linarith) hs rfl ?_ rfl ?_ hqs hqprime hqmin
  · rw [hs]
    exact div_nonneg (Real.log_nonneg hΔ.le) (Real.log_pos hz).le
  · have hone : ((1 : ℕ) : ℝ) ≤ Δ := by norm_num; linarith
    have : 1 ≤ Nat.floor Δ := Nat.le_floor hone
    omega

/-- The exact depth-zero comparison is induction-ready on every bounded
screened range. -/
theorem upperRosserBoundaryScreenedResidualComparison_zero
    (S : BoundingSieve) {z c s₁ : ℝ} {q : ℕ} (hz : 1 < z) :
    UpperRosserBoundaryScreenedResidualComparison S z q 0 0 c s₁ :=
  (upperRosserBoundaryResidualComparison_zero S hz).screened

/-- The outer prime exposed by one Buchstab pair lies in the exact inherited
screen.  The cubic Rosser condition gives the closed `s / 3` face, while the
residual carrier gives the strict inherited face `b`. -/
theorem upperRosserBoundaryPair_outerLogCoordinate_mem
    {z Δ s b : ℝ} {q p₀ : ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hqprime : q.Prime) (hp₀prime : p₀.Prime) (hqp₀ : q < p₀)
    (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hp₀upper : Real.log p₀ / Real.log z < b) :
    Real.log p₀ / Real.log z ∈
      Set.Ioc (Real.log q / Real.log z) (min b (s / 3)) ∩ Set.Iio b := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
  have hqcoord :
      Real.log q / Real.log z < Real.log p₀ / Real.log z := by
    apply (div_lt_div_iff_of_pos_right hlogz).2
    exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₀pos).2
      (by exact_mod_cast hqp₀)
  have hp₀floor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
  have hp₀Δ : (p₀ : ℝ) ^ 3 ≤ Δ := by
    have hcast : ((p₀ ^ 3 : ℕ) : ℝ) ≤ (Nat.floor Δ : ℝ) := by
      exact_mod_cast hp₀floor
    norm_num at hcast
    exact hcast.trans (Nat.floor_le hΔ.le)
  have hlogpow : 3 * Real.log p₀ ≤ Real.log Δ := by
    have h := Real.strictMonoOn_log.monotoneOn
      (by exact pow_pos hp₀pos 3) hΔ hp₀Δ
    simpa [Real.log_pow] using h
  have hp₀third : Real.log p₀ / Real.log z ≤ s / 3 := by
    rw [hs]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hdiv :
        (3 * Real.log p₀) / Real.log z ≤ Real.log Δ / Real.log z :=
      (div_le_div_iff_of_pos_right hlogz).2 hlogpow
    calc
      Real.log p₀ / Real.log z * 3 =
          (3 * Real.log p₀) / Real.log z := by ring
      _ ≤ Real.log Δ / Real.log z := hdiv
  exact ⟨⟨hqcoord, le_min hp₀upper.le hp₀third⟩, hp₀upper⟩

/-- A residual comparison can be instantiated at the exact altered level left
by peeling two primes.  The ceiling-divided level and residual coordinate agree
after the elementary logarithm identities; ambient support is inherited, and
the strict carrier bound `p < p₁` supplies the logarithmic upper face. -/
theorem UpperRosserBoundaryResidualComparison.ceilDiv
    {S : BoundingSieve} {z : ℝ} {q k : ℕ} {ε : ℝ}
    (hcomparison : UpperRosserBoundaryResidualComparison S z q k ε)
    {Δ s : ℝ} {p₀ p₁ : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z)
    (hqprime : q.Prime) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqs : q ∉ P) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) (hupper : ∀ p ∈ P, p < p₁) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p))
        ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q P k ≤
      LinearSieve.upperRosserBoundaryMassAux k
          (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
          (Real.log q / Real.log z) (Real.log p₁ / Real.log z) + ε := by
  have hp₀pos : 0 < p₀ := hp₀prime.pos
  have hp₁pos : 0 < p₁ := hp₁prime.pos
  have hcpos : 0 < p₀ * p₁ := Nat.mul_pos hp₀pos hp₁pos
  have hprodCube : p₀ * p₁ < p₀ ^ 3 := by
    calc
      p₀ * p₁ < p₀ * p₀ := (Nat.mul_lt_mul_left hp₀pos).2 hp₁₀
      _ < p₀ ^ 3 := by simp only [pow_succ]; nlinarith
  have hcubeFloor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
  have hprodFloor : p₀ * p₁ < Nat.floor Δ :=
    hprodCube.trans_le hcubeFloor
  have hprodΔ : (p₀ : ℝ) * p₁ < Δ := by
    have hfloor : (Nat.floor Δ : ℝ) ≤ Δ := Nat.floor_le hΔ.le
    have hcast : ((p₀ * p₁ : ℕ) : ℝ) < (Nat.floor Δ : ℝ) := by
      exact_mod_cast hprodFloor
    norm_num at hcast
    exact hcast.trans_le hfloor
  let Δ' : ℝ := Δ / (p₀ * p₁)
  have hΔ' : 1 < Δ' :=
    (one_lt_div₀ (by exact_mod_cast hcpos)).2 hprodΔ
  have hlevel :
      (Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁) = Nat.floor Δ' + 1 := by
    simpa [Δ'] using
      ceilDiv_floor_add_one_eq_floor_div_add_one hΔ.le hcpos
  have hsres :
      s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z =
        Real.log Δ' / Real.log z := by
    rw [hs]
    have hp₀R : (p₀ : ℝ) ≠ 0 := by positivity
    have hp₁R : (p₁ : ℝ) ≠ 0 := by positivity
    rw [show Δ' = Δ / ((p₀ : ℝ) * p₁) by simp [Δ']]
    rw [Real.log_div hΔ.ne' (mul_ne_zero hp₀R hp₁R),
      Real.log_mul hp₀R hp₁R]
    ring
  have hlogUpper :
      ∀ p ∈ P, Real.log p / Real.log z < Real.log p₁ / Real.log z := by
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    have hp₁Pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
    apply (div_lt_div_iff_of_pos_right (Real.log_pos hz)).2
    exact (Real.strictMonoOn_log.lt_iff_lt hpPos hp₁Pos).2
      (by exact_mod_cast hupper p hp)
  rw [hlevel]
  exact hcomparison hΔ' hsres hP hqs hqprime hprime hqmin hlogUpper

/-- A screened bounded residual comparison applies after peeling an admissible
prime pair.  The residual level decreases, and the second prime supplies an
inherited face at most one whenever it lies below the ambient cutoff. -/
theorem UpperRosserBoundaryScreenedResidualComparison.ceilDiv
    {S : BoundingSieve} {z : ℝ} {q k : ℕ} {ε c s₁ : ℝ}
    (hcomparison :
      UpperRosserBoundaryScreenedResidualComparison S z q k ε c s₁)
    {Δ s : ℝ} {p₀ p₁ : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z) (hsUpper : s ≤ s₁)
    (hqprime : q.Prime) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hp₁cut : (p₁ : ℝ) ≤ z)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqs : q ∉ P) (hprime : ∀ p ∈ P, p.Prime)
    (hqmin : ∀ p ∈ P, q ≤ p) (hupper : ∀ p ∈ P, p < p₁)
    (hqscreen : c ≤ Real.log q / Real.log z) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p))
        ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q P k ≤
      LinearSieve.upperRosserBoundaryMassAux k
          (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
          (Real.log q / Real.log z) (Real.log p₁ / Real.log z) + ε := by
  have hp₀pos : 0 < p₀ := hp₀prime.pos
  have hp₁pos : 0 < p₁ := hp₁prime.pos
  have hcpos : 0 < p₀ * p₁ := Nat.mul_pos hp₀pos hp₁pos
  have hprodCube : p₀ * p₁ < p₀ ^ 3 := by
    calc
      p₀ * p₁ < p₀ * p₀ := (Nat.mul_lt_mul_left hp₀pos).2 hp₁₀
      _ < p₀ ^ 3 := by simp only [pow_succ]; nlinarith
  have hcubeFloor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
  have hprodFloor : p₀ * p₁ < Nat.floor Δ :=
    hprodCube.trans_le hcubeFloor
  have hprodΔ : (p₀ : ℝ) * p₁ < Δ := by
    have hfloor : (Nat.floor Δ : ℝ) ≤ Δ := Nat.floor_le hΔ.le
    have hcast : ((p₀ * p₁ : ℕ) : ℝ) < (Nat.floor Δ : ℝ) := by
      exact_mod_cast hprodFloor
    norm_num at hcast
    exact hcast.trans_le hfloor
  let Δ' : ℝ := Δ / (p₀ * p₁)
  have hΔ' : 1 < Δ' :=
    (one_lt_div₀ (by exact_mod_cast hcpos)).2 hprodΔ
  have hlevel :
      (Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁) = Nat.floor Δ' + 1 := by
    simpa [Δ'] using
      ceilDiv_floor_add_one_eq_floor_div_add_one hΔ.le hcpos
  have hsres :
      s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z =
        Real.log Δ' / Real.log z := by
    rw [hs]
    have hp₀R : (p₀ : ℝ) ≠ 0 := by positivity
    have hp₁R : (p₁ : ℝ) ≠ 0 := by positivity
    rw [show Δ' = Δ / ((p₀ : ℝ) * p₁) by simp [Δ']]
    rw [Real.log_div hΔ.ne' (mul_ne_zero hp₀R hp₁R),
      Real.log_mul hp₀R hp₁R]
    ring
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hp₀log : 0 ≤ Real.log p₀ :=
    Real.log_nonneg (by exact_mod_cast hp₀prime.one_lt.le)
  have hp₁log : 0 ≤ Real.log p₁ :=
    Real.log_nonneg (by exact_mod_cast hp₁prime.one_lt.le)
  have hsresUpper :
      s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z ≤ s₁ := by
    have hp₀coord : 0 ≤ Real.log p₀ / Real.log z :=
      div_nonneg hp₀log hlogz.le
    have hp₁coord : 0 ≤ Real.log p₁ / Real.log z :=
      div_nonneg hp₁log hlogz.le
    linarith
  have hp₁Upper : Real.log p₁ / Real.log z ≤ 1 := by
    apply (div_le_one hlogz).2
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hp₁prime.pos)
    · exact Set.mem_Ioi.mpr (by linarith)
    · exact hp₁cut
  have hlogUpper :
      ∀ p ∈ P, Real.log p / Real.log z < Real.log p₁ / Real.log z := by
    intro p hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    have hp₁Pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
    apply (div_lt_div_iff_of_pos_right hlogz).2
    exact (Real.strictMonoOn_log.lt_iff_lt hpPos hp₁Pos).2
      (by exact_mod_cast hupper p hp)
  rw [hlevel]
  exact hcomparison hΔ' hsres hsresUpper hP hqs hqprime hprime hqmin
    hlogUpper hqscreen hp₁Upper

/-- After peeling the first two selected primes, the ceiling-divided discrete
depth-zero mass is bounded by the continuous mass at the exact residual logarithmic
parameter.  In particular, there is no rounding loss in the residual Rosser level. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux_ceilDiv
    (nu : ℕ → ℝ) {z Δ s a b : ℝ} {q p₀ p₁ : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (ha : a = Real.log q / Real.log z)
    (hqprime : q.Prime) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hqs : q ∉ P) (hqmin : ∀ p ∈ P, q ≤ p) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity nu
        ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q P 0 ≤
      LinearSieve.upperRosserBoundaryMassAux 0
        (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z) a b := by
  have hp₀pos : 0 < p₀ := hp₀prime.pos
  have hp₁pos : 0 < p₁ := hp₁prime.pos
  have hcpos : 0 < p₀ * p₁ := Nat.mul_pos hp₀pos hp₁pos
  have hp₀one : 1 < p₀ := hp₀prime.one_lt
  have hprodCube : p₀ * p₁ < p₀ ^ 3 := by
    calc
      p₀ * p₁ < p₀ * p₀ := (Nat.mul_lt_mul_left hp₀pos).2 hp₁₀
      _ < p₀ ^ 3 := by simp only [pow_succ]; nlinarith
  have hcubeFloor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
  have hprodFloor : p₀ * p₁ < Nat.floor Δ :=
    hprodCube.trans_le hcubeFloor
  have hprodΔ : (p₀ : ℝ) * p₁ < Δ := by
    have hfloor : (Nat.floor Δ : ℝ) ≤ Δ := Nat.floor_le hΔ.le
    have hcast : ((p₀ * p₁ : ℕ) : ℝ) < (Nat.floor Δ : ℝ) := by
      exact_mod_cast hprodFloor
    norm_num at hcast
    exact hcast.trans_le hfloor
  let Δ' : ℝ := Δ / (p₀ * p₁)
  have hΔ' : 0 < Δ' := div_pos hΔ (by exact_mod_cast hcpos)
  have hΔ'one : 1 < Δ' :=
    (one_lt_div₀ (by exact_mod_cast hcpos)).2 hprodΔ
  have hlevel :
      (Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁) = Nat.floor Δ' + 1 := by
    simpa [Δ'] using
      ceilDiv_floor_add_one_eq_floor_div_add_one hΔ.le hcpos
  have hDlarge' : 1 < Nat.floor Δ' + 1 := by
    have hone : ((1 : ℕ) : ℝ) ≤ Δ' := by
      norm_num
      exact hΔ'one.le
    have : 1 ≤ Nat.floor Δ' := Nat.le_floor hone
    omega
  have hDlarge : 1 < (Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁) := by
    rw [hlevel]
    exact hDlarge'
  have hsres :
      s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z =
        Real.log Δ' / Real.log z := by
    rw [hs]
    have hp₀R : (p₀ : ℝ) ≠ 0 := by positivity
    have hp₁R : (p₁ : ℝ) ≠ 0 := by positivity
    rw [show Δ' = Δ / ((p₀ : ℝ) * p₁) by simp [Δ']]
    rw [Real.log_div hΔ.ne' (mul_ne_zero hp₀R hp₁R),
      Real.log_mul hp₀R hp₁R]
    ring
  apply
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux
      nu hz hΔ' hsres ha ?_ hlevel hDlarge hqs hqprime hqmin
  rw [hsres]
  exact div_nonneg (Real.log_nonneg hΔ'one.le) (Real.log_pos hz).le

/-- Pointwise depth-one Buchstab majorant.  Peeling the unique prime pair and
using the exact depth-zero shell comparison leaves precisely the residual
continuous indicator, with no local-product or rounding error. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_one_le_residualBoundaryMassAux
    (nu : ℕ → ℝ) {z Δ s : ℝ} {q : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hqs : q ∉ P) (hqprime : q.Prime)
    (hprime : ∀ p ∈ P, p.Prime) (hqmin : ∀ p ∈ P, q ≤ p)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        nu (Nat.floor Δ + 1) q P 1 ≤
      ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          nu p₀ * nu p₁ *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
  rw [LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_succ
    nu hqs hqprime hprime hqmin 0]
  apply Finset.sum_le_sum
  intro p₀ hp₀
  apply Finset.sum_le_sum
  intro p₁ hp₁
  have hp₁' := Finset.mem_filter.mp hp₁
  apply mul_le_mul_of_nonneg_left
  · apply
      upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux_ceilDiv
        nu hz hΔ hs rfl hqprime (hprime p₀ hp₀) (hprime p₁ hp₁'.1)
          hp₁'.2.1 hp₁'.2.2
    · simp [hqs]
    · intro p hp
      exact hqmin p (Finset.mem_filter.mp hp).1
  · exact mul_nonneg (hnu p₀ hp₀) (hnu p₁ hp₁'.1)

/-- The pointwise depth-one majorant can be restricted to the exact inherited
outer screen.  The upper endpoint is closed because the cubic condition only
implies `x₀ ≤ s / 3`; primes on that face must not be discarded. -/
theorem
    upperRosserBoundaryChainsFixedDepthDensity_one_le_screenedResidualBoundaryMassAux
    (nu : ℕ → ℝ) {z Δ s b : ℝ} {q : ℕ} {P : Finset ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hqs : q ∉ P) (hqprime : q.Prime)
    (hprime : ∀ p ∈ P, p.Prime) (hqmin : ∀ p ∈ P, q ≤ p)
    (hupper : ∀ p ∈ P, Real.log p / Real.log z < b)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        nu (Nat.floor Δ + 1) q P 1 ≤
      ∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
          Real.log p₀ / Real.log z ≤ min b (s / 3)),
        ∑ p₁ ∈ P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          nu p₀ * nu p₁ *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
  calc
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          nu (Nat.floor Δ + 1) q P 1 ≤
        ∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            nu p₀ * nu p₁ *
              LinearSieve.upperRosserBoundaryMassAux 0
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z) :=
      upperRosserBoundaryChainsFixedDepthDensity_one_le_residualBoundaryMassAux
        nu hz hΔ hs hqs hqprime hprime hqmin hnu
    _ = ∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
          Real.log p₀ / Real.log z ≤ min b (s / 3)),
        ∑ p₁ ∈ P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          nu p₀ * nu p₁ *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p₀ hp₀ hp₀not
      apply Finset.sum_eq_zero
      intro p₁ hp₁
      have hp₁' := Finset.mem_filter.mp hp₁
      have hqp₀ : q < p₀ := lt_of_le_of_ne (hqmin p₀ hp₀) (by
        intro hEq
        apply hqs
        simpa [hEq] using hp₀)
      have hscreen :=
        upperRosserBoundaryPair_outerLogCoordinate_mem hz hΔ hs hqprime
          (hprime p₀ hp₀) hqp₀ hp₁'.2.2 (hupper p₀ hp₀)
      exact (hp₀not (Finset.mem_filter.mpr ⟨hp₀, hscreen.1.2⟩)).elim

/-- The lower support exposed after peeling a Rosser pair is uniform at every
fixed residual depth.  The inherited upper bound is retained in the residual
mass, while the lower bound depends only on that depth. -/
theorem upperRosserBoundaryMassAux_ne_zero_outer_log_lower
    (k : ℕ) {z Δ s : ℝ} {q p₀ p₁ : ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hmass : LinearSieve.upperRosserBoundaryMassAux k
      (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
      (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≠ 0) :
    1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
  have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
  have hp₀floor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
  have hp₀Δ : (p₀ : ℝ) ^ 3 ≤ Δ := by
    have hcast : ((p₀ ^ 3 : ℕ) : ℝ) ≤ (Nat.floor Δ : ℝ) := by
      exact_mod_cast hp₀floor
    norm_num at hcast
    exact hcast.trans (Nat.floor_le hΔ.le)
  have hlogpow : 3 * Real.log p₀ ≤ Real.log Δ := by
    have h := Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < (p₀ : ℝ) ^ 3; exact pow_pos hp₀pos 3)
      (by change (0 : ℝ) < Δ; exact hΔ) hp₀Δ
    simpa [Real.log_pow] using h
  have hx₀ : Real.log p₀ / Real.log z ≤ s / 3 := by
    rw [hs]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hdiv :
        (3 * Real.log p₀) / Real.log z ≤ Real.log Δ / Real.log z :=
      (div_le_div_iff_of_pos_right hlogz).2 hlogpow
    calc
      Real.log p₀ / Real.log z * 3 =
          (3 * Real.log p₀) / Real.log z := by ring
      _ ≤ Real.log Δ / Real.log z := hdiv
  have hx₁ :
      Real.log p₁ / Real.log z < Real.log p₀ / Real.log z := by
    apply (div_lt_div_iff_of_pos_right hlogz).2
    exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
      (by exact_mod_cast hp₁₀)
  exact LinearSieve.upperRosserBoundaryMassAux_ne_zero_outer_lower
    k hslo hx₀ hx₁ hmass

/-- Every nonzero term in the continuous depth-zero majorant left after peeling
the first Rosser pair has its distinguished-prime coordinate above `1 / 6`.
Unlike fixed-chain support, this applies after the discrete residual has already
been enlarged to the continuous indicator. -/
theorem upperRosserBoundaryMassAux_zero_ne_zero_outer_log_lower
    {z Δ s : ℝ} {q p₀ p₁ : ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hmass : LinearSieve.upperRosserBoundaryMassAux 0
      (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
      (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≠ 0) :
    1 / 6 < Real.log q / Real.log z := by
  have h := upperRosserBoundaryMassAux_ne_zero_outer_log_lower
    0 hz hΔ hs hslo hp₀prime hp₁prime hp₁₀ hp₀cube hmass
  norm_num at h
  exact h

/-- The recursive support screen gives a uniform bound for every residual mass
at a fixed depth.  This supplies the boundedness input for finite Darboux
majorants independently of the sieve and of all prime coordinates. -/
theorem upperRosserBoundaryMassAux_le_fixedDepthScreen
    (k : ℕ) {z Δ s : ℝ} {q p₀ p₁ : ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) (hp₀prime : p₀.Prime) (hp₁prime : p₁.Prime)
    (hp₁₀ : p₁ < p₀) (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hp₁cut : (p₁ : ℝ) ≤ z) :
    LinearSieve.upperRosserBoundaryMassAux k
        (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
        (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
      ((((1 : ℝ) / (2 * 3 ^ (k + 1)))⁻¹) *
        (((1 : ℝ) / (2 * 3 ^ (k + 1)))⁻¹)) ^ k := by
  let c : ℝ := 1 / (2 * 3 ^ (k + 1))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hp₁pos : (0 : ℝ) < p₁ := by
    exact_mod_cast hp₁prime.pos
  have hp₁coord : Real.log p₁ / Real.log z ≤ 1 := by
    apply (div_le_iff₀ hlogz).2
    simpa using Real.strictMonoOn_log.monotoneOn hp₁pos
      (hp₁pos.trans_le hp₁cut) hp₁cut
  by_cases hmass : LinearSieve.upperRosserBoundaryMassAux k
      (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
      (Real.log q / Real.log z) (Real.log p₁ / Real.log z) = 0
  · rw [hmass]
    positivity
  · have hqcoord : c < Real.log q / Real.log z := by
      simpa [c] using upperRosserBoundaryMassAux_ne_zero_outer_log_lower
        k (by linarith) hΔ hs hslo hp₀prime hp₁prime hp₁₀ hp₀cube hmass
    simpa [c] using
      LinearSieve.upperRosserBoundaryMassAux_le_of_lower_bound
        k hc hqcoord.le hp₁coord

/-- All three exposed logarithmic coordinates of a nonzero fixed-depth residual
lie above the same depth-dependent screen. -/
theorem upperRosserBoundaryMassAux_ne_zero_outer_inner_log_lower
    (k : ℕ) {z Δ s : ℝ} {q p₀ p₁ : ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) (hqprime : q.Prime) (hp₀prime : p₀.Prime)
    (hp₁prime : p₁.Prime) (hq₀ : q < p₀) (hq₁ : q < p₁) (hp₁₀ : p₁ < p₀)
    (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hmass : LinearSieve.upperRosserBoundaryMassAux k
      (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
      (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≠ 0) :
    1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z ∧
      1 / (2 * 3 ^ (k + 1)) < Real.log p₀ / Real.log z ∧
        1 / (2 * 3 ^ (k + 1)) < Real.log p₁ / Real.log z := by
  have hq :=
    upperRosserBoundaryMassAux_ne_zero_outer_log_lower
      k hz hΔ hs hslo hp₀prime hp₁prime hp₁₀ hp₀cube hmass
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
  have hqp₀ : Real.log q / Real.log z < Real.log p₀ / Real.log z := by
    apply (div_lt_div_iff_of_pos_right hlogz).2
    exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₀pos).2
      (by exact_mod_cast hq₀)
  have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
  have hqp₁ : Real.log q / Real.log z < Real.log p₁ / Real.log z := by
    apply (div_lt_div_iff_of_pos_right hlogz).2
    exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
      (by exact_mod_cast hq₁)
  exact ⟨hq, hq.trans hqp₀, hq.trans hqp₁⟩

/-- A nonzero residual after the first Rosser pair confines all three prime
coordinates away from zero.  The distinguished-prime inequality is the recursive
cubic support; the other two follow from the ordering above `q`.  This supplies a
common lower cutoff for every depth-two logarithmic mesh. -/
theorem upperRosserBoundaryMassAux_zero_ne_zero_outer_inner_log_lower
    {z Δ s : ℝ} {q p₀ p₁ : ℕ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) (hqprime : q.Prime) (hp₀prime : p₀.Prime)
    (hp₁prime : p₁.Prime) (hq₀ : q < p₀) (hq₁ : q < p₁) (hp₁₀ : p₁ < p₀)
    (hp₀cube : p₀ ^ 3 < Nat.floor Δ + 1)
    (hmass : LinearSieve.upperRosserBoundaryMassAux 0
      (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
      (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≠ 0) :
    1 / 6 < Real.log q / Real.log z ∧
      1 / 6 < Real.log p₀ / Real.log z ∧
        1 / 6 < Real.log p₁ / Real.log z := by
  have h := upperRosserBoundaryMassAux_ne_zero_outer_inner_log_lower
    0 hz hΔ hs hslo hqprime hp₀prime hp₁prime hq₀ hq₁ hp₁₀ hp₀cube hmass
  norm_num at h
  exact h

/-- The complete discrete depth-two contribution is bounded by the two peeled
prime sums weighted by the continuous residual depth-zero mass.  This is the exact
finite majorant to which the two logarithmic partition estimates are applied. -/
theorem
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_one_le_residualBoundaryMass
    {S : BoundingSieve} {z Δ s : ℝ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 1 ≤
      ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ∑ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
            ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux 0
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · apply
      upperRosserBoundaryChainsFixedDepthDensity_one_le_residualBoundaryMassAux
        (fun p => S.nu p / (1 - S.nu p)) hz hΔ hs
    · simp
    · exact Nat.prime_of_mem_primeFactors hq
    · intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
    · intro p hp
      exact nu_div_one_sub_nonneg_of_mem (Finset.mem_filter.mp hp).1
  · exact nu_div_one_sub_nonneg_of_mem hq

/-- Induction step for a fixed-depth boundary comparison.  After screening the
distinguished prime at the exact depth-dependent support, any pointwise
majorant for the residual depth lifts through the exact two-prime recursion.
The function `E` records the residual induction error without hiding how it is
weighted by the two newly peeled coordinates. -/
theorem
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ_le_screenedResidualBoundaryMassAux_add
    (k : ℕ) (E : ℕ → ℕ → ℕ → ℝ)
    {S : BoundingSieve} {z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hmajorant :
      ∀ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ =>
            1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z),
        ∀ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          ∀ p₁ ∈
              (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p))
                ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q
                ((S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p => p < p₁)) k ≤
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z) +
                E q p₀ p₁) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1) ≤
      ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ =>
            1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z),
        (S.nu q / (1 - S.nu q)) *
          ∑ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
            ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                (LinearSieve.upperRosserBoundaryMassAux k
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z) (Real.log p₁ / Real.log z) +
                  E q p₀ p₁) := by
  rw [sum_mul_upperRosserBoundaryChainsFixedDepthDensity_eq_screened
    (fun p => S.nu p / (1 - S.nu p))
    (fun p => S.nu p / (1 - S.nu p)) (k + 1) hz hΔ hs hslo hcut]
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · apply LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_succ_le
      (fun p => S.nu p / (1 - S.nu p))
      (by simp) (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
    · intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
    · intro p hp
      exact nu_div_one_sub_nonneg_of_mem (Finset.mem_filter.mp hp).1
    · exact fun p₀ hp₀ p₁ hp₁ hp₁₀ hp₀cube =>
        hmajorant q hq p₀ hp₀ p₁
          (Finset.mem_filter.mpr ⟨hp₁, hp₁₀, hp₀cube⟩)
  · exact nu_div_one_sub_nonneg_of_mem (Finset.mem_filter.mp hq).1

/-- Error-free specialization of the fixed-depth recursion lift.  It isolates
the exact induction obligation: dominate every inherited residual carrier by
`upperRosserBoundaryMassAux k` with its actual upper endpoint. -/
theorem
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ_le_screenedResidualBoundaryMassAux
    (k : ℕ) {S : BoundingSieve} {z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hmajorant :
      ∀ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ =>
            1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z),
        ∀ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          ∀ p₁ ∈
              (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p))
                ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q
                ((S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p => p < p₁)) k ≤
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1) ≤
      ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ =>
            1 / (2 * 3 ^ (k + 1)) < Real.log q / Real.log z),
        (S.nu q / (1 - S.nu q)) *
          ∑ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
            ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux k
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z)
                  (Real.log p₁ / Real.log z) := by
  simpa using
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ_le_screenedResidualBoundaryMassAux_add
      k (fun _ _ _ => 0) hz hΔ hs hslo hcut
      (by
        intro q hq p₀ hp₀ p₁ hp₁
        simpa using hmajorant q hq p₀ hp₀ p₁ hp₁)

/-- The exact depth-two residual majorant may be restricted to the compact
box where all three logarithmic coordinates exceed `1 / 6`.  This is the
screened finite sum to which the nested Darboux partitions are applied. -/
theorem
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_one_le_screenedResidualBoundaryMass
    {S : BoundingSieve} {z Δ s : ℝ}
    (hz : 1 < z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 1 ≤
      ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => 1 / 6 < Real.log q / Real.log z),
        (S.nu q / (1 - S.nu q)) *
          ∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
              (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
            ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                1 / 6 < Real.log p₁ / Real.log z),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux 0
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
  calc
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 1 ≤
        ∑ q ∈ S.prodPrimes.primeFactors,
          (S.nu q / (1 - S.nu q)) *
            ∑ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
              ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
                (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux 0
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z) (Real.log p₁ / Real.log z) :=
      sum_mul_upperRosserBoundaryChainsFixedDepthDensity_one_le_residualBoundaryMass
        hz hΔ hs
    _ = ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => 1 / 6 < Real.log q / Real.log z),
          (S.nu q / (1 - S.nu q)) *
            ∑ p₀ ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
              ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
                (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux 0
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
      symm
      apply Finset.sum_subset
      · intro q hq
        exact (Finset.mem_filter.mp hq).1
      · intro q hq hqnot
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro p₀ hp₀
        apply Finset.sum_eq_zero
        intro p₁ hp₁
        have hqprime : q.Prime :=
          Nat.prime_of_mem_primeFactors hq
        have hp₀' := Finset.mem_filter.mp hp₀
        have hp₀prime : p₀.Prime :=
          Nat.prime_of_mem_primeFactors hp₀'.1
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₁base := Finset.mem_filter.mp hp₁'.1
        have hp₁prime : p₁.Prime :=
          Nat.prime_of_mem_primeFactors hp₁base.1
        have hmass :
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) = 0 := by
          by_contra hne
          have hscreen :=
            upperRosserBoundaryMassAux_zero_ne_zero_outer_inner_log_lower
              hz hΔ hs hslo hqprime hp₀prime hp₁prime hp₀'.2 hp₁base.2
                hp₁'.2.1 hp₁'.2.2 hne
          exact hqnot (Finset.mem_filter.mpr ⟨hq, hscreen.1⟩)
        simp [hmass]
    _ = ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => 1 / 6 < Real.log q / Real.log z),
          (S.nu q / (1 - S.nu q)) *
            ∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
              ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                    1 / 6 < Real.log p₁ / Real.log z),
                (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux 0
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqscreen := (Finset.mem_filter.mp hq).2
      have hqprime : q.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      have hp₀filter :
          (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
              (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z) =
            S.prodPrimes.primeFactors.filter (fun p => q < p) := by
        apply Finset.filter_eq_self.mpr
        intro p₀ hp₀
        have hp₀' := Finset.mem_filter.mp hp₀
        have hp₀prime : p₀.Prime :=
          Nat.prime_of_mem_primeFactors hp₀'.1
        have hlogz : 0 < Real.log z := Real.log_pos hz
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
        have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
        have hqp₀ : Real.log q / Real.log z < Real.log p₀ / Real.log z := by
          apply (div_lt_div_iff_of_pos_right hlogz).2
          exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₀pos).2
            (by exact_mod_cast hp₀'.2)
        exact hqscreen.trans hqp₀
      rw [hp₀filter]
      congr 1
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      have hp₁filter :
          (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                1 / 6 < Real.log p₁ / Real.log z) =
            (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1) := by
        apply Finset.filter_congr
        intro p₁ hp₁
        have hp₁base := Finset.mem_filter.mp hp₁
        have hp₁prime : p₁.Prime :=
          Nat.prime_of_mem_primeFactors hp₁base.1
        have hlogz : 0 < Real.log z := Real.log_pos hz
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
        have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
        have hqp₁ : Real.log q / Real.log z < Real.log p₁ / Real.log z := by
          apply (div_lt_div_iff_of_pos_right hlogz).2
          exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
            (by exact_mod_cast hp₁base.2)
        constructor
        · intro h
          exact ⟨h.1, h.2.1⟩
        · intro h
          exact ⟨h.1, h.2, hqscreen.trans hqp₁⟩
      rw [hp₁filter]

/-- One logarithmic cell of the inner `p₁`-sum in the depth-two residual
majorant.  The residual depth-zero mass is an indicator and hence is bounded by
one.  A possible prime on the closed right face is retained and paid for by the
fixed-depth atom bound `η`. -/
theorem
    sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_rpow_Icc_add_atom
    {S : BoundingSieve} {K z s x₀ a u v η : ℝ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hu : 0 < u) (huv : u ≤ v)
    (hzu : 2 ≤ z ^ u)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z ^ u ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ v)
    (hη : 0 ≤ η)
    (hatom : ∀ p ∈ T, S.nu p / (1 - S.nu p) ≤ η) :
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        LinearSieve.upperRosserBoundaryMassAux 0
          (s - x₀ - Real.log p / Real.log z) a
          (Real.log p / Real.log z) ≤
      v / u * (1 + K / (u * Real.log z)) - 1 + η := by
  have h := weighted_sum_nu_div_one_sub_le_of_rpow_Icc_add_atom
    hlocal hz hu huv hzu hT hinterval
    (M := 1) (η := η)
    (w := fun p => LinearSieve.upperRosserBoundaryMassAux 0
      (s - x₀ - Real.log p / Real.log z) a
      (Real.log p / Real.log z))
    (by norm_num)
    (by
      intro p hp
      rw [LinearSieve.upperRosserBoundaryMassAux_zero]
      split_ifs <;> norm_num)
    hη
    (by
      intro p hp
      rw [LinearSieve.upperRosserBoundaryMassAux_zero]
      split_ifs
      · simpa using hatom p hp
      · simpa using hη)
  simpa [mul_comm] using h

/-- Partitioned form of the inner `p₁` residual estimate.  It is the finite
upper Darboux sum used for the inner integral in
`upperRosserBoundaryMass 1`; every closed cell contributes its local-product
increment and one fixed-depth atom error. -/
theorem
    sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_rpow_partition_Icc_add_atoms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K z s x₀ a : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {u v η : ι → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i)
    (hzu : ∀ i, 2 ≤ z ^ (u i))
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T,
      z ^ (u (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ (v (cell p)))
    (hη : ∀ i, 0 ≤ η i)
    (hatom : ∀ p ∈ T, S.nu p / (1 - S.nu p) ≤ η (cell p)) :
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        LinearSieve.upperRosserBoundaryMassAux 0
          (s - x₀ - Real.log p / Real.log z) a
          (Real.log p / Real.log z) ≤
      ∑ i, (v i / u i * (1 + K / (u i * Real.log z)) - 1 + η i) := by
  have h := weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_atoms
    hlocal hz hu huv hzu hT hinterval
    (M := fun _ => 1) (η := η)
    (w := fun p => LinearSieve.upperRosserBoundaryMassAux 0
      (s - x₀ - Real.log p / Real.log z) a
      (Real.log p / Real.log z))
    (fun _ => by norm_num)
    (by
      intro p hp
      rw [LinearSieve.upperRosserBoundaryMassAux_zero]
      split_ifs <;> norm_num)
    hη
    (by
      intro p hp
      rw [LinearSieve.upperRosserBoundaryMassAux_zero]
      split_ifs
      · simpa using hatom p hp
      · simpa using hη (cell p))
  simpa [mul_comm] using h

/-- Partitioned inner residual estimate with one global budget for every closed
right-face atom.  Since the depth-zero residual mass is an indicator, the
weighted endpoint contribution is bounded by the unweighted normalized atom
mass appearing in `hatom`. -/
theorem
    sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_rpow_partition_Icc_add_global_atoms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K z s x₀ a η : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {u v : ι → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i)
    (hzu : ∀ i, 2 ≤ z ^ (u i))
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T,
      z ^ (u (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ (v (cell p)))
    (hatom :
      ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
          S.nu p / (1 - S.nu p) ≤ η) :
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        LinearSieve.upperRosserBoundaryMassAux 0
          (s - x₀ - Real.log p / Real.log z) a
          (Real.log p / Real.log z) ≤
      (∑ i, (v i / u i * (1 + K / (u i * Real.log z)) - 1)) + η := by
  have h := weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_global_atoms
    hlocal hz hu huv hzu hT hinterval
    (M := fun _ => 1)
    (w := fun p => LinearSieve.upperRosserBoundaryMassAux 0
      (s - x₀ - Real.log p / Real.log z) a
      (Real.log p / Real.log z))
    (by intro i; norm_num)
    (by
      intro p hp
      rw [LinearSieve.upperRosserBoundaryMassAux_zero]
      split_ifs <;> norm_num)
    (by
      calc
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
              LinearSieve.upperRosserBoundaryMassAux 0
                  (s - x₀ - Real.log p / Real.log z) a
                  (Real.log p / Real.log z) *
                (S.nu p / (1 - S.nu p)) ≤
            ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
              S.nu p / (1 - S.nu p) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpT := (Finset.mem_filter.mp hp).1
          apply mul_le_of_le_one_left
            (nu_div_one_sub_nonneg_of_mem (hT hpT))
          rw [LinearSieve.upperRosserBoundaryMassAux_zero]
          split_ifs <;> norm_num
        _ ≤ η := hatom)
  simpa [mul_comm] using h

/-- The union of all closed right faces of a logarithmic partition contains at
most one natural number for each cell.  This is the combinatorial reason that
endpoint errors cost the size of the fixed mesh, rather than the number of
primes being sieved. -/
theorem card_rpow_partition_right_faces_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {z : ℝ} {T : Finset ℕ} {cell : ℕ → ι} {b : ι → ℝ}
    (hupper : ∀ p ∈ T, (p : ℝ) ≤ z ^ (b (cell p))) :
    (T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p)))).card ≤
      Fintype.card ι := by
  let E := T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p)))
  have hinj : Set.InjOn cell (E : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpe : (p : ℝ) = z ^ (b (cell p)) :=
      le_antisymm (hupper p hp'.1) (le_of_not_gt hp'.2)
    have hqe : (q : ℝ) = z ^ (b (cell q)) :=
      le_antisymm (hupper q hq'.1) (le_of_not_gt hq'.2)
    have hpqR : (p : ℝ) = q := by
      rw [hpe, hqe, hpq]
    exact_mod_cast hpqR
  change E.card ≤ Fintype.card ι
  exact Finset.card_le_card_of_injOn cell
    (by intro p hp; simp) hinj

/-- A pointwise atom bound yields one global budget for all right faces of a
fixed logarithmic partition.  In particular, the loss is controlled by the
number of cells and is independent of the number of primes in the sieve. -/
theorem sum_rpow_partition_right_faces_le_card_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {z η : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {b : ι → ℝ} {w : ℕ → ℝ}
    (hη : 0 ≤ η)
    (hupper : ∀ p ∈ T, (p : ℝ) ≤ z ^ (b (cell p)))
    (hatom : ∀ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤ η) :
    ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p))),
        w p * (S.nu p / (1 - S.nu p)) ≤
      (Fintype.card ι : ℝ) * η := by
  let E := T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p)))
  calc
    ∑ p ∈ E, w p * (S.nu p / (1 - S.nu p)) ≤ ∑ _p ∈ E, η := by
      apply Finset.sum_le_sum
      intro p hp
      exact hatom p (Finset.mem_filter.mp hp).1
    _ = (E.card : ℝ) * η := by simp
    _ ≤ (Fintype.card ι : ℝ) * η := by
      apply mul_le_mul_of_nonneg_right _ hη
      exact_mod_cast card_rpow_partition_right_faces_le hupper

/-- For a fixed logarithmic mesh, all closed-face atoms are uniformly
negligible under the dimension-one local-product hypothesis.  The cutoff is
independent of the sieve, the partition assignment, and the face locations. -/
theorem exists_rpow_partition_right_faces_mass_le
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K ρ c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ)
          (cell : ℕ → ι) (b : ι → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, z ^ c ≤ (p : ℝ)) →
        (∀ p ∈ T, (p : ℝ) ≤ z ^ (b (cell p))) →
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p))),
            S.nu p / (1 - S.nu p) ≤ ρ := by
  let η := ρ / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hρ hden
  obtain ⟨z₀, hz₀, hatom⟩ :=
    exists_dimensionOne_atom_cutoff K η c hK hη hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z T cell b hz hlocal hT hlower hupper
  have hface :=
    sum_rpow_partition_right_faces_le_card_mul
      (S := S) (z := z) (T := T) (cell := cell) (b := b)
      (w := fun _ => 1) hη.le hupper (by
        intro p hp
        simpa using hatom S z p hz hlocal (hT hp) (hlower p hp))
  have hηeq : ((Fintype.card ι : ℝ) + 1) * η = ρ := by
    dsimp [η]
    field_simp
  calc
    ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p))),
        S.nu p / (1 - S.nu p) ≤
        (Fintype.card ι : ℝ) * η := by simpa using hface
    _ ≤ ρ := by nlinarith

/-- Uniform weighted Stieltjes comparison on an arbitrary fixed positive
logarithmic screen and an arbitrary finite closed partition.  This is the
depth-independent form of the screened comparison: the lower screen `c`, the
cell geometry, and the weight majorants are all parameters. -/
theorem exists_weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K ρ B c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (cell : ℕ → ι) (u v M : ι → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        (∀ i, c ≤ u i) → (∀ i, u i ≤ v i) →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T,
          z ^ (u (cell p)) ≤ (p : ℝ) ∧
            (p : ℝ) ≤ z ^ (v (cell p))) →
        (∀ i, 0 ≤ M i) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p)) →
        (∀ p ∈ T, w p ≤ B) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∑ i, M i *
            (v i / u i * (1 + K / (u i * Real.log z)) - 1)) + ρ := by
  let ρface := ρ / (B + 1)
  have hB1 : 0 < B + 1 := by linarith
  have hρface : 0 < ρface := div_pos hρ hB1
  obtain ⟨zA, hzA, hfaces⟩ :=
    exists_rpow_partition_right_faces_mass_le
      ι K ρface c hK hρface hc
  let z₀ := max zA ((2 : ℝ) ^ (1 / c))
  refine ⟨z₀, hzA.trans (le_max_left _ _), ?_⟩
  intro S z T w cell u v M hz hlocal hcu huv hT hinterval hM hw hwB
  have hzA_le : zA ≤ z := (le_max_left _ _).trans hz
  have hzbase : (2 : ℝ) ^ (1 / c) ≤ z :=
    (le_max_right _ _).trans hz
  have hz2 : 2 ≤ z := hzA.trans hzA_le
  have hz1 : 1 < z := by linarith
  have hzc : 2 ≤ z ^ c := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ = ((2 : ℝ) ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        field_simp
      _ ≤ z ^ c := Real.rpow_le_rpow (by positivity) hzbase hc.le
  have hfaceMass :
      ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
          S.nu p / (1 - S.nu p) ≤ ρface := by
    apply hfaces S z T cell v hzA_le hlocal hT
    · intro p hp
      exact
        (Real.rpow_le_rpow_of_exponent_le hz1.le (hcu (cell p))).trans
          (hinterval p hp).1
    · intro p hp
      exact (hinterval p hp).2
  have hweightedFaces :
      ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
          w p * (S.nu p / (1 - S.nu p)) ≤ ρ := by
    calc
      ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
          w p * (S.nu p / (1 - S.nu p)) ≤
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
          B * (S.nu p / (1 - S.nu p)) := by
            apply Finset.sum_le_sum
            intro p hp
            apply mul_le_mul_of_nonneg_right
              (hwB p (Finset.mem_filter.mp hp).1)
            exact nu_div_one_sub_nonneg_of_mem
              (hT (Finset.mem_filter.mp hp).1)
      _ = B * ∑ p ∈ T.filter
          (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
            S.nu p / (1 - S.nu p) := by rw [Finset.mul_sum]
      _ ≤ B * ρface := mul_le_mul_of_nonneg_left hfaceMass hB
      _ ≤ ρ := by
        calc
          B * ρface ≤ (B + 1) * ρface :=
            mul_le_mul_of_nonneg_right (by linarith) hρface.le
          _ = ρ := by
            dsimp [ρface]
            field_simp
  apply weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_global_atoms
    hlocal hz1
  · intro i
    exact hc.trans_le (hcu i)
  · exact huv
  · intro i
    exact hzc.trans
      (Real.rpow_le_rpow_of_exponent_le hz1.le (hcu i))
  · exact hT
  · exact hinterval
  · exact hM
  · exact hw
  · exact hweightedFaces

/-- The normalized prime mass above a fixed positive logarithmic screen is
bounded by one dimension-one local-product interval. -/
theorem sum_nu_div_one_sub_le_of_log_coordinate_lower
    {S : BoundingSieve} {K z c : ℝ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hc1 : c ≤ 1) (hzc : 2 ≤ z ^ c)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hcut : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hscreen : ∀ p ∈ P, c ≤ Real.log p / Real.log z) :
    ∑ p ∈ P, S.nu p / (1 - S.nu p) ≤
      Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1 := by
  apply sum_nu_div_one_sub_le_of_subset_interval hlocal hzc
  · calc
      z ^ c ≤ z ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hz.le hc1
      _ = z := by simp
      _ ≤ z + 1 := by linarith
  · exact hP
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hzpos : 0 < z := by linarith
    constructor
    · calc
        z ^ c ≤ z ^ (Real.log p / Real.log z) :=
          Real.rpow_le_rpow_of_exponent_le hz.le (hscreen p hp)
        _ = (p : ℝ) := by
          simpa [Real.logb] using
            (Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz) hpPos)
    · linarith [hcut p hp]

/-- A uniform pointwise residual error remains quantitative after both peeled
prime sums.  On a fixed positive logarithmic screen it costs at most the square
of the one-dimensional normalized prime mass bound. -/
theorem sum_pair_mul_residual_error_le_of_uniform
    (E : ℕ → ℕ → ℝ)
    {S : BoundingSieve} {K z c ε : ℝ} {D : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hc1 : c ≤ 1) (hzc : 2 ≤ z ^ c) (hε : 0 ≤ ε)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hcut : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hscreen : ∀ p ∈ P, c ≤ Real.log p / Real.log z)
    (hE : ∀ p₀ ∈ P,
      ∀ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        0 ≤ E p₀ p₁ ∧ E p₀ p₁ ≤ ε) :
    ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) * E p₀ p₁ ≤
      ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  let w : ℕ → ℝ := fun p => S.nu p / (1 - S.nu p)
  let R : ℝ :=
    Real.log (z + 1) / Real.log (z ^ c) *
      (1 + K / Real.log (z ^ c)) - 1
  have hw : ∀ p ∈ P, 0 ≤ w p :=
    fun p hp => nu_div_one_sub_nonneg_of_mem (hP hp)
  have hmass : ∑ p ∈ P, w p ≤ R := by
    simpa [w, R] using
      sum_nu_div_one_sub_le_of_log_coordinate_lower
        hlocal hz hc1 hzc hP hcut hscreen
  have hR : 0 ≤ R := (Finset.sum_nonneg hw).trans hmass
  calc
    ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) * E p₀ p₁ ≤
        ∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            w p₀ * w p₁ * ε := by
      apply Finset.sum_le_sum
      intro p₀ hp₀
      apply Finset.sum_le_sum
      intro p₁ hp₁
      apply mul_le_mul_of_nonneg_left (hE p₀ hp₀ p₁ hp₁).2
      exact mul_nonneg (hw p₀ hp₀)
        (hw p₁ (Finset.mem_filter.mp hp₁).1)
    _ ≤ ∑ p₀ ∈ P, w p₀ * (R * ε) := by
      apply Finset.sum_le_sum
      intro p₀ hp₀
      have hinner :
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D), w p₁ ≤ R := by
        calc
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D), w p₁ ≤
              ∑ p₁ ∈ P, w p₁ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro p hpP _
              exact hw p hpP
          _ ≤ R := hmass
      calc
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            w p₀ * w p₁ * ε =
            (w p₀ * ε) *
              ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D), w p₁ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          ring
        _ ≤ (w p₀ * ε) * R :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg (hw p₀ hp₀) hε)
        _ = w p₀ * (R * ε) := by ring
    _ = (∑ p ∈ P, w p) * (R * ε) := by rw [Finset.sum_mul]
    _ ≤ R * (R * ε) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg hR hε)
    _ = ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      dsimp [R]
      ring

end MathlibNt.SieveTheory.SwitchingPrinciple
