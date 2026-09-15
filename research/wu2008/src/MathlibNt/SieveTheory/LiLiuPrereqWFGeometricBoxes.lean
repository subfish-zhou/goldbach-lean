import MathlibNt.SieveTheory.LiLiuPrereqWFGeometry

/-!
# The actual geometric prime boxes

The lower grid is `D^(ε²(1+θ)^j)` and each box is the half-open interval
from one grid point to the next, intersected with a fixed finite sieve
prime set. Thus distinct labels give disjoint prime ranges, while repeated
labels retain all their divided-power multiplicity.

The final theorem specializes to Iwaniec's `θ = ε⁹` and source numerical
admissibility. It includes a fixed supplied small-prime weight. The subsequent
`LiLiuPrereqWFSmallRosser` supplies concrete upper/lower weights and their
finite sieve inequalities; their density remains a separate obligation.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset LiLiuPrereqWFAdmissibility

noncomputable def geometricLower (D ε θ : ℝ) (j : ℕ) : ℝ :=
  D ^ (ε ^ 2 * (1 + θ) ^ j)

theorem geometricLower_one_le {D ε θ : ℝ} (hD : 1 ≤ D) (hθ : 0 ≤ θ) (j : ℕ) :
    1 ≤ geometricLower D ε θ j :=
  Real.one_le_rpow hD (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _))

theorem geometricLower_monotone {D ε θ : ℝ} (hD : 1 ≤ D) (hθ : 0 ≤ θ) :
    Monotone (geometricLower D ε θ) := by
  intro i j hij
  exact Real.rpow_le_rpow_of_exponent_le hD
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hij) (sq_nonneg ε))

theorem geometricLower_succ {D ε θ : ℝ} (hD : 0 ≤ D) (j : ℕ) :
    geometricLower D ε θ (j + 1) = geometricLower D ε θ j ^ (1 + θ) := by
  unfold geometricLower
  rw [← Real.rpow_mul hD, pow_succ (1 + θ) j, mul_assoc]

/-- `P` is the fixed finite set of sieve primes below the desired cutoff. -/
noncomputable def geometricPrimeBox (P : Finset ℕ) (D ε θ : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => p.Prime ∧ geometricLower D ε θ j ≤ (p : ℝ) ∧
    (p : ℝ) < geometricLower D ε θ (j + 1))

@[simp]
theorem mem_geometricPrimeBox (P : Finset ℕ) (D ε θ : ℝ) (j p : ℕ) :
    p ∈ geometricPrimeBox P D ε θ j ↔ p ∈ P ∧ p.Prime ∧
      geometricLower D ε θ j ≤ (p : ℝ) ∧
      (p : ℝ) < geometricLower D ε θ (j + 1) := by
  classical
  simp only [geometricPrimeBox, Finset.mem_filter]

theorem geometricPrimeBox_upper (P : Finset ℕ) {D ε θ : ℝ} (hD : 0 ≤ D)
    (j p : ℕ) (hp : p ∈ geometricPrimeBox P D ε θ j) :
    (p : ℝ) < geometricLower D ε θ j ^ (1 + θ) := by
  rw [← geometricLower_succ hD]
  exact (mem_geometricPrimeBox _ _ _ _ _ _).mp hp |>.2.2.2

theorem geometricPrimeBox_disjoint (P : Finset ℕ) {D ε θ : ℝ}
    (hD : 1 ≤ D) (hθ : 0 ≤ θ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (geometricPrimeBox P D ε θ i) (geometricPrimeBox P D ε θ j) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨_, _, hil, hiu⟩ := (mem_geometricPrimeBox _ _ _ _ _ _).mp hpi
  obtain ⟨_, _, hjl, hju⟩ := (mem_geometricPrimeBox _ _ _ _ _ _).mp hpj
  rcases lt_or_gt_of_ne hij with h | h
  · have hm := geometricLower_monotone (ε := ε) hD hθ (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hm.trans hjl)) hiu
  · have hm := geometricLower_monotone (ε := ε) hD hθ (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hm.trans hil)) hju

noncomputable def geometricSmallPrimes (P : Finset ℕ) (D ε : ℝ) : Finset ℕ :=
  P.filter (fun p => p.Prime ∧ (p : ℝ) < D ^ (ε ^ 2))

theorem geometricSmallPrimes_disjoint (P : Finset ℕ) {D ε θ : ℝ}
    (hD : 1 ≤ D) (hθ : 0 ≤ θ) (s : Finset ℕ) :
    Disjoint (geometricSmallPrimes P D ε) (s.biUnion (geometricPrimeBox P D ε θ)) := by
  classical
  simp only [Finset.disjoint_biUnion_right]
  intro j _
  apply Finset.disjoint_left.mpr
  intro p hp hpb
  have hsmall : (p : ℝ) < D ^ (ε ^ 2) := (Finset.mem_filter.mp hp).2.2
  have hlarge := ((mem_geometricPrimeBox _ _ _ _ _ _).mp hpb).2.2.1
  have hzero := geometricLower_monotone (ε := ε) hD hθ (Nat.zero_le j)
  have hbase : D ^ (ε ^ 2) ≤ geometricLower D ε θ j := by
    simpa only [geometricLower, pow_zero, mul_one] using hzero
  exact (not_lt_of_ge (hbase.trans hlarge)) hsmall

/-- A fixed normalized box term with its small coefficient function. -/
noncomputable def geometricBoxTerm (P : Finset ℕ) (D ε θ : ℝ)
    (input : List ℕ) (ψ : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ψ * boxProduct input.toFinset (geometricPrimeBox P D ε θ) input.count

theorem geometricBoxTerm_wellFactorable (P : Finset ℕ)
    {upper : Bool} {D ε θ : ℝ} (input : List ℕ) (ψ : ArithmeticFunction ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hθ : 0 ≤ θ) (hεθ : ε ≤ 1 + θ)
    (hadm : Admissible upper (geometricLower D ε θ) D input)
    (hψp : PrimeSupported (geometricSmallPrimes P D ε) ψ)
    (hψb : BoundedOne ψ) (hψs : SupportedAt ψ (D ^ ε)) :
    WellFactorable (geometricBoxTerm P D ε θ input ψ) (D ^ (1 + ε + θ)) := by
  apply admissible_smallWeight_wellFactorable input (geometricPrimeBox P D ε θ)
    (geometricLower D ε θ) (geometricSmallPrimes P D ε) ψ hD hε hθ hεθ hadm
  · intro j _ p hp _
    exact (geometricPrimeBox_upper P (le_trans zero_le_one hD) j p hp).le
  · intro i _ j _ hij
    exact geometricPrimeBox_disjoint P hD hθ hij
  · exact geometricSmallPrimes_disjoint P hD hθ _
  · exact hψp
  · exact hψb
  · exact hψs

/-- Source parameters: `θ = ε⁹`, `0 < ε < 1/8`, `D ≥ 2`. No numerical
prefix budget, disjointness, or support allocation is left as an input. -/
theorem iwaniec_boxTerm_wellFactorable (P : Finset ℕ)
    {upper : Bool} {D ε : ℝ} (input : List ℕ) (ψ : ArithmeticFunction ℝ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hadm : Admissible upper (geometricLower D ε (ε ^ 9)) D input)
    (hψp : PrimeSupported (geometricSmallPrimes P D ε) ψ)
    (hψb : BoundedOne ψ) (hψs : SupportedAt ψ (D ^ ε)) :
    WellFactorable (geometricBoxTerm P D ε (ε ^ 9) input ψ) (D ^ (1 + ε + ε ^ 9)) :=
  geometricBoxTerm_wellFactorable P input ψ (by linarith) hε.le
    (pow_nonneg hε.le _) (by nlinarith [pow_nonneg hε.le 9]) hadm hψp hψb hψs

end MathlibNt.SieveTheory.LiLiuPrereqWF
