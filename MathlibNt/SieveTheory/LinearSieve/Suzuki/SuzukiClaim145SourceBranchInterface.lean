import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceSigmaFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SmallDHighCoordinate

open scoped Classical BigOperators

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Claim 14.5: source Case-A / Case-B interface

This is the source branch dispatcher, not the later Lemma-14.4 Case-I/Case-II
split.  Its public disjunction is literally

`log D ≤ C1 * K^Θ ∨ sourceSigma D d ≤ s`.

Every branch contract below returns the actual discrete Claim-14.5 inequality.
In particular, the open low-`s` scalar target and the high-`s` logarithmic-gain
lemma are not accepted as substitutes for a closed Case-A branch.
-/

/-- Claim 14.5 for the actual discrete parity sum and the literal natural
ceiling cutoff attached to the coordinate `s`. -/
def ActualClaim145BoundAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D : ℕ) (d Δ K s C145 : ℝ) : Prop :=
  suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
    C145 * claim14_5Scale S H N (D : ℝ) d Δ
      (sourceSigma (D : ℝ) d) K s

/-- The Claim-14.5 scale is nonnegative on its source domain.  This permits
branch constants to be enlarged without hiding any analytic premise. -/
theorem claim14_5Scale_nonneg_on_source_domain
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ K s : ℝ}
    (hH : Section13HatSourceContract H) (hD : 2 ≤ D) (hs : 2 ≤ s) :
    0 ≤ claim14_5Scale S H N (D : ℝ) d Δ
      (sourceSigma (D : ℝ) d) K s := by
  have hD1 : (1 : ℝ) < (D : ℝ) := by
    exact_mod_cast (show 1 < D by omega)
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hσ : 0 < sourceSigma (D : ℝ) d := sourceSigma_pos_of_nat_two_le hD
  have hs0 : 0 < s := by linarith
  have hV : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    unfold claim14_5VProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
  have hE : 0 ≤ errorEnvelope H N (D : ℝ) d s :=
    errorEnvelope_nonneg H N hD1 hs0.le
      (hH.toSection13HatContract.positive _ s hs0).le
  unfold claim14_5Scale
  positivity

/-- Enlarging the multiplicative constant preserves the actual Claim bound. -/
theorem ActualClaim145BoundAt.mono_constant
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ K s C C' : ℝ}
    (hH : Section13HatSourceContract H) (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hCC' : C ≤ C')
    (h : ActualClaim145BoundAt S H N D d Δ K s C) :
    ActualClaim145BoundAt S H N D d Δ K s C' := by
  exact h.trans (mul_le_mul_of_nonneg_right hCC'
    (claim14_5Scale_nonneg_on_source_domain S H hH hD hs))

/-- The bounded-`K` piece suppressed by the paper's implicit-constant notation.
The constant is chosen before `K,N,D,s`; hence this is genuinely uniform on
`2 ≤ K ≤ K0`, rather than a pointwise compactness assertion. -/
def Claim145CaseABoundedKClosed
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C1 Θ K0 CA : ℝ) : Prop :=
  ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
    2 ≤ K → K ≤ K0 → HasDimensionOneLocalProductBound S K →
    2 ≤ D → 2 ≤ s → Real.log (D : ℝ) ≤ C1 * K ^ Θ →
    ActualClaim145BoundAt S H N D d Δ K s CA

/-- Large-`K`, low-coordinate half of source Case A.  This contract is closed
only when it returns the final actual bound, not merely the frozen big-O scalar
target from `C2Claim145CaseALowS`. -/
def Claim145CaseALargeKLowSClosed
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C1 Θ K0 CA : ℝ) : Prop :=
  ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
    K0 ≤ K → HasDimensionOneLocalProductBound S K →
    2 ≤ D → 2 ≤ s → s ≤ Real.sqrt K / Real.log K →
    Real.log (D : ℝ) ≤ C1 * K ^ Θ →
    ActualClaim145BoundAt S H N D d Δ K s CA

/-- Large-`K`, high-coordinate half of source Case A.  The logarithmic-gain
lemmas are upstream ingredients; this contract demands their completed
composition with Lemma 14.3 and Proposition 13.1(ii). -/
def Claim145CaseALargeKHighSClosed
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C1 Θ K0 CA : ℝ) : Prop :=
  ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
    K0 ≤ K → HasDimensionOneLocalProductBound S K →
    2 ≤ D → 2 ≤ s → Real.sqrt K / Real.log K ≤ s →
    Real.log (D : ℝ) ≤ C1 * K ^ Θ →
    ActualClaim145BoundAt S H N D d Δ K s CA

/-- Honest assembly of source Case A, including the bounded-`K` range. -/
theorem claim145_caseA_closed_of_boundedK_lowS_highS
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ K0 CA : ℝ}
    (hbounded : Claim145CaseABoundedKClosed S H d Δ C1 Θ K0 CA)
    (hlow : Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 CA)
    (hhigh : Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 CA) :
    ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
      2 ≤ K → HasDimensionOneLocalProductBound S K →
      2 ≤ D → 2 ≤ s → Real.log (D : ℝ) ≤ C1 * K ^ Θ →
      ActualClaim145BoundAt S H N D d Δ K s CA := by
  intro K N D s hK hlocal hD hs hsmall
  by_cases hKK0 : K ≤ K0
  · exact hbounded K N D s hK hKK0 hlocal hD hs hsmall
  · have hK0K : K0 ≤ K := (lt_of_not_ge hKK0).le
    rcases le_total s (Real.sqrt K / Real.log K) with hlowS | hhighS
    · exact hlow K N D s hK0K hlocal hD hs hlowS hsmall
    · exact hhigh K N D s hK0K hlocal hD hs hhighS hsmall

/-- Source Case B.  `CB` and `C1min` are fixed before `C1`; this makes the paper's
assertion that the Case-B implicit constant is independent of `C1` visible in
the quantifier order.  `C1min ≤ C1` records that the source first chooses `C1`
sufficiently large. -/
def Claim145CaseBClosed
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ Θ C1min CB : ℝ) : Prop :=
  ∀ (C1 K : ℝ) (N D : ℕ) (s : ℝ),
    C1min ≤ C1 → 2 ≤ K → HasDimensionOneLocalProductBound S K →
    2 ≤ D → 2 ≤ s → C1 * K ^ Θ < Real.log (D : ℝ) →
    sourceSigma (D : ℝ) d ≤ s →
    ActualClaim145BoundAt S H N D d Δ K s CB

/-- Complete source-disjunction assembler.  Case A may have a `C1`-dependent
constant `CA`; Case B uses a constant `CB` selected independently of `C1`.
The final public constant is their maximum. -/
theorem claim145_actual_of_source_disjunction
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ C1min CA CB K s : ℝ} {N D : ℕ}
    (hH : Section13HatSourceContract H)
    (hC1 : C1min ≤ C1) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hA : ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
      2 ≤ K → HasDimensionOneLocalProductBound S K →
      2 ≤ D → 2 ≤ s → Real.log (D : ℝ) ≤ C1 * K ^ Θ →
      ActualClaim145BoundAt S H N D d Δ K s CA)
    (hB : Claim145CaseBClosed S H d Δ Θ C1min CB)
    (hregime : Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
      sourceSigma (D : ℝ) d ≤ s) :
    ActualClaim145BoundAt S H N D d Δ K s (max CA CB) := by
  rcases hregime with hsmall | hlargeS
  · exact (hA K N D s hK hlocal hD hs hsmall).mono_constant
      S H hH hD hs (le_max_left _ _)
  · by_cases hsmall : Real.log (D : ℝ) ≤ C1 * K ^ Θ
    · exact (hA K N D s hK hlocal hD hs hsmall).mono_constant
        S H hH hD hs (le_max_left _ _)
    · have hlargeD : C1 * K ^ Θ < Real.log (D : ℝ) := lt_of_not_ge hsmall
      exact (hB C1 K N D s hC1 hK hlocal hD hs hlargeD hlargeS).mono_constant
        S H hH hD hs (le_max_right _ _)

/-- End-to-end branch assembly.  This theorem accepts exactly three completed
Case-A leaves (bounded `K`, large-`K` low `s`, and large-`K` high `s`) plus the
completed Case-B leaf, and returns the literal source disjunction.  None of the
four inputs may be replaced by a scalar target, logarithmic gain, or endpoint-
only theorem. -/
theorem claim145_actual_of_closed_source_branches
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ K0 C1min CA CB K s : ℝ} {N D : ℕ}
    (hH : Section13HatSourceContract H)
    (hC1 : C1min ≤ C1) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hbounded : Claim145CaseABoundedKClosed S H d Δ C1 Θ K0 CA)
    (hlow : Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 CA)
    (hhigh : Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 CA)
    (hB : Claim145CaseBClosed S H d Δ Θ C1min CB)
    (hregime : Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨
      sourceSigma (D : ℝ) d ≤ s) :
    ActualClaim145BoundAt S H N D d Δ K s (max CA CB) := by
  apply claim145_actual_of_source_disjunction S H hH hC1 hK hlocal hD hs
    (claim145_caseA_closed_of_boundedK_lowS_highS S H hbounded hlow hhigh)
    hB hregime


end MathlibNt.SieveTheory
