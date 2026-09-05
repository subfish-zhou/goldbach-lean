import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionBoundary

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4 Case II: `N = 1` / odd-successor dispatcher

The concrete double-rounded Case-II endpoint starts at `2 ≤ N`, whereas the
parity domain still contains the genuine odd base `N = 1`.  This file keeps the
outer quantification over arbitrary odd `N` and performs the necessary split
before selecting either producer.
-/

/-- An odd natural depth is either the genuine base depth or an odd depth at
least three.  In particular, only the second branch may be sent to a theorem
requiring `2 ≤ N`. -/
theorem odd_eq_one_or_three_le (N : ℕ) (hN : Odd N) :
    N = 1 ∨ 3 ≤ N := by
  rcases hN with ⟨k, hk⟩
  omega

/-- Domain-preserving Case-II dispatcher at the natural ceiling.

`P` is the common conclusion expected by the surrounding Lemma-14.4 assembly.
At `N = 1`, that conclusion must be obtained from the actual source-native base
estimate.  At every other odd depth, the successor callback receives both
`Odd M` and `2 ≤ M`, exactly the depth hypotheses required by
`caseII_total_le_doubleRounded_direct_concrete_relative_natCeil`.

Thus the top-level depth remains arbitrary; in particular it is not silently
strengthened to `2 ≤ N`. -/
theorem lemma14_4_caseII_natCeil_base_successor_dispatcher
    {S : BoundingSieve} {D z N : ℕ} {s K : ℝ}
    {P : ℕ → ℝ → Prop}
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hD : 1 < (D : ℝ))
    (hdom : s ∈ suzukiParityDomainOne 2 N)
    (hs3 : s ≤ 3)
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hbase :
      suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
          (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) →
        P 1 s)
    (hsuccessor : ∀ M : ℕ, Odd M → 2 ≤ M →
      s ∈ suzukiParityDomainOne 2 M → P M s)
    (hN : Odd N) :
    P N s := by
  rcases odd_eq_one_or_three_le N hN with hN1 | hN3
  · subst N
    apply hbase
    exact lemma14_4_base_one_natCeil hz hD hdom hs3 hroot2 hK hlocal
  · exact hsuccessor N hN (by omega) hdom

/-- The same dispatcher with the successor producer restricted to the sharp
odd-successor range `3 ≤ M`.  This is convenient when the caller records the
stronger parity consequence, while the direct endpoint itself only consumes
`2 ≤ M`. -/
theorem lemma14_4_caseII_natCeil_base_odd_three_dispatcher
    {S : BoundingSieve} {D z N : ℕ} {s K : ℝ}
    {P : ℕ → ℝ → Prop}
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hD : 1 < (D : ℝ))
    (hdom : s ∈ suzukiParityDomainOne 2 N)
    (hs3 : s ≤ 3)
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hbase :
      suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
          (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) →
        P 1 s)
    (hoddSuccessor : ∀ M : ℕ, Odd M → 3 ≤ M →
      s ∈ suzukiParityDomainOne 2 M → P M s)
    (hN : Odd N) :
    P N s := by
  apply lemma14_4_caseII_natCeil_base_successor_dispatcher
    hz hD hdom hs3 hroot2 hK hlocal hbase
  intro M hM hM2 hMdom
  exact hoddSuccessor M hM (by
    rcases odd_eq_one_or_three_le M hM with hM1 | hM3
    · omega
    · exact hM3) hMdom
  exact hN

-- Audited source signature (in `C2DoubleRoundedDirectAssembly.lean`):
-- `caseII_total_le_doubleRounded_direct_concrete_relative_natCeil` consumes
-- `(hN : Odd N) (hN2 : 2 ≤ N)`.  Its production import object
-- `MathlibNt.SieveTheory.SuzukiRoundedEndpointTransport.olean` is currently
-- absent, so this standalone dispatcher deliberately does not import that
-- unavailable cone.

end MathlibNt.SieveTheory
