/-
A finite, source-indexed discrete Suzuki package.

`section14ExtendedV S n D z` is a total extension of the recurrence used only after
Section 14 support/domain reductions.  It is not Suzuki’s unconditional `V_n`.
It is indexed by the length `n` of the complete source
chain.  Its base `n = 1` is Suzuki's terminal cubic shell.  For `n >= 2` the
definition is the exact one-prime recurrence of Lemma 7.1, with natural levels
represented by `Nat.ceilDiv`: `D/p` in the source becomes `D ⌈/⌉ p`, preserving
strict integral inequalities.

`section14ExtendedT S N D z` is project notation for Suzuki's finite discrete
parity sum; Suzuki uses `T_N(D,z)` in Lemma 14.4 but reserves the displayed
Section 9 notation for its continuous counterpart.
-/
import MathlibNt.SieveTheory.LowerSuzukiDiscreteBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The finite Euler product `V(z)` on the supported prime carrier. -/
noncomputable def sourceDiscreteEuler (S : BoundingSieve) (z : ℕ) : ℝ :=
  ∏ p ∈ suzukiSupportedBelow S z, (1 - S.nu p)


/-- Source-selected indices `1 ≤ n ≤ N`, `n ≡ N (mod 2)`. -/
def sourceParityIndices (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n % 2 = N % 2)


end MathlibNt.SieveTheory
