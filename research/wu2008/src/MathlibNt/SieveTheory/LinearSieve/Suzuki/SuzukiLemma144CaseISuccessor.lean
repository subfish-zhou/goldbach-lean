import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedBaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# Lemma 14.4: Case-I successor and same-constant absorption

This is the maximal source-faithful reduction available in the current compiled
import cone.  It uses the literal finite (14.9) equality and the production
(14.10) assembler.  It assumes neither a `mainSum` bound, a Claim-14.5/14.6
conclusion, nor a Case-I producer.

The source files for the newer Case-I recurrence/endpoint modules are present,
but their `.olean` modules are absent from the production search path.  The
purported full internal Claim-14.6 source also does not rebuild: it imports a
staged declaration of `Section13HatAsymptoticContract` which collides with the
production declaration.  Therefore the exact three analytic estimates not yet
available as compiled theorems are exposed below, before terminal scalar
absorption:

* `hSigma0`: the low-prime source estimate supplied mathematically by Claim 14.5
  at the endpoint `σ`;
* `hSigma11`: the endpoint remainder after the finite-source-layer main term;
* `hSigma12`: the internal-Claim-14.6 contraction multiplier plus endpoint
  remainder.

These are source estimates, not renamed final conclusions.  `Σ₂` is retained in
(14.9) and separately eliminated by its exact Case-I zero identity.
-/

/-- The finite parity index set occurring in Suzuki's source `T_N`. -/
noncomputable def lemma144ParityIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n % 2 = N % 2

/-- Literal source predecessor sum used in (14.9)--(14.10). -/
noncomputable def lemma144SourcePred
    (S : BoundingSieve) (n D p : ℕ) : ℝ :=
  ∑ m ∈ lemma144ParityIndices n, suzukiSourceV S m D p

/-- Strict multiplier certificate for same-`C` absorption. -/
structure Lemma144StrictFactor where
  ρ : ℝ
  nonneg : 0 ≤ ρ
  lt_one : ρ < 1

/-- Actual finite (14.9), stated on its three literal source sums. -/
def Lemma144Equation149
    (S : BoundingSieve) (N D z : ℕ) (σ τ : ℝ) : Prop :=
  (∑ n ∈ lemma144ParityIndices N, suzukiSourceV S n D z) =
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
      S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p) +
    sigmaOne (suzukiSupportedBelow S z) S.nu (lemma144SourcePred S)
      N D σ τ +
    (∑ p ∈ (suzukiSupportedBelow S z).filter
        (fun p : ℕ => (D : ℝ) ^ (1 / τ) ≤ (p : ℝ)),
      S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p)

/-- The genuine `N-1 → N` Case-I successor reduction.  The same constant `C`
appears in `hIH`, in the contracted inherited budget, and in the conclusion.
No `C_N` is introduced.

The only induction use is `hIH`, consumed by the actual
`equation14_10_finset_assembly`.  The side allocation is strict in the analytic
sense `ρ < 1`, recorded by `q.lt_one`. -/
theorem lemma14_4_caseI_successor_sameC
    (S : BoundingSieve) (V : ℕ → ℝ)
    {N D z : ℕ} {β σ τ s C K Δ Vz E ρ e0 e11 e12 : ℝ}
    (hN2 : 2 ≤ N)
    (hτs : τ = s)
    (h149 : Lemma144Equation149 S N D z σ τ)
    (hSigma2Zero :
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / τ) ≤ (p : ℝ)),
        S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p) = 0)
    (hVz : Vz ≠ 0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ τ,
      0 ≤ S.nu p)
    (hIH : PointwiseInductionContract
      (suzukiSupportedBelow S z) (lemma144SourcePred S) V
      (fun _ _ _ => E) β C K Δ N D σ τ)
    (hSigma0 :
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
        S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p) ≤ e0)
    (hSigma11 :
      sigmaEleven (suzukiSupportedBelow S z) S.nu V Vz β N D σ τ ≤
        Vz * finiteSourceLayer 1 β N s + e11)
    (hSigma12 :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu V
          (fun _ _ _ => E) Vz C K Δ N D σ τ ≤
        ρ * (C * E) + e12)
    (q : Lemma144StrictFactor)
    (hq : q.ρ = ρ)
    (hside : e0 + e11 + e12 ≤ (1 - ρ) * (C * E)) :
    (∑ n ∈ lemma144ParityIndices N, suzukiSourceV S n D z) ≤
      Vz * finiteSourceLayer 1 β N s + C * E := by
  subst s
  have _hdepth : 0 < N - 1 := by omega
  have h14 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu V (lemma144SourcePred S)
    (fun _ _ _ => E) Vz β C K Δ N D σ τ hVz hnu hIH
  unfold Lemma144Equation149 at h149
  rw [h149, hSigma2Zero]
  have hstrict : ρ < 1 := by simpa [← hq] using q.lt_one
  calc
    (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
        S.nu p * lemma144SourcePred S (N - 1) (D ⌈/⌉ p) p) +
        sigmaOne (suzukiSupportedBelow S z) S.nu (lemma144SourcePred S)
          N D σ τ + 0
        ≤ e0 +
          (sigmaEleven (suzukiSupportedBelow S z) S.nu V Vz β N D σ τ +
            sigmaTwelve (suzukiSupportedBelow S z) S.nu V
              (fun _ _ _ => E) Vz C K Δ N D σ τ) := by
          linarith
    _ ≤ e0 + ((Vz * finiteSourceLayer 1 β N τ + e11) +
          (ρ * (C * E) + e12)) :=
      add_le_add le_rfl (add_le_add hSigma11 hSigma12)
    _ ≤ Vz * finiteSourceLayer 1 β N τ + C * E := by
      have _ := hstrict
      nlinarith [hside]

/-- Finite-depth termination, based at the genuine depth one.  Every successor
call decreases to `N-1`; hence a target `N ≤ depth` reaches the base after at
most `N-1` calls. -/
theorem lemma14_4_finite_depth_from_caseI_successor
    (depth : ℕ) (P : ℕ → Prop)
    (hbase : P 1)
    (hsucc : ∀ N, 2 ≤ N → N ≤ depth → P (N - 1) → P N) :
    ∀ N, 1 ≤ N → N ≤ depth → P N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN1 hNd
      by_cases hN : N = 1
      · simpa [hN] using hbase
      · exact hsucc N (by omega) hNd
          (ih (N - 1) (by omega) (by omega) (by omega))


end MathlibNt.SieveTheory
