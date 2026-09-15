import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144Equation1410

open SuzukiFiniteContinuousLayers
open SuzukiFiniteContinuousLayers.KappaOneModel

/-- The genuine global depth-`n` form of the Lemma 14.4 induction
hypothesis.  It is uniform in the natural cutoff `D'`, the sieve endpoint `z'`,
and every legal parity coordinate.  The endpoint is tied to the coordinate by
the source power relation; `Dmin` records the large-parameter threshold. -/
def GlobalDepthLemma144InductionHypothesis
    (T : ℕ → ℕ → ℕ → ℝ) (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (n Dmin : ℕ) : Prop :=
  ∀ D' z' : ℕ, Dmin ≤ D' → 2 ≤ D' → 2 ≤ z' →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain β n →
      ((D' : ℝ) ^ (1 / x) = (z' : ℝ)) →
      T n D' z' ≤
        V z' *
          (finiteSourceLayer 1 β n x +
            C * Real.exp (Real.sqrt K) * E n D' x *
              (Real.log (D' : ℝ)) ^ (-Δ))

/-- The earliest outer-geometry edge not supplied by the current (14.10)
carrier API.  It is deliberately frozen separately: this is exactly what is
needed to retain a prescribed global-IH cutoff after division by every carrier
prime, and is not itself an induction hypothesis or endpoint estimate. -/
def CarrierQuotientThresholdGeometry
    (support : Finset ℕ) (D Dmin : ℕ) (σ τ : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier support D σ τ, Dmin * p ≤ D

/-- A quotient-scale lower bound simultaneously verifies the induction
threshold and that the natural recursive cutoff is at least two. -/
theorem ceilDiv_ge_threshold_of_scale
    {D p Dmin : ℕ} (hp : 0 < p) (hscale : Dmin * p ≤ D) :
    Dmin ≤ D ⌈/⌉ p := by
  have hfloor : Dmin ≤ D / p := by
    rw [Nat.le_div_iff_mul_le hp]
    simpa [Nat.mul_comm] using hscale
  have hdivceil : D / p ≤ D ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_le_div_right
    omega
  exact hfloor.trans hdivceil

/-- The recursive logarithmic coordinate really parametrizes the natural
endpoint `p` by a real power.  Thus it is admissible for the global IH rather
than merely an unrelated pointwise coordinate. -/
theorem recursiveCoordinate_power_identity
    {D p : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ D ⌈/⌉ p) :
    (((D ⌈/⌉ p : ℕ) : ℝ) ^ (1 / recursiveCoordinate D p) = (p : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hqR : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) := by positivity
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))
  have hlogq : Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega)))
  rw [Real.rpow_def_of_pos hqR, recursiveCoordinate]
  field_simp [hlogp, hlogq]
  rw [Real.exp_log hpR]

/-- Suzuki's parity domains are upward closed. -/
theorem parityDomain_mono {β : ℝ} {n : ℕ} {x y : ℝ}
    (hx : x ∈ KappaOneModel.parityDomain β n) (hxy : x ≤ y) :
    y ∈ KappaOneModel.parityDomain β n := by
  unfold KappaOneModel.parityDomain at hx ⊢
  by_cases hodd : n % 2 = 1
  · rw [if_pos hodd] at hx ⊢
    exact hx.trans_le hxy
  · rw [if_neg hodd] at hx ⊢
    exact hx.trans hxy

/-- Internalize the global Lemma-14.4 induction hypothesis at every carrier
point of (14.10).

`hscale` is the exact remaining outer geometry: it says that every carrier
prime leaves a quotient above the global induction threshold.  From it we prove
both `⌈D/p⌉ ≥ Dmin ≥ 2` and `2p ≤ D`.  The recursive coordinate is then proved
to lie in `I_{N-1}` (rather than assumed there), and its power-coordinate
identity is checked before the global IH is instantiated.  No pointwise
induction contract is an input. -/
theorem pointwiseInductionContract_of_globalDepthIH
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D Dmin : ℕ) (σ τ : ℝ)
    (hDmin : 2 ≤ Dmin)
    (hprime : ∀ p ∈ support, p.Prime)
    (hscale : CarrierQuotientThresholdGeometry support D Dmin σ τ)
    (hinherited : ∀ p ∈ sigmaOneCarrier support D σ τ,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1))
    (hV : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ V p)
    (hC : 0 ≤ C)
    (hSource : ∀ p ∈ sigmaOneCarrier support D σ τ,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p))
    (hError : ∀ p ∈ sigmaOneCarrier support D σ τ,
      E (N - 1) (D ⌈/⌉ p) (recursiveCoordinate D p) ≤
        E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p))
    (hglobal : GlobalDepthLemma144InductionHypothesis
      T V E β C K Δ (N - 1) Dmin) :
    PointwiseInductionContract support T V E β C K Δ N D σ τ := by
  have hnatural : NaturalCeilPointwiseInductionContract
      support T V E β C K Δ N D σ τ := by
    intro p hpCarrier
    have hpSupport : p ∈ support := (Finset.mem_filter.mp hpCarrier).1
    have hpPrime : p.Prime := hprime p hpSupport
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hp0 : 0 < p := hpPrime.pos
    have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
      ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    have h2pD : 2 * p ≤ D :=
      (Nat.mul_le_mul_right p hDmin).trans (hscale p hpCarrier)
    have hrecursive : recursiveCoordinate D p ∈
        KappaOneModel.parityDomain β (N - 1) :=
      parityDomain_mono (hinherited p hpCarrier)
        (coordinate_bounds hp2 h2pD).1
    exact hglobal (D ⌈/⌉ p) p hqThreshold hq2 hp2
      (recursiveCoordinate D p) hrecursive
      (recursiveCoordinate_power_identity hp2 hq2)
  have hlog : ∀ p ∈ sigmaOneCarrier support D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    intro p hpCarrier
    have hpSupport : p ∈ support := (Finset.mem_filter.mp hpCarrier).1
    have hp0 : 0 < p := (hprime p hpSupport).pos
    have hqThreshold := ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))).le
  exact naturalCeilContract_to_sourceCoordinate support T V E β C K Δ N D σ τ
    hV hC hlog hSource hError hnatural


end SuzukiLemma144Equation1410
end MathlibNt.SieveTheory.SwitchingPrinciple
