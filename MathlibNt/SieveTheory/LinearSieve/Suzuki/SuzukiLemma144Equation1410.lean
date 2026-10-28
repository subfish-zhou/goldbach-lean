import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseISourceRecurrence

/-!
# Suzuki (14.10): finite assembly of the pointwise induction hypothesis

This file isolates exactly the finite step which turns the pointwise induction
hypothesis for `T_{N-1}(⌈D/p⌉,p)` into `Σ₁ ≤ Σ₁₁ + Σ₁₂`.
The recursive natural argument always uses ceiling division.  The cutoff and
continuous-layer coordinates are displayed explicitly as real powers/logarithms.
No endpoint estimate for either resulting sum is assumed.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144Equation1410

open SuzukiFiniteContinuousLayers
open SuzukiLemma144KappaOne

/-- The finite prime carrier in the range
`D^(1/σ) ≤ p < D^(1/τ)`.  The casts make the real-power cutoffs explicit. -/
noncomputable def sigmaOneCarrier
    (support : Finset ℕ) (D : ℕ) (σ τ : ℝ) : Finset ℕ :=
  support.filter fun p =>
    (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧ (p : ℝ) < (D : ℝ) ^ (1 / τ)

/-- The continuous coordinate at the inherited depth in (14.10). -/
noncomputable def inheritedCoordinate (D p : ℕ) : ℝ :=
  Real.log (D : ℝ) / Real.log (p : ℝ) - 1

/-- The coordinate obtained by applying the induction theorem literally at the
natural recursive argument `D ⌈/⌉ p`. -/
noncomputable def recursiveCoordinate (D p : ℕ) : ℝ :=
  Real.log ((D ⌈/⌉ p : ℕ) : ℝ) / Real.log (p : ℝ)


lemma ceilDiv_mul_bounds {D p : ℕ} (hp : 0 < p) :
    D ≤ (D ⌈/⌉ p) * p ∧ (D ⌈/⌉ p) * p ≤ D + p - 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  constructor
  · have hmod := Nat.mod_lt (D + p - 1) hp
    have hdecomp := Nat.div_add_mod (D + p - 1) p
    have hcomm : p * ((D + p - 1) / p) = ((D + p - 1) / p) * p := Nat.mul_comm _ _
    omega
  · exact Nat.div_mul_le_self _ _

lemma inheritedCoordinate_eq_log_div (D p : ℕ) (hD : 0 < D) (hp : 2 ≤ p) :
    inheritedCoordinate D p = Real.log ((D : ℝ) / p) / Real.log p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
  rw [inheritedCoordinate, Real.log_div (Nat.cast_ne_zero.mpr (ne_of_gt hD))
    (Nat.cast_ne_zero.mpr (by omega))]
  field_simp [hlogp]

/-- Exact direction and a uniform explicit size bound for the ceiling
perturbation.  The hypothesis `2 * p ≤ D` is the natural-number form of the
range condition `2 ≤ D / p`. -/
theorem coordinate_bounds {D p : ℕ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) :
    inheritedCoordinate D p ≤ recursiveCoordinate D p ∧
      recursiveCoordinate D p ≤ inheritedCoordinate D p +
        Real.log (3 / 2 : ℝ) / Real.log (p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hD0 : 0 < D := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < p by omega))
  have hmul := ceilDiv_mul_bounds (D := D) (p := p) hp0
  have hlowerNat := hmul.1
  have hupperNat := hmul.2
  have hlowerR : (D : ℝ) / p ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast hlowerNat
  have hDdivpos : (0 : ℝ) < (D : ℝ) / p := div_pos (by positivity) hpR
  have hqpos : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) :=
    hDdivpos.trans_le hlowerR
  have hloglower : Real.log ((D : ℝ) / p) ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hDdivpos hqpos hlowerR
  have hupperProdR : (((D ⌈/⌉ p : ℕ) : ℝ) * p) ≤ (3 / 2 : ℝ) * D := by
    have hraw : (((D ⌈/⌉ p : ℕ) : ℝ) * p) ≤ (D : ℝ) + p := by
      have : (D ⌈/⌉ p) * p ≤ D + p := hupperNat.trans (Nat.sub_le _ _)
      exact_mod_cast this
    have hhalf : (2 : ℝ) * p ≤ D := by exact_mod_cast hDp
    linarith
  have hupperR : (((D ⌈/⌉ p : ℕ) : ℝ)) ≤ (3 / 2 : ℝ) * ((D : ℝ) / p) := by
    calc
      (((D ⌈/⌉ p : ℕ) : ℝ)) ≤ ((3 / 2 : ℝ) * D) / p :=
        (le_div_iff₀ hpR).2 hupperProdR
      _ = (3 / 2 : ℝ) * ((D : ℝ) / p) := by ring
  have hthreepos : (0 : ℝ) < 3 / 2 := by norm_num
  have hrhspos : 0 < (3 / 2 : ℝ) * ((D : ℝ) / p) := mul_pos hthreepos hDdivpos
  have hlogupper : Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤
      Real.log ((3 / 2 : ℝ) * ((D : ℝ) / p)) :=
    Real.strictMonoOn_log.monotoneOn hqpos hrhspos hupperR
  rw [inheritedCoordinate_eq_log_div D p hD0 hp]
  constructor
  · exact (div_le_div_iff_of_pos_right hlogp).2 hloglower
  · rw [Real.log_mul (ne_of_gt hthreepos) (ne_of_gt hDdivpos)] at hlogupper
    calc
      Real.log ((D ⌈/⌉ p : ℕ) : ℝ) / Real.log (p : ℝ) ≤
          (Real.log (3 / 2 : ℝ) + Real.log ((D : ℝ) / p)) / Real.log p :=
        (div_le_div_iff_of_pos_right hlogp).2 hlogupper
      _ = Real.log ((D : ℝ) / p) / Real.log p +
          Real.log (3 / 2 : ℝ) / Real.log p := by ring


/-- Proposition 9.3 has exactly the useful direction: since ceiling division
increases the coordinate, antitonicity makes the literal recursive main term no
larger than the source coordinate main term. -/
theorem finiteSourceLayer_recursive_le_inherited
    {β : ℝ} (hβ : 1 < β) (N D p : ℕ) (hp : 2 ≤ p) (hDp : 2 * p ≤ D)
    (hx : inheritedCoordinate D p ∈ KappaOneModel.parityDomain β N)
    (hy : recursiveCoordinate D p ∈ KappaOneModel.parityDomain β N) :
    finiteSourceLayer 1 β N (recursiveCoordinate D p) ≤
      finiteSourceLayer 1 β N (inheritedCoordinate D p) := by
  exact finiteSourceLayer_antitoneOn_parityDomain hβ N hx hy (coordinate_bounds hp hDp).1


/-- The logarithmic loss at the literal ceiling quotient is no larger than the
source logarithmic loss at `D / p`.  Positivity is recorded explicitly: the
assumption `2 * p ≤ D` puts both logarithm arguments in `(1,∞)`, while
`0 ≤ Δ` makes the exponent `-Δ` nonpositive. -/
theorem ceilDiv_log_rpow_neg_le_div_log_rpow_neg
    {D p : ℕ} {Δ : ℝ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) (hΔ : 0 ≤ Δ) :
    (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) ≤
      (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hdiv2 : (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast hDp
  have hdivpos : (0 : ℝ) < (D : ℝ) / (p : ℝ) := zero_lt_two.trans_le hdiv2
  have hceilLower : (D : ℝ) / (p : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast (ceilDiv_mul_bounds (D := D) (p := p) hp0).1
  have hceilpos : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) := hdivpos.trans_le hceilLower
  have hlogdiv : 0 < Real.log ((D : ℝ) / (p : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hdiv2)
  have hlogceil : Real.log ((D : ℝ) / (p : ℝ)) ≤
      Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hdivpos hceilpos hceilLower
  exact Real.rpow_le_rpow_of_nonpos hlogdiv hlogceil (neg_nonpos.mpr hΔ)

/-- For a fixed nonnegative source coordinate, the explicit error envelope is
antitone in its cutoff argument.  This is the cutoff-coordinate comparison
needed because `⌈D/p⌉ ≥ D/p`. -/
theorem errorEnvelope_antitone_cutoff
    (H : Section13HatLayers) (n : ℕ) {X Y d s : ℝ}
    (hX : 1 < X) (hXY : X ≤ Y) (hs : 0 ≤ s)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth n) s) :
    errorEnvelope H n Y d s ≤ errorEnvelope H n X d s := by
  have hY : 1 < Y := hX.trans_le hXY
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hlogXY : Real.log X ≤ Real.log Y :=
    Real.strictMonoOn_log.monotoneOn (zero_lt_one.trans hX)
      (zero_lt_one.trans hY) hXY
  have hsd : 0 ≤ s ^ d := Real.rpow_nonneg hs _
  have hquot : s ^ d / Real.log Y ≤ s ^ d / Real.log X :=
    div_le_div_of_nonneg_left hsd hlogX hlogXY
  have hbase : 1 + s ^ d / Real.log Y ≤ 1 + s ^ d / Real.log X := by
    linarith
  have hbaseY : 0 ≤ 1 + s ^ d / Real.log Y := by
    have : 0 ≤ s ^ d / Real.log Y := div_nonneg hsd hlogY.le
    linarith
  have hpow := Real.rpow_le_rpow hbaseY hbase hs
  have hspow : 0 ≤ s ^ (H.kappaHat - 1 + 1) := Real.rpow_nonneg hs _
  unfold errorEnvelope
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow hspow) hT


/-- The induction theorem applied literally at the natural recursive argument.
Unlike `PointwiseInductionContract`, this contract does not silently replace
`log ⌈D/p⌉ / log p` by `log D / log p - 1`. -/
def NaturalCeilPointwiseInductionContract
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier support D σ τ,
    T (N - 1) (D ⌈/⌉ p) p ≤
      V p *
        (finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) +
          C * Real.exp (Real.sqrt K) *
            E (N - 1) (D ⌈/⌉ p) (recursiveCoordinate D p) *
              (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ))


/-- Narrow pointwise induction contract used in (14.10).

The discrete recursive argument is `D ⌈/⌉ p` (natural ceiling division), while
both occurrences of the continuous coordinate are exactly
`log D / log p - 1`. -/
def PointwiseInductionContract
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier support D σ τ,
    T (N - 1) (D ⌈/⌉ p) p ≤
      V p *
        (finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) +
          C * Real.exp (Real.sqrt K) *
            E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) *
              (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ))

/-- Full closure criterion.  The finite source layer and the error envelope
must both be antitone across the ceiling displacement (or otherwise satisfy the
two displayed pointwise inequalities).  Without `hError`, only
`naturalCeilContract_to_perturbed` is available. -/
theorem naturalCeilContract_to_sourceCoordinate
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hV : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ V p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier support D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSource : ∀ p ∈ sigmaOneCarrier support D σ τ,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p))
    (hError : ∀ p ∈ sigmaOneCarrier support D σ τ,
      E (N - 1) (D ⌈/⌉ p) (recursiveCoordinate D p) ≤
        E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p))
    (hIH : NaturalCeilPointwiseInductionContract support T V E β C K Δ N D σ τ) :
    PointwiseInductionContract support T V E β C K Δ N D σ τ := by
  intro p hp
  calc
    T (N - 1) (D ⌈/⌉ p) p ≤
        V p *
          (finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) +
            C * Real.exp (Real.sqrt K) *
              E (N - 1) (D ⌈/⌉ p) (recursiveCoordinate D p) *
                (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)) := hIH p hp
    _ ≤ V p *
          (finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) +
            C * Real.exp (Real.sqrt K) *
              E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) *
                (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)) := by
      apply mul_le_mul_of_nonneg_left _ (hV p hp)
      apply add_le_add (hSource p hp)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hlog p hp) _)
      exact mul_le_mul_of_nonneg_left (hError p hp)
        (mul_nonneg hC (Real.exp_nonneg _))

/-- Suzuki's `Σ₁`, restricted to the finite range in (14.10). -/
noncomputable def sigmaOne
    (support : Finset ℕ) (omega : ℕ → ℝ) (T : ℕ → ℕ → ℕ → ℝ)
    (N D : ℕ) (σ τ : ℝ) : ℝ :=
  ∑ p ∈ sigmaOneCarrier support D σ τ,
    omega p * T (N - 1) (D ⌈/⌉ p) p

/-- The main-term sum `Σ₁₁` in (14.10), with the normalization `V(p)/V(z)`
displayed rather than cancelled. -/
noncomputable def sigmaEleven
    (support : Finset ℕ) (omega V : ℕ → ℝ) (Vz β : ℝ)
    (N D : ℕ) (σ τ : ℝ) : ℝ :=
  Vz * ∑ p ∈ sigmaOneCarrier support D σ τ,
    omega p * V p / Vz *
      finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p)

/-- The inherited-error sum `Σ₁₂` in (14.10). -/
noncomputable def sigmaTwelve
    (support : Finset ℕ) (omega V : ℕ → ℝ)
    (E : ℕ → ℕ → ℝ → ℝ) (Vz C K Δ : ℝ)
    (N D : ℕ) (σ τ : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * Vz *
    ∑ p ∈ sigmaOneCarrier support D σ τ,
      omega p * V p / Vz *
        E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) *
          (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)

/-- Equation (14.10), as a pure finite assembly theorem.  It uses only the
pointwise induction contract, nonnegativity of the outer weights, and the
nonvanishing of the normalizing Euler product.  In particular it does not
assume or prove either endpoint bound for `Σ₁₁` or `Σ₁₂`. -/
theorem equation14_10_finset_assembly
    (support : Finset ℕ) (omega V : ℕ → ℝ)
    (T : ℕ → ℕ → ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (Vz β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hVz : Vz ≠ 0)
    (homega : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ omega p)
    (hIH : PointwiseInductionContract support T V E β C K Δ N D σ τ) :
    sigmaOne support omega T N D σ τ ≤
      sigmaEleven support omega V Vz β N D σ τ +
        sigmaTwelve support omega V E Vz C K Δ N D σ τ := by
  unfold sigmaOne sigmaEleven sigmaTwelve
  calc
    (∑ p ∈ sigmaOneCarrier support D σ τ,
        omega p * T (N - 1) (D ⌈/⌉ p) p) ≤
      ∑ p ∈ sigmaOneCarrier support D σ τ,
        omega p *
          (V p *
            (finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) +
              C * Real.exp (Real.sqrt K) *
                E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) *
                  (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ))) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hIH p hp) (homega p hp)
    _ = Vz *
          (∑ p ∈ sigmaOneCarrier support D σ τ,
            omega p * V p / Vz *
              finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p)) +
        C * Real.exp (Real.sqrt K) * Vz *
          ∑ p ∈ sigmaOneCarrier support D σ τ,
            omega p * V p / Vz *
              E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) *
                (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      field_simp

end SuzukiLemma144Equation1410
end MathlibNt.SieveTheory.SwitchingPrinciple
