import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseISourceRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorObjects
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Div

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

/-- The (nonnegative) coordinate displacement caused by natural ceiling
division. -/
noncomputable def coordinatePerturbation (D p : ℕ) : ℝ :=
  recursiveCoordinate D p - inheritedCoordinate D p

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
  have hqpos : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) := by
    have : 0 < D ⌈/⌉ p := by
      by_contra h
      have hz : D ⌈/⌉ p = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hlowerNat
      exact (Nat.ne_of_gt hD0) hlowerNat
    positivity
  have hDdivpos : (0 : ℝ) < (D : ℝ) / p := div_pos (by positivity) hpR
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

/-- Sharper, `D,p`-dependent version of the upper bound.  The coarse `3/2`
bound above follows from `(p-1)/D < 1/2`; this version retains the full natural
ceiling error. -/
theorem coordinate_bounds_sharp {D p : ℕ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) :
    inheritedCoordinate D p ≤ recursiveCoordinate D p ∧
      recursiveCoordinate D p ≤ inheritedCoordinate D p +
        Real.log (1 + ((p : ℝ) - 1) / D) / Real.log (p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hD0 : 0 < D := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < p by omega))
  have hupperNat := (ceilDiv_mul_bounds (D := D) (p := p) hp0).2
  have hupperR : ((D ⌈/⌉ p : ℕ) : ℝ) ≤ ((D + p - 1 : ℕ) : ℝ) / p := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast hupperNat
  have hqpos : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) := by
    have hlower := (ceilDiv_mul_bounds (D := D) (p := p) hp0).1
    have : 0 < D ⌈/⌉ p := by
      by_contra h
      have hz : D ⌈/⌉ p = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hlower
      exact (Nat.ne_of_gt hD0) hlower
    positivity
  have hfactor : (0 : ℝ) < 1 + ((p : ℝ) - 1) / D := by
    have hpminus : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ p by omega))
    have : 0 ≤ ((p : ℝ) - 1) / D := div_nonneg hpminus hDR.le
    linarith
  have hfactorization :
      ((D + p - 1 : ℕ) : ℝ) / p =
        ((D : ℝ) / p) * (1 + ((p : ℝ) - 1) / D) := by
    rw [Nat.cast_sub (by omega : 1 ≤ D + p)]
    push_cast
    field_simp [ne_of_gt hpR, ne_of_gt hDR]
    ring
  rw [hfactorization] at hupperR
  have hDdivpos : (0 : ℝ) < (D : ℝ) / p := div_pos hDR hpR
  have hlogupper : Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤
      Real.log (((D : ℝ) / p) * (1 + ((p : ℝ) - 1) / D)) :=
    Real.strictMonoOn_log.monotoneOn hqpos (mul_pos hDdivpos hfactor) hupperR
  rw [Real.log_mul (ne_of_gt hDdivpos) (ne_of_gt hfactor)] at hlogupper
  have hlowerCoord := (coordinate_bounds hp hDp).1
  rw [inheritedCoordinate_eq_log_div D p hD0 hp] at hlowerCoord
  rw [inheritedCoordinate_eq_log_div D p hD0 hp]
  constructor
  · exact hlowerCoord
  · calc
      Real.log ((D ⌈/⌉ p : ℕ) : ℝ) / Real.log (p : ℝ) ≤
          (Real.log ((D : ℝ) / p) + Real.log (1 + ((p : ℝ) - 1) / D)) /
            Real.log p := (div_le_div_iff_of_pos_right hlogp).2 hlogupper
      _ = Real.log ((D : ℝ) / p) / Real.log p +
          Real.log (1 + ((p : ℝ) - 1) / D) / Real.log p := by ring

theorem coordinatePerturbation_bounds {D p : ℕ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) :
    0 ≤ coordinatePerturbation D p ∧
      coordinatePerturbation D p ≤ Real.log (3 / 2 : ℝ) / Real.log (p : ℝ) := by
  rcases coordinate_bounds hp hDp with ⟨hlower, hupper⟩
  unfold coordinatePerturbation
  constructor <;> linarith

theorem coordinatePerturbation_bounds_sharp
    {D p : ℕ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) :
    0 ≤ coordinatePerturbation D p ∧
      coordinatePerturbation D p ≤
        Real.log (1 + ((p : ℝ) - 1) / D) / Real.log (p : ℝ) := by
  rcases coordinate_bounds_sharp hp hDp with ⟨hlower, hupper⟩
  unfold coordinatePerturbation
  constructor <;> linarith

theorem recursiveCoordinate_eq_inherited_add_perturbation (D p : ℕ) :
    recursiveCoordinate D p = inheritedCoordinate D p + coordinatePerturbation D p := by
  unfold coordinatePerturbation
  ring

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

/-- The error displacement is kept as an explicit additive term.  No
monotonicity of `E` is built into the induction contract. -/
noncomputable def inheritedErrorPerturbation
    (E : ℕ → ℕ → ℝ → ℝ) (n D p : ℕ) : ℝ :=
  E n (D ⌈/⌉ p) (recursiveCoordinate D p) -
    E n (D ⌈/⌉ p) (inheritedCoordinate D p)

theorem error_at_recursive_eq_inherited_add_perturbation
    (E : ℕ → ℕ → ℝ → ℝ) (n D p : ℕ) :
    E n (D ⌈/⌉ p) (recursiveCoordinate D p) =
      E n (D ⌈/⌉ p) (inheritedCoordinate D p) + inheritedErrorPerturbation E n D p := by
  unfold inheritedErrorPerturbation
  ring

/-- To discard the error perturbation one needs antitonicity, in the same
direction as for the finite source layer.  In particular this is the required
extra input when `E` is instantiated by `errorEnvelope`; its Section-13 layer
field is arbitrary, so the direction is not a consequence of that definition. -/
theorem error_recursive_le_inherited_of_antitoneOn
    (E : ℕ → ℕ → ℝ → ℝ) (n D p : ℕ)
    (hp : 2 ≤ p) (hDp : 2 * p ≤ D) (S : Set ℝ)
    (hx : inheritedCoordinate D p ∈ S) (hy : recursiveCoordinate D p ∈ S)
    (hanti : AntitoneOn (E n (D ⌈/⌉ p)) S) :
    E n (D ⌈/⌉ p) (recursiveCoordinate D p) ≤
      E n (D ⌈/⌉ p) (inheritedCoordinate D p) := by
  exact hanti hx hy (coordinate_bounds hp hDp).1

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

/-- Pointwise closure of the two ceiling discrepancies against source (14.13).

`hanti` removes the displacement from the literal recursive coordinate to the
source coordinate.  `hcutoff` is the separate monotonicity comparison in the
cutoff argument of `errorEnvelope`, from `⌈D/p⌉` down to the source cutoff
`D/p`.  The preceding lemma then enlarges only the logarithmic factor.  Thus
the final hypothesis is exactly the existing source-level
`Claim14_13PointwisePremise`, with every positivity/domain input visible. -/
theorem naturalCeil_error_le_claim14_13
    (H : Section13HatLayers) {N D p : ℕ} {d Δ : ℝ}
    (hp : 2 ≤ p) (hDp : 2 * p ≤ D) (hΔ : 0 ≤ Δ)
    (S : Set ℝ)
    (hinherited : inheritedCoordinate D p ∈ S)
    (hrecursive : recursiveCoordinate D p ∈ S)
    (hanti : AntitoneOn
      (errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d) S)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : Claim14_13PointwisePremise H N (D : ℝ) d Δ
      (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (recursiveCoordinate D p) *
        (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) ≤
      (Real.log (D : ℝ)) ^ (-Δ) *
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
  have hcoord := error_recursive_le_inherited_of_antitoneOn
    (E := fun n x s => errorEnvelope H n (x : ℝ) d s)
    (n := N - 1) (D := D) (p := p) hp hDp S hinherited hrecursive hanti
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hdiv2 : (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast hDp
  have hceil2 : (2 : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    calc
      (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := hdiv2
      _ ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
        rw [div_le_iff₀ hpR]
        exact_mod_cast (ceilDiv_mul_bounds (D := D) (p := p) (by omega : 0 < p)).1
  have hlogceil : 0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hceil2)).le
  have hlogdiv : 0 ≤ Real.log ((D : ℝ) / (p : ℝ)) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hdiv2)).le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < p by omega))
  have hinherited_nonneg : 0 ≤ inheritedCoordinate D p := by
    rw [inheritedCoordinate_eq_log_div D p (by omega) hp]
    exact div_nonneg hlogdiv hlogp.le
  have hceilLower : (D : ℝ) / (p : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast (ceilDiv_mul_bounds (D := D) (p := p) (by omega : 0 < p)).1
  have hcutoff := errorEnvelope_antitone_cutoff H (N - 1) (d := d)
    (lt_of_lt_of_le (by norm_num) hdiv2) hceilLower hinherited_nonneg hT
  have herror_nonneg := errorEnvelope_nonneg H (N - 1) (d := d)
    (lt_of_lt_of_le (by norm_num) hceil2) hinherited_nonneg hT
  have hceilFactor : 0 ≤ (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg hlogceil _
  have hdivFactor : 0 ≤ (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
    Real.rpow_nonneg hlogdiv _
  have hfactor := ceilDiv_log_rpow_neg_le_div_log_rpow_neg hp hDp hΔ
  have hsourceCoord :
      Real.log (D : ℝ) / Real.log (p : ℝ) - 1 = inheritedCoordinate D p := by
    rfl
  calc
    errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (recursiveCoordinate D p) *
        (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) ≤
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p) *
        (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) :=
      mul_le_mul_of_nonneg_right hcoord hceilFactor
    _ ≤ errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p) *
        (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
      mul_le_mul_of_nonneg_left hfactor herror_nonneg
    _ ≤ errorEnvelope H (N - 1) ((D : ℝ) / (p : ℝ)) d
          (inheritedCoordinate D p) *
        (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
      mul_le_mul_of_nonneg_right hcutoff hdivFactor
    _ ≤ (Real.log (D : ℝ)) ^ (-Δ) *
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
      rw [← hsourceCoord]
      exact h1413

/-- The normalized form of `naturalCeil_error_le_claim14_13`.  Its conclusion is
exactly a `R(log D / log p) ≤ qD(..., log D / log p)` premise of the shape
consumed by `sigma12_middle_le_qD_lemma8_7`: the global
`(log D)^{-Δ}` has been cancelled, but the literal induction factor at
`⌈D/p⌉` remains visible inside `R`. -/
theorem naturalCeil_error_normalized_le_qD
    (H : Section13HatLayers) {N D p : ℕ} {d Δ : ℝ}
    (hp : 2 ≤ p) (hDp : 2 * p ≤ D) (hΔ : 0 ≤ Δ)
    (S : Set ℝ)
    (hinherited : inheritedCoordinate D p ∈ S)
    (hrecursive : recursiveCoordinate D p ∈ S)
    (hanti : AntitoneOn
      (errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d) S)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : Claim14_13PointwisePremise H N (D : ℝ) d Δ
      (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    (Real.log (D : ℝ)) ^ Δ *
        (errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
            (recursiveCoordinate D p) *
          (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)) ≤
      qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
  have hmain := naturalCeil_error_le_claim14_13 H hp hDp hΔ S
    hinherited hrecursive hanti hT h1413
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < D by omega))
  have hscale : 0 ≤ (Real.log (D : ℝ)) ^ Δ := Real.rpow_nonneg hlogD.le _
  calc
    (Real.log (D : ℝ)) ^ Δ *
        (errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
            (recursiveCoordinate D p) *
          (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)) ≤
      (Real.log (D : ℝ)) ^ Δ *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
            (Real.log (D : ℝ) / Real.log (p : ℝ))) :=
      mul_le_mul_of_nonneg_left hmain hscale
    _ = qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
      rw [← mul_assoc, ← Real.rpow_add hlogD]
      simp

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

/-- Maximal unconditional bridge after using antitonicity only for the finite
source layer.  The error is evaluated at the inherited coordinate plus the
explicit displacement `inheritedErrorPerturbation`; it is not hidden in the
induction hypothesis. -/
def PerturbedPointwiseInductionContract
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier support D σ τ,
    T (N - 1) (D ⌈/⌉ p) p ≤
      V p *
        (finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) +
          C * Real.exp (Real.sqrt K) *
            (E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) +
              inheritedErrorPerturbation E (N - 1) D p) *
              (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ))

theorem naturalCeilContract_to_perturbed
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ)
    (V : ℕ → ℝ) (E : ℕ → ℕ → ℝ → ℝ)
    (β C K Δ : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hV : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ V p)
    (hSource : ∀ p ∈ sigmaOneCarrier support D σ τ,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p))
    (hIH : NaturalCeilPointwiseInductionContract support T V E β C K Δ N D σ τ) :
    PerturbedPointwiseInductionContract support T V E β C K Δ N D σ τ := by
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
              (E (N - 1) (D ⌈/⌉ p) (inheritedCoordinate D p) +
                inheritedErrorPerturbation E (N - 1) D p) *
                (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ)) := by
      apply mul_le_mul_of_nonneg_left _ (hV p hp)
      rw [← error_at_recursive_eq_inherited_add_perturbation E (N - 1) D p]
      exact add_le_add (hSource p hp) le_rfl

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
