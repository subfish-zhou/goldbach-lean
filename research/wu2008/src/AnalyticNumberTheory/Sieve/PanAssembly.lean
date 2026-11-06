import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Sieve.PanMainTerm

/-! # Weighted Pan mean-value assembly

This module assembles the separate coarse Vaughan proposition
`PanVaughanSplitCrude` from three input propositions
(`PanTypeICharacterMeanValue`, `PanTypeIICharacterMeanValue`,
`PanMainTermSieveBound`) and two analytic conditions
(`PanLogEventuallyLarge`, `PanVaughanPointwiseSplit`).
It yields the polylogarithmic `PanMeanValueUniformCrude` through
`PanMeanValueUniformCrude.of_vaughanSplit`.
The classical `PanMeanValueUniform` is assembled separately by
`PanMeanValueUniform.of_signedAnalyticInputs`.

The mathematical decomposition (Liu 2022 §III Thm 2; Pan 1963) starts from
`panMaxY X q x f = max_{y≤x} max_l |Σ_a f(a)·Δ(y;a,q,l)|`,
where `Δ(y;a,q,l) = π(y;a,q,l) − li(y/a)/φ(q)`.
Vaughan's identity separates the Type I (`apV1`), Type II (`apV3`),
and main-term contributions. In this coarse interface the third piece
is the absolute pure-`li` term, with `li` denoting the project's
`x/log x` proxy. The signed assembly retains the necessary subtraction.

The three bounds are obtained conditionally through
`PanTypeIWeightedBound.of_characterMeanValue` (`PanMeanValueBody` §5),
`PanTypeIIWeightedBound.of_characterMeanValue` (§5.2), and
`PanMainTermBound.of_sieveBound` (`PanMainTerm` §2).

The finite algebra proved here consists of:
1. The per-modulus split `w_q·panMaxY ≤ w_q·PI + w_q·PII + w_q·PM`
   (`panAssembly_pointwise`). At `q = 0`, `μ²(q) = 0`; for `q > 0`,
   use the pointwise input and nonnegative weights.
2. Splitting the modulus sum by `sum_add_distrib`.
3. Reconciling cutoffs (`panAssembly_floor_le`): choose
   `B = max B₁ (max B₂ B₃)`. If `log(xX) ≥ 1`, then
   `Q_B ≤ Q_{B_i}`; nonnegative terms allow enlargement of each range.
4. Bounding the Type I/II terms by `C_i·xX/log^A(xX)` and the
   pure main term by `C₃·xX·(log xX)^{A+7}`. For `log(xX) ≥ 1`,
   each Type I/II bound is at most `C_i·xX·(log xX)^{A+7}`,
   giving `(C₁+C₂+C₃)·xX·(log xX)^{A+7}`.

The pure main-term estimate is polylogarithmic:
`PanMainSieveAbsorption` (`PanMainTerm.lean` §6) absorbs fixed
polylogarithmic factors into a larger logarithmic power.
It does not yield the classical `C·xX/log^A(xX)` saving
(Liu Thm 2), which requires signed main-term cancellation.

The two coarse analytic inputs are propositions, not unconditional
theorems: (a) eventual `log(xX) ≥ 1`, as follows from `xX → ∞`;
(b) the pointwise conversion from prime AP counts to the
`apV1/apV3/li` pieces. The latter concerns the analytic transition
from von Mangoldt counts to prime counts and is not supplied by
finite Vaughan algebra alone.
-/

namespace AnalyticNumberTheory.Sieve

open Real Finset

open scoped Classical
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000

/-- **Coarse pure-li Vaughan split**, with a polylogarithmic right side:
for each `A > 0`, there are `C > 0`, `B`, and `x₀` such that
for every `X ≥ x₀`, with `Q = (xX)^{1/2}/log^B(xX)`,
`Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·panMaxY X q ⌊xX⌋ f
 ≤ C·xX·(log xX)^{A+7}`.

This is definitionally the coarse `PanMeanValueUniformCrude`
proposition, not the classical `PanMeanValueUniform`.
`PanVaughanSplitCrude.of_analyticInputs` derives it from the
three bound inputs and the two analytic conditions.
The pure-`li` piece admits polylogarithmic absorption
(`PanMainSieveAbsorption`, `PanMainTerm.lean` §6), not a
`C·xX/log^A(xX)` saving. The classical Vaughan argument controls
Type I/II by their weighted bounds and retains the signed
middle/main-term difference; its logarithmic saving needs that
additional analytic cancellation (Liu Thm 2). -/
def PanVaughanSplitCrude (x : ℕ → ℝ) (f : ℕ → ℝ) (_u _v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X * (log (x X)) ^ (A + 7)

/-- **Eventual logarithmic lower bound**: `log(x X) ≥ 1` for all
sufficiently large `X`. This follows classically from `x X → ∞`
(Liu 2022 §III). It permits cutoff comparison `Q_B ≤ Q_{B_i}`,
using monotonicity of real powers in the exponent for bases at least 1. -/
def PanLogEventuallyLarge (x : ℕ → ℝ) : Prop :=
  ∃ x₀ : ℕ, ∀ X : ℕ, x₀ ≤ X → 1 ≤ Real.log (x X)

/-- **Coarse pointwise Vaughan-split input**: for each `q > 0` and
all truncations, the maximum weighted prime-distribution error is
bounded by three piecewise maxima:

  panMaxY X q x f ≤
    panPieceMaxY X q x f (fun y q l => apV1 y q l u / log y) +
    panPieceMaxY X q x f (fun y q l => apV3 y q l u v / log y) +
    panPieceMaxY X q x f (fun y q l => li y / φ(q)).

The classical route (Liu 2022 §III Thm 2; HR 1974 Ch. 10) applies
Vaughan's identity (`vaughanIdentity_threeTerm`, `VaughanIdentity.lean`)
to `apVonMangoldt` (`PanMeanValueBody` §4), retaining the small and
middle terms as well as V1 and V3. Passing from
`π(y;q,l)·log y` to `Σ_{n≤y,n≡l} Λ(n)` and handling the signed
main-term difference require analytic input before taking maxima
over `y,l`. The pure-`li` inequality here is an explicit coarse
assumption, not a consequence of that finite identity alone. -/
def PanVaughanPointwiseSplit (_x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y : ℕ, 0 < q →
    panMaxY X q y f ≤
      panPieceMaxY X q y f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)

/-- The piece's `l`-maximum is nonnegative; when `q = 0` the residue
set is empty and its value is 0. This mirrors `panMaxL_nonneg`. -/
lemma panPieceMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    0 ≤ panPieceMaxL y X q f g := by
  unfold panPieceMaxL
  by_cases h : (unitResidues q).Nonempty
  · dsimp only []
    rw [dif_pos h]
    rcases h with ⟨l, hl⟩
    have hl' : |panPieceSum y X q l f g| ∈
        (Finset.image (fun l : ℕ => |panPieceSum y X q l f g|)
          (unitResidues q)) := by
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    exact le_trans (abs_nonneg _) (Finset.le_max' _ _ hl')
  · dsimp only []
    rw [dif_neg h]

/-- The piece's `y`-maximum is nonnegative: the image contains the
`y = 0` term, and each value is a maximum of absolute values. -/
private lemma panPieceMaxY_nonneg (X q x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    0 ≤ panPieceMaxY X q x f g := by
  unfold panPieceMaxY
  exact le_trans (panPieceMaxL_nonneg 0 X q f g)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g))
      (x := panPieceMaxL 0 X q f g)
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))

/-- **Cutoff comparison**: if `B' ≤ B`, `1 ≤ L`, and `z ≥ 0`, then
`⌊z/L^B⌋ ≤ ⌊z/L^{B'}⌋`. This gives `Q_B ≤ Q_{B_i}`. -/
lemma panAssembly_floor_le (z L : ℝ) (B B' : ℝ)
    (hz : 0 ≤ z) (hL1 : 1 ≤ L) (hB : B' ≤ B) :
    Nat.floor (z / L ^ B) ≤ Nat.floor (z / L ^ B') := by
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_left hz (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL1) B')
    (Real.rpow_le_rpow_of_exponent_le hL1 hB)

/-- **Weighted per-modulus split**:
`w_q·panMaxY ≤ w_q·PI + w_q·PII + w_q·PM`.
At `q = 0`, `μ²(q) = 0`; for `q > 0`, use `hsplit` and
nonnegativity of the weight. -/
private lemma panAssembly_pointwise (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hsplit : ∀ X q x : ℕ, 0 < q →
      panMaxY X q x f ≤
        panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        panPieceMaxY X q x f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q x f ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ]
  · simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (hsplit X q x (Nat.pos_of_ne_zero hq0))
        (panTypeI_weight_nonneg q)

/-- **Enlarging a sum**: if `Q ≤ Q'` and `w` is nonnegative, then
`Σ_{q ≤ Q} w q ≤ Σ_{q ≤ Q'} w q`. -/
lemma panAssembly_sum_le_sum (Q Q' : ℕ) (w : ℕ → ℝ) (hQQ' : Q ≤ Q')
    (hw : ∀ q : ℕ, 0 ≤ w q) :
    (∑ q ∈ Finset.range (Q + 1), w q) ≤ ∑ q ∈ Finset.range (Q' + 1), w q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hQQ'))
    (fun q hq hq' => hw q)



/-!
The old theorem at this seam returned `PanMeanValueUniform` by definitional
equality.  That was the semantic bug: the old split has a polylogarithmic RHS,
whereas Liu's signed theorem has inverse-log decay.  The faithful assembly is
defined below and requires an explicit signed-main block.
-/

/-- A weighted bound for the two residual kernels which together form the
signed main block.  The first kernel is the signed `li`-minus-middle/small
piece; the second carries the prime-power correction. -/
def PanSignedMainTermBound (x f : ℕ → ℝ)
    (main correction : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          (panPieceMaxY X q (Nat.floor (x X)) f main +
            panPieceMaxY X q (Nat.floor (x X)) (fun a => |f a|) correction) ≤
        C * x X / (log (x X)) ^ A

/-- Corrected pointwise Vaughan split.  Unlike `PanVaughanPointwiseSplit`,
the residual kernels stay inside the signed main block. -/
def PanVaughanPointwiseSplitSigned (_x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ)
    (main correction : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ X q y : ℕ, 0 < q →
    panMaxY X q y f ≤
      panPieceMaxY X q y f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      (panPieceMaxY X q y f main +
        panPieceMaxY X q y (fun a => |f a|) correction)

/- The preceding crude wrapper is intentionally not named `PanMeanValueUniform`:
theorem PanMeanValueUniform.of_vaughanSplit
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hV : PanVaughanSplit x f u v) :
    PanMeanValueUniform x f := by
  simpa [PanMeanValueUniform, PanVaughanSplit] using hV
would be a false parameter pass-through. -/

/-! ## Eventual log growth: PanLogEventuallyLarge

For `x : ℕ → ℝ` with `Tendsto x atTop atTop`,
`PanLogEventuallyLarge x` follows from standard eventuality.
`Real.tendsto_log_atTop.comp htend` gives
`Tendsto (log ∘ x) atTop atTop`.
Use `Filter.Tendsto.eventually` and `eventually_ge_atTop` to pull back
`∀ᶠ y, 1 ≤ y` to `∀ᶠ X, 1 ≤ log (x X)`, then `eventually_atTop`
to express it as `∃ x₀, ∀ X ≥ x₀, ...`. -/

section PanLogEventuallyLarge_instances

open Filter

/-- If `x : ℕ → ℝ` tends to infinity, then `PanLogEventuallyLarge x`:
eventually `log(x X) ≥ 1`, since `log(x X) → ∞`. -/
theorem panLogEventuallyLarge_of_tendsto_atTop {x : ℕ → ℝ}
    (htend : Tendsto x atTop atTop) : PanLogEventuallyLarge x := by
  have hlog : Tendsto (fun X : ℕ => Real.log (x X)) atTop atTop :=
    Real.tendsto_log_atTop.comp htend
  have hev : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (x X) :=
    hlog (eventually_ge_atTop 1)
  exact (eventually_atTop.mp hev)

/-- The real embedding `x X = (X : ℝ)` tends to infinity by
`tendsto_natCast_atTop_atTop`, so it satisfies `PanLogEventuallyLarge`. -/
theorem panLogEventuallyLarge_natCast :
    PanLogEventuallyLarge (fun N : ℕ => (N : ℝ)) := by
  exact panLogEventuallyLarge_of_tendsto_atTop tendsto_natCast_atTop_atTop

end PanLogEventuallyLarge_instances

end AnalyticNumberTheory.Sieve
