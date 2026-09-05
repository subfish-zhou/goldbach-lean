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
-- The li piece is independent of the residue parameter l'; suppress the corresponding warning, as in PanMainTerm.lean.
set_option linter.unusedVariables false

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
def PanVaughanSplitCrude (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
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
def PanVaughanPointwiseSplit (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y : ℕ, 0 < q →
    panMaxY X q y f ≤
      panPieceMaxY X q y f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)

/-- The piece's `l`-maximum is nonnegative; when `q = 0` the residue
set is empty and its value is 0. This mirrors `panMaxL_nonneg`. -/
private lemma panPieceMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
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
        panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q x f ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card :=
      panTypeI_weight_nonneg q
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q x f
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
                panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
                panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
            exact mul_le_mul_of_nonneg_left (hsplit X q x hq) hw
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
            ring

/-- **Enlarging a sum**: if `Q ≤ Q'` and `w` is nonnegative, then
`Σ_{q ≤ Q} w q ≤ Σ_{q ≤ Q'} w q`. -/
lemma panAssembly_sum_le_sum (Q Q' : ℕ) (w : ℕ → ℝ) (hQQ' : Q ≤ Q')
    (hw : ∀ q : ℕ, 0 ≤ w q) :
    (∑ q ∈ Finset.range (Q + 1), w q) ≤ ∑ q ∈ Finset.range (Q' + 1), w q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hQQ'))
    (fun q hq hq' => hw q)

/-- **Conditional coarse Vaughan assembly**: three character-mean/sieve
inputs and two analytic conditions (eventual log growth and the
pointwise split) imply `PanVaughanSplitCrude`.

1. Apply the reduction theorems, including
   `PanTypeIWeightedBound.of_characterMeanValue`, to obtain bounds
   with constants `Cᵢ`, exponents `Bᵢ`, and thresholds `x₀ᵢ`.
2. For each `A > 0`, choose `C = C₁+C₂+C₃`,
   `B = max B₁ (max B₂ B₃)`, and
   `x₀ = max (max x₀₁ (max x₀₂ x₀₃)) X₀`.
3. Use the weighted pointwise split, with zero weight at `q = 0`,
   and split the sum into three pieces.
4. From `hfin`, `log(xX) ≥ 1`; since `Bᵢ ≤ B`, enlarge each
   nonnegative sum from `Q_B` to `Q_{Bᵢ}`.
5. Convert the Type I/II logarithmic-saving bounds to the common
   polylogarithmic scale of the main-term bound and sum.

All cutoff, weight, and logarithmic-power algebra is proved here;
the input propositions remain hypotheses. -/
theorem PanVaughanSplitCrude.of_analyticInputs
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hI : PanTypeICharacterMeanValue x f u)
    (hII : PanTypeIICharacterMeanValue x f u v)
    (hM : PanMainTermSieveBound x f)
    (hfin : PanLogEventuallyLarge x)
    (hsplit : PanVaughanPointwiseSplit x f u v) :
    PanVaughanSplitCrude x f u v := by
  have hI' : PanTypeIWeightedBound x f u := PanTypeIWeightedBound.of_characterMeanValue hI
  have hII' : PanTypeIIWeightedBound x f u v := PanTypeIIWeightedBound.of_characterMeanValue hII
  have hM' : PanMainTermBound x f := PanMainTermBound.of_sieveBound hM
  rcases hfin with ⟨X₀, hX₀'⟩
  intro A hA
  rcases hI' A hA with ⟨C1, hC1, B1, x₀₁, hI1⟩
  rcases hII' A hA with ⟨C2, hC2, B2, x₀₂, hII1⟩
  rcases hM' A hA with ⟨C3, hC3, B3, x₀₃, hM1⟩
  refine ⟨C1 + C2 + C3, add_pos (add_pos hC1 hC2) hC3,
    max B1 (max B2 B3), max (max x₀₁ (max x₀₂ x₀₃)) X₀, ?_⟩
  intro X hX
  have hX₁ : x₀₁ ≤ X := by omega
  have hX₂ : x₀₂ ≤ X := by omega
  have hX₃ : x₀₃ ≤ X := by omega
  have hX₄ : X₀ ≤ X := by omega
  have hL : 1 ≤ Real.log (x X) := hX₀' X hX₄
  have hsqrt : 0 ≤ (x X) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  let B : ℝ := max B1 (max B2 B3)
  let Q : ℕ := Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B)
  have hB₁ : B1 ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have hB₂ : B2 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hB₃ : B3 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hQ1 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B1 hsqrt hL hB₁
  have hQ2 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B2 hsqrt hL hB₂
  have hQ3 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B3 hsqrt hL hB₃
  have hI2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
        ≤ C1 * x X / (Real.log (x X)) ^ A := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
              hQ1 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => apV1 y q l u / Real.log (y : ℝ))))
      _ ≤ C1 * x X / (Real.log (x X)) ^ A := hI1 X hX₁
  have hII2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
        ≤ C2 * x X / (Real.log (x X)) ^ A := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
              hQ2 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => apV3 y q l u v / Real.log (y : ℝ))))
      _ ≤ C2 * x X / (Real.log (x X)) ^ A := hII1 X hX₂
  have hM2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f
              (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
        ≤ C3 * x X * (Real.log (x X)) ^ (A + 7) := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f
              (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
              hQ3 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)))
      _ ≤ C3 * x X * (Real.log (x X)) ^ (A + 7) := hM1 X hX₃
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q (Nat.floor (x X)) f)
        ≤ ∑ q ∈ Finset.range (Q + 1),
            (((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact panAssembly_pointwise X q (Nat.floor (x X)) f u v hsplit
    _ = (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ))) +
        (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))) +
        (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f
                (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ C1 * x X / (Real.log (x X)) ^ A + C2 * x X / (Real.log (x X)) ^ A +
          C3 * x X * (Real.log (x X)) ^ (A + 7) := by
        apply add_le_add
        · apply add_le_add
          · exact hI2
          · exact hII2
        · exact hM2
    _ ≤ (C1 + C2 + C3) * x X * (Real.log (x X)) ^ (A + 7) := by
        -- Termwise, Cᵢx/log^A ≤ Cᵢx·log^{A+7}, since log(xX) ≥ 1 and xX ≥ 0, and
        -- C₃x·log^{A+7} ≤ (C1+C2+C3)x·log^{A+7}, since the coefficients are nonnegative.
        have hxXnn : 0 ≤ x X := by
          -- The right side of hI1 is nonnegative because Σ₁ ≥ 0, hence xX ≥ 0.
          have hsum1nn : (0 : ℝ) ≤
              (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) + 1),
                ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                  panPieceMaxY X q (Nat.floor (x X)) f
                    (fun y q l => apV1 y q l u / Real.log (y : ℝ))) := by
            exact Finset.sum_nonneg (fun q hq => mul_nonneg (panTypeI_weight_nonneg q)
              (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                (fun y q l => apV1 y q l u / Real.log (y : ℝ))))
          have hle0 : (0 : ℝ) ≤ C1 * x X / (Real.log (x X)) ^ A := le_trans hsum1nn (hI1 X hX₁)
          have hLpos : 0 < (Real.log (x X)) ^ A :=
            lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (Real.one_le_rpow hL (le_of_lt hA))
          have hC1x : 0 ≤ C1 * x X := nonneg_of_mul_nonneg_left hle0 (inv_pos.mpr hLpos)
          have hxC1 : 0 ≤ x X * C1 := by simpa [mul_comm] using hC1x
          exact nonneg_of_mul_nonneg_left hxC1 hC1
        have hlogAge1 : 1 ≤ (Real.log (x X)) ^ A := Real.one_le_rpow hL (le_of_lt hA)
        have hlogA7ge1 : 1 ≤ (Real.log (x X)) ^ (A + 7) :=
          Real.one_le_rpow hL (by positivity : 0 ≤ A + 7)
        have hcoef1 : ((Real.log (x X)) ^ A)⁻¹ ≤ (Real.log (x X)) ^ (A + 7) := by
          calc
            ((Real.log (x X)) ^ A)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogAge1
            _ ≤ (Real.log (x X)) ^ (A + 7) := hlogA7ge1
        have hc1 : C1 * x X / (Real.log (x X)) ^ A ≤ C1 * x X * (Real.log (x X)) ^ (A + 7) := by
          calc
            C1 * x X / (Real.log (x X)) ^ A = C1 * x X * ((Real.log (x X)) ^ A)⁻¹ := by ring
            _ ≤ C1 * x X * (Real.log (x X)) ^ (A + 7) := by
              exact mul_le_mul_of_nonneg_left hcoef1 (mul_nonneg (le_of_lt hC1) hxXnn)
        have hc2 : C2 * x X / (Real.log (x X)) ^ A ≤ C2 * x X * (Real.log (x X)) ^ (A + 7) := by
          calc
            C2 * x X / (Real.log (x X)) ^ A = C2 * x X * ((Real.log (x X)) ^ A)⁻¹ := by ring
            _ ≤ C2 * x X * (Real.log (x X)) ^ (A + 7) := by
              exact mul_le_mul_of_nonneg_left hcoef1 (mul_nonneg (le_of_lt hC2) hxXnn)
        have hc3 : C3 * x X * (Real.log (x X)) ^ (A + 7) ≤
            (C1 + C2 + C3) * x X * (Real.log (x X)) ^ (A + 7) := by
          have hsum12 : 0 ≤ C1 + C2 := by linarith
          have hLnn : 0 ≤ Real.log (x X) := by linarith
          have hnonneg : 0 ≤ (C1 + C2) * x X * (Real.log (x X)) ^ (A + 7) := by
            exact mul_nonneg (mul_nonneg hsum12 hxXnn) (Real.rpow_nonneg hLnn (A + 7))
          calc
            C3 * x X * (Real.log (x X)) ^ (A + 7)
                ≤ C3 * x X * (Real.log (x X)) ^ (A + 7) +
                    (C1 + C2) * x X * (Real.log (x X)) ^ (A + 7) := by linarith
            _ = (C1 + C2 + C3) * x X * (Real.log (x X)) ^ (A + 7) := by ring
        calc
          C1 * x X / (Real.log (x X)) ^ A + C2 * x X / (Real.log (x X)) ^ A +
              C3 * x X * (Real.log (x X)) ^ (A + 7)
              ≤ C1 * x X * (Real.log (x X)) ^ (A + 7) + C2 * x X * (Real.log (x X)) ^ (A + 7) +
                  C3 * x X * (Real.log (x X)) ^ (A + 7) := by
                exact add_le_add (add_le_add hc1 hc2) (le_rfl)
            _ = (C1 + C2 + C3) * x X * (Real.log (x X)) ^ (A + 7) := by ring

/-- The coarse pure-`li` split yields only the polylogarithmic
`PanMeanValueUniformCrude`, not the classical Pan theorem. -/
theorem PanMeanValueUniformCrude.of_vaughanSplit
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hV : PanVaughanSplitCrude x f u v) :
    PanMeanValueUniformCrude x f := by
  simpa [PanMeanValueUniformCrude, PanVaughanSplitCrude] using hV

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
def PanVaughanPointwiseSplitSigned (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ)
    (main correction : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ X q y : ℕ, 0 < q →
    panMaxY X q y f ≤
      panPieceMaxY X q y f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      (panPieceMaxY X q y f main +
        panPieceMaxY X q y (fun a => |f a|) correction)

/-- Weighted finite assembly for the honest signed split.  All three analytic
bounds retain inverse-log decay; this theorem only aligns their cutoffs and
sums the pointwise inequality. -/
theorem PanMeanValueUniform.of_signedAnalyticInputs
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    {main correction : ℕ → ℕ → ℕ → ℝ}
    (hI : PanTypeICharacterMeanValue x f u)
    (hII : PanTypeIICharacterMeanValue x f u v)
    (hM : PanSignedMainTermBound x f main correction)
    (hfin : PanLogEventuallyLarge x)
    (hsplit : PanVaughanPointwiseSplitSigned x f u v main correction) :
    PanMeanValueUniform x f := by
  have hI' : PanTypeIWeightedBound x f u :=
    PanTypeIWeightedBound.of_characterMeanValue hI
  have hII' : PanTypeIIWeightedBound x f u v :=
    PanTypeIIWeightedBound.of_characterMeanValue hII
  rcases hfin with ⟨X₀, hX₀'⟩
  intro A hA
  rcases hI' A hA with ⟨C1, hC1, B1, x₀₁, hI1⟩
  rcases hII' A hA with ⟨C2, hC2, B2, x₀₂, hII1⟩
  rcases hM A hA with ⟨C3, hC3, B3, x₀₃, hM1⟩
  refine ⟨C1 + C2 + C3, add_pos (add_pos hC1 hC2) hC3,
    max B1 (max B2 B3), max (max x₀₁ (max x₀₂ x₀₃)) X₀, ?_⟩
  intro X hX
  have hX₁ : x₀₁ ≤ X := by omega
  have hX₂ : x₀₂ ≤ X := by omega
  have hX₃ : x₀₃ ≤ X := by omega
  have hX₄ : X₀ ≤ X := by omega
  have hL : 1 ≤ Real.log (x X) := hX₀' X hX₄
  have hsqrt : 0 ≤ (x X) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  let B : ℝ := max B1 (max B2 B3)
  let Q : ℕ := Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B)
  have hQ1 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) := by
    exact panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_max_left _ _)
  have hQ2 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) := by
    exact panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_trans (le_max_left _ _) (le_max_right _ _))
  have hQ3 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) := by
    exact panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_trans (le_max_right _ _) (le_max_right _ _))
  let w : ℕ → ℝ := fun q =>
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card
  let pI : ℕ → ℝ := fun q =>
    panPieceMaxY X q (Nat.floor (x X)) f
      (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let pII : ℕ → ℝ := fun q =>
    panPieceMaxY X q (Nat.floor (x X)) f
      (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let pM : ℕ → ℝ := fun q =>
    panPieceMaxY X q (Nat.floor (x X)) f main +
      panPieceMaxY X q (Nat.floor (x X)) (fun a => |f a|) correction
  have hw : ∀ q, 0 ≤ w q := fun q => panTypeI_weight_nonneg q
  have hInn : ∀ q, 0 ≤ pI q := fun q =>
    panPieceMaxY_nonneg _ _ _ _ _
  have hIInn : ∀ q, 0 ≤ pII q := fun q =>
    panPieceMaxY_nonneg _ _ _ _ _
  have hMnn : ∀ q, 0 ≤ pM q := fun q => add_nonneg
    (panPieceMaxY_nonneg _ _ _ _ _) (panPieceMaxY_nonneg _ _ _ _ _)
  have hI2 : (∑ q ∈ Finset.range (Q + 1), w q * pI q) ≤
      C1 * x X / (Real.log (x X)) ^ A := by
    exact le_trans
      (panAssembly_sum_le_sum Q _ (fun q => w q * pI q) hQ1
        (fun q => mul_nonneg (hw q) (hInn q)))
      (by simpa [w, pI] using hI1 X hX₁)
  have hII2 : (∑ q ∈ Finset.range (Q + 1), w q * pII q) ≤
      C2 * x X / (Real.log (x X)) ^ A := by
    exact le_trans
      (panAssembly_sum_le_sum Q _ (fun q => w q * pII q) hQ2
        (fun q => mul_nonneg (hw q) (hIInn q)))
      (by simpa [w, pII] using hII1 X hX₂)
  have hM2 : (∑ q ∈ Finset.range (Q + 1), w q * pM q) ≤
      C3 * x X / (Real.log (x X)) ^ A := by
    exact le_trans
      (panAssembly_sum_le_sum Q _ (fun q => w q * pM q) hQ3
        (fun q => mul_nonneg (hw q) (hMnn q)))
      (by simpa [w, pM] using hM1 X hX₃)
  calc
    (∑ q ∈ Finset.range (Q + 1), w q * panMaxY X q (Nat.floor (x X)) f)
        ≤ ∑ q ∈ Finset.range (Q + 1), w q * (pI q + pII q + pM q) := by
          apply Finset.sum_le_sum
          intro q hq
          by_cases hq0 : q = 0
          · subst q
            have hμ : (μ 0 : ℤ) = 0 :=
              ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
            simp [w, hμ]
          · exact mul_le_mul_of_nonneg_left
              (by simpa [pI, pII, pM] using
                hsplit X q (Nat.floor (x X)) (Nat.pos_of_ne_zero hq0))
              (hw q)
    _ = (∑ q ∈ Finset.range (Q + 1), w q * pI q) +
          (∑ q ∈ Finset.range (Q + 1), w q * pII q) +
          (∑ q ∈ Finset.range (Q + 1), w q * pM q) := by
            simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C1 * x X / (Real.log (x X)) ^ A +
          C2 * x X / (Real.log (x X)) ^ A +
          C3 * x X / (Real.log (x X)) ^ A :=
      add_le_add (add_le_add hI2 hII2) hM2
    _ = (C1 + C2 + C3) * x X / (Real.log (x X)) ^ A := by ring
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
