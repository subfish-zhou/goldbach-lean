import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Mertens.PartialSummation
import AnalyticNumberTheory.Sieve.GoldbachDensity
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # AnalyticNumberTheory.Sieve.PanMainTerm

## Polylogarithmic bounds for the pure main-term contribution

The coarse weighted Pan decomposition separates Type I (`apV1`),
Type II (`apV3`), and a pure main-term piece after absorbing `a`
into the residue class (Liu 2022 §III; Halberstam--Richert 1974 Ch. 10).
This module supplies the reduction chain for the third piece,
`PanMainTermBound` from `PanMeanValueBody.lean` §4.

Here `li` abbreviates the project's proxy
`logarithmicIntegral x = x/log x` (`BombieriVinogradov.lean`),
not the genuine logarithmic integral.
For `|f| ≤ 1`, the unmaximized main term satisfies

```text
|Σ_{(a,q)=1, a≤X} f(a)·li(⌊y/a⌋)/φ(q)|
  ≤ Σ_{1≤a≤X} |li(⌊y/a⌋)|/φ(q)
  ≤ (max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)|)/φ(q).
```

Thus its weighted modulus sum is at most
`max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)| · Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q)`.
`PanMainTermBound.of_sieveBound` reduces the bound to this product
(`PanMainTermSieveBound`). The triangle inequality, `|f| ≤ 1`,
both maxima, nonnegative weights, and the zero weight at `q = 0`
are all handled by finite algebra, parallel to the Type I reduction
`PanTypeICharacterMeanValue.of_sieveBound`.

## Elementary estimates for the two factors

- **The `(y,a)` factor (§3)**: `|li(m)| ≤ m/log 2` for every natural `m`,
  hence `Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1 + log X)`.
  The maximum over `y ≤ x` is at most `(x/log 2)·(1 + log X)`,
  by the harmonic-sum bound and `⌊y/a⌋ ≤ y/a`.
- **The `q` factor (§4)**: for squarefree `q`,
  `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`
  (using `goldbachNu_squarefree_eq_inv_totient`).
  Subset expansion gives
  `Σ_{q≤Q, squarefree} ∏_{p|q} c_p ≤ ∏_{p≤Q} (1+c_p)`.
  Combine `1+u ≤ exp u` with Mertens' second theorem
  (`mertensSecond_nat`) to get
  `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

## Limitation: an absolute main term does not give a logarithmic saving

These estimates have product `xX·polylog(xX)`. They cannot yield
`C·xX/log^A(xX)`: the term `a = 1`, `q = 2`, `y = xX` alone
has size `li(xX)/φ(2) ≈ xX/log(xX)`. The saving claim is already
false for `x X = X` and `A = 2`; §6 also proves a counterexample
to the corresponding absorption inequality.

The classical argument instead subtracts the sieve main term
`x/log x·∏(1-ν(p))` from the `li` contribution, leaving a signed
error `O(x/log^A x)` (Liu §III; HR 1974 Ch. 10).
That cancellation requires sieve-product and prime-distribution input,
not an upper bound on the absolute main term. The signed-main-term
requirements are discussed in `PAN_PROOF_ATLAS.md` and the main-term
bridge in `ROADMAP`.

The results here have the provable polylogarithmic right side
`C·xX·(log xX)^{A+7}`:
`panMainTotientWeightedSum_le_polylog` bounds the `q` factor,
`panMainWeightedSum_polylog` combines the elementary factors, and
`panMainSieveAbsorption_of_dom` proves absorption into a larger log power
under `X ≤ x X`. Finally,
`PanMainTermSieveBound.of_innerSumBound` assembles the bound.
These results belong to the coarse pure-main-term chain and do not
establish the classical signed logarithmic-saving estimate.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open AnalyticNumberTheory.Mertens

open scoped Classical
open scoped ArithmeticFunction.Moebius


/-! ## 1. Main-term inner sums and maximum reductions -/

/-- The pure main-term inner sum `Σ_{1≤a≤X} |li(⌊y/a⌋)|`.
Its argument uses natural-number division, matching the truncation
`g (y / a) q ...` in `panPieceSum`. -/
noncomputable def mainTermInnerSum (y X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|

/-- Maximum of the inner sum over `y ≤ x`, mirroring `panPieceMaxY`. -/
noncomputable def mainTermInnerSumMax (X x : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => mainTermInnerSum y X)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Weighted reciprocal-totient sum `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q)`;
the `q = 0` term has zero weight. -/
noncomputable def panMainTotientWeightedSum (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)

/-- The inner sum is nonnegative. -/
theorem mainTermInnerSum_nonneg (y X : ℕ) : 0 ≤ mainTermInnerSum y X := by
  unfold mainTermInnerSum
  exact Finset.sum_nonneg (fun a ha => abs_nonneg _)

/-- The maximum inner sum is nonnegative. -/
theorem mainTermInnerSumMax_nonneg (X x : ℕ) : 0 ≤ mainTermInnerSumMax X x := by
  unfold mainTermInnerSumMax
  exact le_trans (mainTermInnerSum_nonneg 0 X)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => mainTermInnerSum y X))
      (x := mainTermInnerSum 0 X)
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))

/-- Nonnegative weight: `μ²(q)·3^{ω(q)} ≥ 0`. -/
theorem panMain_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact AnalyticNumberTheory.Sieve.panTypeI_weight_nonneg q

/-- **Termwise triangle reduction**: remove the coprimality indicator
and use `|f| ≤ 1`, starting from
`|f(a)·li(⌊y/a⌋)/φ(q)| ≤ |f(a)|·|li(⌊y/a⌋)|/φ(q)`.
Only `φ(q) ≥ 0` is needed, so the bound holds for every `q`;
both sides vanish at `q = 0`. -/
private lemma panMain_summand_abs_le (y _X q : ℕ) (f : ℕ → ℝ) (a : ℕ)
    (_hfb : ∀ a : ℕ, |f a| ≤ 1) :
    |if a.Coprime q then
      f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
    else 0|
      ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop]
    have hφ : (0 : ℝ) ≤ (Nat.totient q : ℝ) := by positivity
    calc
      |f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))|
          = |f a| * |logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ)| := by
            rw [abs_mul]
      _ = |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
            rw [abs_div, abs_of_nonneg hφ]
      _ ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := le_rfl
  · have hnn : 0 ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| /
        (Nat.totient q : ℝ)) := by
      exact mul_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) (by positivity))
    simp [hcop, hnn]

/-- **Pointwise main-term reduction**:
`|panPieceSum| ≤ innerSum/φ(q)` before taking maxima.
The bound is uniform under `|f| ≤ 1` and independent of `l`. -/
theorem panMainPieceSum_abs_le (y X q : ℕ) (f : ℕ → ℝ) (l : ℕ)
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    |panPieceSum y X q l f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q')|
      ≤ mainTermInnerSum y X / (Nat.totient q : ℝ) := by
  unfold panPieceSum mainTermInnerSum
  calc
    |∑ a ∈ Finset.Icc 1 X,
        if a.Coprime q then
          f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
        else 0|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
            else 0| := by
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact panMain_summand_abs_le y X q f a hfb
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have hφ : (0 : ℝ) ≤ (Nat.totient q : ℝ) := by positivity
          have hnn : 0 ≤ |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) :=
            div_nonneg (abs_nonneg _) hφ
          calc
            |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ))
                ≤ 1 * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) :=
                  mul_le_mul_of_nonneg_right (hfb a) hnn
            _ = |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) := by simp
    _ = (∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|) /
          (Nat.totient q : ℝ) := by
          rw [← Finset.sum_div]

/-- **Residue-maximum reduction**:
`panPieceMaxL ≤ innerSum/φ(q)`, since the bound is independent of `l`.
For `q = 0`, the residue set is empty and nonnegativity gives the result. -/
theorem panMainPieceMaxL_le (y X q : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panPieceMaxL y X q f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q') ≤
      mainTermInnerSum y X / (Nat.totient q : ℝ) := by
  unfold panPieceMaxL
  by_cases hS : (unitResidues q).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    exact panMainPieceSum_abs_le y X q f l hfb
  · dsimp only []
    rw [dif_neg hS]
    exact div_nonneg (mainTermInnerSum_nonneg y X)
      (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **Truncation-maximum reduction**:
`panPieceMaxY ≤ innerSumMax/φ(q)`, by taking the maximum of the
pointwise bounds `panPieceMaxL ≤ innerSum/φ(q)`. -/
theorem panMainPieceMaxY_le (X q x : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panPieceMaxY X q x f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q') ≤
      mainTermInnerSumMax X x / (Nat.totient q : ℝ) := by
  unfold panPieceMaxY mainTermInnerSumMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panPieceMaxL y X q f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q')
        ≤ mainTermInnerSum y X / (Nat.totient q : ℝ) := panMainPieceMaxL_le y X q f hfb
    _ ≤ mainTermInnerSumMax X x / (Nat.totient q : ℝ) := by
          exact div_le_div_of_nonneg_right
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => mainTermInnerSum y X))
              (x := mainTermInnerSum y X)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **Weighted modulus-sum reduction**: the main-term expression is at most
`innerSumMax · Σ_{q≤Q} μ²3^ω/φ(q)`. The `q = 0` weight vanishes;
for the other moduli use the pointwise bound and nonnegative weights. -/
theorem panMainWeightedSum_le (X Q x : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q')) ≤
      mainTermInnerSumMax X x *
        (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) := by
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q x f (fun y' q' _ => logarithmicIntegral (y' : ℝ) / Nat.totient q'))
        ≤ ∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (mainTermInnerSumMax X x / (Nat.totient q : ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (panMainPieceMaxY_le X q x f hfb)
            (panMain_weight_nonneg q)
    _ = mainTermInnerSumMax X x *
          (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring

/-! ## 1.1 Liu Section III: the non-decaying Selberg main term

The following finite identity models Liu's equation `M₁`: the `li` sum is
multiplied by the Selberg quadratic factor.  It is deliberately separate from
the signed Pan remainder, whose inverse-log decay concerns `π - li`.
-/

/-- The Selberg quadratic factor `Σ λ(d₁)λ(d₂)/φ([d₁,d₂])`. -/
noncomputable def panSelbergQuadraticFactor (D : Finset ℕ) (coeff : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ D, ∑ d₂ ∈ D,
    coeff d₁ * coeff d₂ / (Nat.totient (Nat.lcm d₁ d₂) : ℝ)

/-- Liu's weighted logarithmic-integral sum `Σ f(a) li(N/a)`. -/
noncomputable def panLiWeightSum (A : Finset ℕ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ A, f a * logarithmicIntegral ((N : ℝ) / a)

/-- The unfactored finite Selberg–`li` main term. -/
noncomputable def panSelbergLiMainTerm
    (D A : Finset ℕ) (coeff f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d₁ ∈ D, ∑ d₂ ∈ D, coeff d₁ * coeff d₂ *
    ∑ a ∈ A, f a *
      (logarithmicIntegral ((N : ℝ) / a) /
        (Nat.totient (Nat.lcm d₁ d₂) : ℝ))

/-- **Finite main-term factorization** (Liu §III, equation `eqn-m1`):
the Selberg quadratic factor and the weighted `li` sum separate exactly. -/
theorem panSelbergLiMainTerm_eq_factor_mul
    (D A : Finset ℕ) (coeff f : ℕ → ℝ) (N : ℕ) :
    panSelbergLiMainTerm D A coeff f N =
      panSelbergQuadraticFactor D coeff * panLiWeightSum A f N := by
  unfold panSelbergLiMainTerm panSelbergQuadraticFactor panLiWeightSum
  calc
    (∑ d₁ ∈ D, ∑ d₂ ∈ D, coeff d₁ * coeff d₂ *
        ∑ a ∈ A, f a *
          (logarithmicIntegral ((N : ℝ) / a) /
            (Nat.totient (Nat.lcm d₁ d₂) : ℝ))) =
      ∑ d₁ ∈ D, ∑ d₂ ∈ D,
        (coeff d₁ * coeff d₂ / (Nat.totient (Nat.lcm d₁ d₂) : ℝ)) *
          ∑ a ∈ A, f a * logarithmicIntegral ((N : ℝ) / a) := by
            apply Finset.sum_congr rfl
            intro d₁ hd₁
            apply Finset.sum_congr rfl
            intro d₂ hd₂
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring
    _ = (∑ d₁ ∈ D, ∑ d₂ ∈ D,
          coeff d₁ * coeff d₂ / (Nat.totient (Nat.lcm d₁ d₂) : ℝ)) *
        ∑ a ∈ A, f a * logarithmicIntegral ((N : ℝ) / a) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d₁ hd₁
          rw [Finset.sum_mul]

/-! ## 2. Analytic input and reduction theorem -/

/-- **Pure main-term bound, polylogarithmic form**: for each `A > 0`,
there exist `C > 0`, `B`, and `x₀` such that for all `X ≥ x₀`,
with `Q = (xX)^{1/2}/log^B(xX)`,
`innerSumMax(X, ⌊xX⌋) · Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q)
 ≤ C·xX·(log xX)^{A+7}`.
Here `innerSumMax(X,x) = max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)|`.

A right side `C·xX/log^A(xX)` would be false for the pure main-term
piece: for `x X = X` and `A = 2`, its left side is at least
`li(X)·1 ~ X/log X`, exceeding `C·X/log²X` eventually.
The classical saving comes from subtracting the sieve main term
`x/log x·∏(1-ν(p))` (Liu 2022 §III; HR 1974 Ch. 10),
requiring a sieve-product object and signed main-term analysis
(see `PAN_PROOF_ATLAS.md` and the main-term bridge in `ROADMAP`).

The elementary factors in §§3--4 instead give
`xX·(1+log X)·log⁶(xX+2)`, of total logarithmic degree 7.
`PanMainSieveAbsorption` in §6 bounds this by the larger power
`C·xX·(log xX)^{A+7}` under domination of `X` by `x X`. -/
def PanMainTermSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        mainTermInnerSumMax X (Nat.floor (x X)) *
          (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
          C * x X * (log (x X)) ^ (A + 7)

/-- **Main-term reduction theorem**:
`PanMainTermSieveBound` implies `PanMainTermBound`.
The triangle inequality, `|f| ≤ 1`, both maximum reductions,
nonnegative weights, and zero weight at `q = 0` are finite algebra;
the only analytic hypothesis is the supplied sieve bound. -/
theorem PanMainTermBound.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ}
    (hS : PanMainTermSieveBound x f) : PanMainTermBound x f := by
  rcases hS with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q))
        ≤ mainTermInnerSumMax X (Nat.floor (x X)) *
            (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) :=
          panMainWeightedSum_le X (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B))
            (Nat.floor (x X)) f hfb
    _ ≤ C * x X * (log (x X)) ^ (A + 7) := hMain X hX

/-! ## 3. Elementary li-proxy bounds and the (y,a) factor

For every natural `m`, `|li(m)| ≤ m/log 2`: if `m ≥ 2`,
`li(m) = m/log m ≤ m/log 2`, while `li(0) = li(1) = 0`.
The harmonic bound `Σ_{1≤a≤X} 1/a ≤ 1+log X` and
`⌊y/a⌋ ≤ y/a` then give
`Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1+log X)`.
Taking the maximum over `y ≤ x` yields
`mainTermInnerSumMax ≤ (x/log 2)·(1+log X)`.

This bounds the `(y,a)` factor in `PanMainTermSieveBound`.
More refined classical estimates use sums such as
`Σ 1/(a·log(y/a)) ≪ log log X` in the appropriate ranges
(see Mertens partial summation); the coarse `log X` bound is
sufficient here, where the exact polylogarithmic exponent is inessential.
-/

/-- Uniform elementary proxy bound: `|li(m)| ≤ m/log 2` for natural `m`.
`li(0) = li(1) = 0`; for `m ≥ 2`, `li(m) = m/log m ≤ m/log 2`. -/
theorem logIntegral_nat_abs_le (m : ℕ) :
    |logarithmicIntegral (m : ℝ)| ≤ (m : ℝ) / Real.log 2 := by
  unfold logarithmicIntegral
  by_cases hm : m ≤ 1
  · have hzero : (m : ℝ) / Real.log (m : ℝ) = 0 := by
      interval_cases m <;> simp [Real.log_zero, Real.log_one]
    rw [hzero]
    simp only [abs_zero]
    exact div_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))
      (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · have hm2 : 2 ≤ m := by omega
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hle_log : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hm2)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    calc
      |(m : ℝ) / Real.log (m : ℝ)| = (m : ℝ) / Real.log (m : ℝ) := by
        rw [abs_of_pos (div_pos hm_pos hlog)]
      _ ≤ (m : ℝ) / Real.log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hm_pos) hlog2 hle_log

/-- **Main-term inner-sum bound**:
`Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1+log X)`.
This controls the `(y,a)` factor under `|f| ≤ 1`, by the harmonic sum,
the floor bound, and `|li(m)| ≤ m/log 2`. -/
theorem mainTermInnerSum_le (X y : ℕ) :
    mainTermInnerSum y X ≤ (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
  unfold mainTermInnerSum
  calc
    (∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|)
        ≤ ∑ a ∈ Finset.Icc 1 X, ((y / a : ℕ) : ℝ) / Real.log 2 := by
          apply Finset.sum_le_sum
          intro a ha
          exact logIntegral_nat_abs_le (y / a)
    _ = (∑ a ∈ Finset.Icc 1 X, ((y / a : ℕ) : ℝ)) / Real.log 2 := by
          rw [← Finset.sum_div]
    _ ≤ (∑ a ∈ Finset.Icc 1 X, (y : ℝ) / (a : ℝ)) / Real.log 2 := by
          exact div_le_div_of_nonneg_right
            (Finset.sum_le_sum (fun a ha => Nat.cast_div_le)) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    _ = ((y : ℝ) * (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ))) / Real.log 2 := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ ≤ (y : ℝ) * (1 + Real.log (X : ℝ)) / Real.log 2 := by
          have hle : (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ)) ≤ 1 + Real.log (X : ℝ) := by
            simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
              Rat.cast_natCast, one_div] using harmonic_le_one_add_log X
          have hy : (0 : ℝ) ≤ (y : ℝ) := by positivity
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hy)
            (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    _ = (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by ring

/-- **Maximum inner-sum bound**:
`max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (x/log 2)·(1+log X)`. -/
theorem mainTermInnerSumMax_le (X x : ℕ) :
    mainTermInnerSumMax X x ≤ (x : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
  unfold mainTermInnerSumMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyx : y ≤ x := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    by_cases hX : X = 0
    · subst X
      simp [Real.log_zero]
    · have hX1 : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX)
      have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
      exact add_nonneg zero_le_one hlog
  calc
    mainTermInnerSum y X ≤ (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) :=
      mainTermInnerSum_le X y
    _ ≤ (x : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (by exact_mod_cast hyx)
              (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))) hlogX

/-! ## 4. The q factor: weighted reciprocal-totient sum

For squarefree `q`, `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`.
Subset expansion gives
`Σ_{q≤Q, squarefree} ∏_{p|q} c_p ≤ ∏_{p≤Q} (1+c_p)`.
Using `∏(1+u) ≤ exp(Σu)` and Mertens' second theorem
(`mertensSecond_nat`) yields
`Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

The ingredients are elementary: `μ²` is 1 on squarefree integers
and 0 otherwise; squarefree integers are determined by their
prime-factor sets; and `Σ 1/(p-1) ≤ 2Σ 1/p`, followed by Mertens.
-/

private lemma squarefree_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    n = ∏ p ∈ n.primeFactors, p := by
  exact (Nat.prod_primeFactors_of_squarefree hn).symm

/-- Subset expansion:
`∏_{x∈s} (1+g x) = Σ_{t⊆s} ∏_{x∈t} g x`. -/
private lemma sum_powerset_prod {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℝ) :
    (∑ t ∈ s.powerset, ∏ x ∈ t, g x) = ∏ x ∈ s, (1 + g x) := by
  exact (Finset.prod_one_add s).symm

/-- Main-term weight for squarefree `q`:
`μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`. -/
theorem panMainTotientWeight_term_squarefree (q : ℕ) (hq : Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
  have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  have hφ : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_primeFactors_of_squarefree hq, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub hp1]
    norm_num
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
        = (3 : ℝ) ^ q.primeFactors.card / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [hmu, hφ]
          norm_num
    _ = (∏ p ∈ q.primeFactors, (3 : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [← Finset.prod_const]
    _ = ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          rw [← Finset.prod_div_distrib]

/-- The main-term weight vanishes for nonsquarefree `q`, since `μ(q) = 0`. -/
theorem panMainTotientWeight_term_non_squarefree (q : ℕ) (hq : ¬ Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) = 0 := by
  have hmu : (μ q : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
  simp [hmu]

/-- The main-term weight, including its totient denominator, is nonnegative. -/
private lemma panMainTotientWeight_term_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
    (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **Subset bound**: for nonnegative coefficients,
`Σ_{q≤Q, squarefree} ∏_{p|q} c p ≤ ∏_{p≤Q} (1+c p)`.
A squarefree integer is determined by its prime-factor set,
`q = ∏ p ∈ q.primeFactors, p`, and the product on the right
expands into the sum of `∏_{p∈S} c p` over all subsets
`S ⊆ {p prime : p ≤ Q}`. -/
theorem sum_squarefree_prod_primeFactors_le_prod_one_add (Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ p : ℕ, p.Prime → 0 ≤ c p) :
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p) ≤
      ∏ p ∈ primesUpTo Q, (1 + c p) := by
  classical
  have hg : Set.InjOn (fun q : ℕ => q.primeFactors)
      (↑((Finset.range (Q + 1)).filter Squarefree) : Set ℕ) := by
    intro a ha b hb hgab
    have haSq : Squarefree a := (Finset.mem_filter.mp ha).2
    have hbSq : Squarefree b := (Finset.mem_filter.mp hb).2
    calc
      a = ∏ p ∈ a.primeFactors, p := squarefree_eq_prod_primeFactors haSq
      _ = ∏ p ∈ b.primeFactors, p := by
            have hgab' : a.primeFactors = b.primeFactors := by simpa using hgab
            rw [← hgab']
      _ = b := (squarefree_eq_prod_primeFactors hbSq).symm
  have him : ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors) ⊆
      (primesUpTo Q).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨q, hq, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hqmem : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hq).1
    have hqSq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hq_le : q ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem)
    have hq_ne : q ≠ 0 := by
      intro hq0
      rw [hq0] at hqSq
      exact not_squarefree_zero (R := ℕ) hqSq
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq_ne) hp_dvd
    exact (mem_primesUpTo).2 ⟨hp_pr, le_trans hp_le_q hq_le⟩
  calc
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p)
        = ∑ S ∈ ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors),
            ∏ p ∈ S, c p := by
          exact (Finset.sum_image (g := fun q : ℕ => q.primeFactors)
            (f := fun S : Finset ℕ => ∏ p ∈ S, c p) hg).symm
    _ ≤ ∑ S ∈ (primesUpTo Q).powerset, ∏ p ∈ S, c p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg him (fun S hSt hSn => by
            exact Finset.prod_nonneg (fun p hp => hc p
              ((mem_primesUpTo.mp ((Finset.mem_powerset.mp hSt) hp)).1)))
    _ = ∏ p ∈ primesUpTo Q, (1 + c p) := by
          rw [sum_powerset_prod (primesUpTo Q) c]

/-- The weighted reciprocal-totient sum is bounded by
`∏_{p≤Q} (1+3/(p-1))`. -/
theorem panMainTotientWeightedSum_le_prod_one_add (Q : ℕ) :
    panMainTotientWeightedSum Q ≤
      ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
  unfold panMainTotientWeightedSum
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        = ∑ q ∈ Finset.range (Q + 1),
            if Squarefree q then
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases h : Squarefree q
          · rw [if_pos h]
          · rw [if_neg h]
            exact panMainTotientWeight_term_non_squarefree q h
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact panMainTotientWeight_term_squarefree q (Finset.mem_filter.mp hq).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
          exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
            (fun p => (3 : ℝ) / ((p : ℝ) - 1)) (by
              intro p hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              exact div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hpm1))

/-- The weighted reciprocal-totient sum is monotone in `Q`,
since its summands are nonnegative. -/
theorem panMainTotientWeightedSum_mono : Monotone panMainTotientWeightedSum := by
  intro Q₁ Q₂ hQ
  unfold panMainTotientWeightedSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hQ))
    (fun q _ _ => panMainTotientWeight_term_nonneg q)

/-- **Polylogarithmic q-factor bound**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
Use subset expansion, `∏(1+u) ≤ exp(Σu)`,
`Σ_{p≤Q} 3/(p-1) ≤ 6·Σ_{p≤Q} 1/p`, and Mertens' second theorem.
Absorb the finite initial range `Q ≤ 2` into the constant. -/
theorem panMainTotientWeightedSum_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      panMainTotientWeightedSum Q ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ := mertensSecond_nat
  let K : ℝ := |mertensSecondConstant| + C₁ / log 2
  let C : ℝ := max (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))
  have hlg2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left (div_pos (by norm_num : (0 : ℝ) < 4) (Real.rpow_pos_of_pos hlg2 (6 : ℝ)))
  refine ⟨C, hCpos, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 2
  · have hbnd : panMainTotientWeightedSum Q ≤ 4 := by
      calc
        panMainTotientWeightedSum Q ≤ panMainTotientWeightedSum 2 := panMainTotientWeightedSum_mono hQ
        _ ≤ ∏ p ∈ primesUpTo 2, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := panMainTotientWeightedSum_le_prod_one_add 2
        _ = 4 := by
              have hP : primesUpTo 2 = ({2} : Finset ℕ) := by
                ext p
                constructor
                · intro hp
                  have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
                  have hp_le : p ≤ 2 := (mem_primesUpTo.mp hp).2
                  interval_cases p
                  · norm_num at hp_pr
                  · norm_num at hp_pr
                  · simp
                · intro hp
                  have hp2 : p = 2 := by simpa using hp
                  subst p
                  exact mem_primesUpTo.2 ⟨by norm_num, by norm_num⟩
              rw [hP]
              norm_num
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log 2) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlg2)
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    calc
      panMainTotientWeightedSum Q ≤ 4 := hbnd
      _ = 4 / (log 2) ^ (6 : ℝ) * (log 2) ^ (6 : ℝ) := by
        have hx : (log 2) ^ (6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlg2 (6 : ℝ)).ne'
        field_simp [hx]
      _ ≤ 4 / (log 2) ^ (6 : ℝ) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogle
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt (Real.rpow_pos_of_pos hlg2 (6 : ℝ))))
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (le_max_left (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K)))
          (Real.rpow_nonneg hlgQ2nn (6 : ℝ))
  · have hQ3 : 3 ≤ Q := by omega
    have hQ2 : 2 ≤ Q := by omega
    have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
    have hlogQ : (0 : ℝ) < log (Q : ℝ) := Real.log_pos hQ1
    have hlogQnn : (0 : ℝ) ≤ log (Q : ℝ) := le_of_lt hlogQ
    have hM' : |primeReciprocalSum Q - (log (log (Q : ℝ)) + mertensSecondConstant)| ≤
        C₁ / log (Q : ℝ) := hM Q hQ2
    have hpRS : primeReciprocalSum Q ≤ log (log (Q : ℝ)) + K := by
      have hle1 : primeReciprocalSum Q ≤
          log (log (Q : ℝ)) + mertensSecondConstant + C₁ / log (Q : ℝ) := by
        linarith [(abs_le.mp hM').2]
      have hc : mertensSecondConstant ≤ |mertensSecondConstant| := le_abs_self _
      have hC : C₁ / log (Q : ℝ) ≤ C₁ / log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hC₁) hlg2
          (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
      dsimp [K]
      linarith
    have hsum : (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) ≤ 6 * primeReciprocalSum Q := by
      calc
        (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1))
            ≤ ∑ p ∈ primesUpTo Q, (6 : ℝ) / (p : ℝ) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              have hppos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              rw [div_le_div_iff₀ hpm1 hppos]
              nlinarith
        _ = 6 * (∑ p ∈ primesUpTo Q, 1 / (p : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              ring
        _ = 6 * primeReciprocalSum Q := by
              unfold primeReciprocalSum
              rfl
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log (Q : ℝ)) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow hlogQnn
        (Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ)) (by exact_mod_cast (by omega : Q ≤ Q + 2)))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    calc
      panMainTotientWeightedSum Q ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) :=
            panMainTotientWeightedSum_le_prod_one_add Q
      _ ≤ rexp (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) := by
            -- Nonnegativity is needed only for primes in the product.
            rw [Real.exp_sum]
            apply Finset.prod_le_prod
            · intro p hp
              have hp1 : (1 : ℝ) ≤ p := by
                exact_mod_cast (mem_primesUpTo.mp hp).1.one_lt.le
              exact add_nonneg zero_le_one (div_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            · intro p hp
              simpa only [add_comm] using Real.add_one_le_exp ((3 : ℝ) / ((p : ℝ) - 1))
      _ ≤ rexp (6 * primeReciprocalSum Q) := by
            exact Real.exp_le_exp.mpr hsum
      _ ≤ rexp (6 * (log (log (Q : ℝ)) + K)) := by
            exact Real.exp_le_exp.mpr (by
              have h6 : (0 : ℝ) ≤ 6 := by norm_num
              exact mul_le_mul_of_nonneg_left hpRS h6)
      _ = rexp (6 * K) * (log (Q : ℝ)) ^ (6 : ℝ) := by
            rw [mul_add, Real.exp_add, mul_comm 6 (log (log (Q : ℝ))),
              Real.exp_mul, Real.exp_log hlogQ, mul_comm]
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
            exact mul_le_mul (le_max_right (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))) hlogle
              (Real.rpow_nonneg hlogQnn (6 : ℝ)) (le_of_lt hCpos)


/-! ## 5. Combined polylogarithmic main-term bound

Under `|f| ≤ 1`, the weighted main-term sum is bounded by
`C·|xX|·(1+log X)·log⁶(Q+2)`, using the elementary proxy estimate
`|li(m)| ≤ m/log 2`, the harmonic sum, and the q-factor bound.
This is the intermediate estimate for `PanMainTermSieveBound`.
Its absorption into `C·xX·(log xX)^{A+7}` is the content of
`PanMainSieveAbsorption` in §6: a fixed polylogarithmic factor
is dominated by a larger logarithmic power. -/
theorem panMainWeightedSum_polylog (x : ℕ → ℝ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ,
      (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q' _ => logarithmicIntegral (y : ℝ) / Nat.totient q')) ≤
        C * |x X| * (1 + Real.log (X : ℝ)) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hQ⟩ := panMainTotientWeightedSum_le_polylog
  let C : ℝ := C₁ / log 2
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos hC₁ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C, hCpos, ?_⟩
  intro X Q
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    by_cases hX : X = 0
    · subst X
      simp [Real.log_zero]
    · have hX1 : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX)
      have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
      linarith
  have hfloor_abs : (Nat.floor (x X) : ℝ) ≤ |x X| := by
    by_cases hx : 0 ≤ x X
    · exact le_trans (Nat.floor_le hx) (le_abs_self (x X))
    · have hx' : x X < 1 := lt_trans (lt_of_not_ge hx) (by norm_num : (0 : ℝ) < 1)
      have hf : Nat.floor (x X) = 0 := Nat.floor_eq_zero.mpr hx'
      simp [hf]
  have hmain : mainTermInnerSumMax X (Nat.floor (x X)) ≤
      |x X| / log 2 * (1 + Real.log (X : ℝ)) := by
    calc
      mainTermInnerSumMax X (Nat.floor (x X)) ≤
          (Nat.floor (x X) : ℝ) / log 2 * (1 + Real.log (X : ℝ)) :=
        mainTermInnerSumMax_le X (Nat.floor (x X))
      _ ≤ |x X| / log 2 * (1 + Real.log (X : ℝ)) := by
        have hd : (Nat.floor (x X) : ℝ) / log 2 ≤ |x X| / log 2 :=
          div_le_div_of_nonneg_right hfloor_abs
            (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        exact mul_le_mul_of_nonneg_right hd hlogX
  have hqnonneg : (0 : ℝ) ≤ C₁ * (Real.log (Q + 2)) ^ (6 : ℝ) := by
    have hlg : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    exact mul_nonneg (le_of_lt hC₁) (Real.rpow_nonneg hlg (6 : ℝ))
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q' _ => logarithmicIntegral (y : ℝ) / Nat.totient q'))
        ≤ mainTermInnerSumMax X (Nat.floor (x X)) * panMainTotientWeightedSum Q := by
          simpa [panMainTotientWeightedSum] using
            panMainWeightedSum_le X Q (Nat.floor (x X)) f hfb
    _ ≤ mainTermInnerSumMax X (Nat.floor (x X)) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hQ Q) (mainTermInnerSumMax_nonneg X (Nat.floor (x X)))
    _ ≤ (|x X| / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hmain hqnonneg
    _ = C * |x X| * (1 + Real.log (X : ℝ)) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
          dsimp [C]
          ring

/-! ## 6. Polylogarithmic absorption and the main-term sieve bound -/

/-- **Polylogarithmic absorption proposition**: assume the sieve scale
dominates the summation range, `X ≤ x X` (as for `x X = (X : ℝ)`).
Then the fixed factor `(1+log X)·log⁶(xX+2)` is eventually dominated
by any larger logarithmic power:
`∀ A > 0, ∃ C > 0, x₀, ∀ X ≥ x₀,
 xX·(1+log X)·log⁶(xX+2) ≤ C·xX·(log xX)^{A+7}`.

Replacing the right side by `C·xX/log^A(xX)` is impossible:
for `x X ≡ 2`, the factor `1+log X` is unbounded while the right
side is constant; for `x X = X`, it would require
`(1+log X)·log⁶(X+2) ≤ C/log^A X`, whose left side grows like
`log⁷X` and whose right side tends to zero.

The classical error `O(x/log^A x)` comes from subtracting the
sieve main term `x/log x·∏(1-ν(p))` from `li`
(Liu 2022 §III; HR 1974 Ch. 10), requiring signed main-term
and sieve-product analysis (see `PAN_PROOF_ATLAS.md`).
A bound on one absolute contribution only gives a larger log power,
of total degree 7 here. `panMainSieveAbsorption_of_dom` in §6.1
proves this proposition. -/
def PanMainSieveAbsorption (x : ℕ → ℝ) : Prop :=
  (∀ X : ℕ, (X : ℝ) ≤ x X) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
          C * x X * (Real.log (x X)) ^ (A + 7)

/-! ## 6.1 Proof of polylogarithmic absorption

For `(X : ℝ) ≤ x X`, the proof has three steps:

1. **Eventual log lower bound** (`panMainSieve_log_ge_one`):
   monotonicity gives `log X ≤ log(xX)`, while
   `Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop`
   gives `log X → ∞`. Hence eventually `1 ≤ log(xX)`.
2. **Product bound** (`panMainSieve_polylog_le`, natural powers):
   for `X ≥ 2` and `1 ≤ log(xX)`,
   `log(xX+2) ≤ log(2·xX) = log 2 + log(xX) ≤ 2·log(xX)`,
   and `1+log X ≤ 2·log(xX)`. Thus
   `(1+log X)·log⁶(xX+2) ≤ (2L)·(2L)^6 = 128·log⁷(xX)`.
3. **Larger exponent** (`panMainSieveAbsorption_of_dom`):
   for base `log(xX) ≥ 1`, use
   `Real.rpow_le_rpow_of_exponent_le` and `7 ≤ A+7` from `A > 0`,
   then multiply by `xX ≥ 0`.

The theorem `not_panMainSieveAbsorption_old_natCast` disproves
the corresponding logarithmic-saving absorption for `x X = X`.
Taking `A = 1` and cancelling `X > 0` would give
`(1+log X)·log⁶(X+2)·log X ≤ C`; its left side is at least
`log X → ∞`, contradicting every fixed `C`.
Even refining the inner-sum upper bound to the classical
`C·xX·(1+log log xX)` shape in suitable ranges does not turn
the additional `log⁶` upper bound into a logarithmic saving.
Such a saving concerns a difference,
`|li main term − sieve main term| ≪ x/log^A x`,
with the sieve product written as `∏(1-ν(p)/p)` when `ν`
uses the unnormalized density convention. It is not a bound
on the separate absolute contributions.

There is also a decomposition issue (see `PanVaughanPointwise.lean`):
this module bounds the coarse pure-`|li|` inner sum
`mainTermInnerSumMax·Σ`. By contrast, finite Vaughan algebra
(`panWeightedVonMangoldt_abs_le`) produces
`|Σ f(a)·(apSmall − apMiddle)|`.
After the analytic ψ-to-π conversion, the classical third piece is
the signed difference
`|Σ f(a)·((apSmall − apMiddle)/log(y/a) − li(y/a)/φ(q))|`.
The separate signed assembly must control this PNT-level main term;
the pure-`li` polylogarithmic bound cannot replace it.
See `PAN_PROOF_ATLAS.md` for the signed-main-term and Chen-weight
requirements. The proof here uses elementary mathlib analysis:
limits, real powers, and logarithm monotonicity.
-/

section PanMainSieveAbsorption_proof

open Filter

/-- **Eventual logarithmic lower bound**: if `(X : ℝ) ≤ x X`,
then eventually `1 ≤ log(x X)`, from `log X → ∞` and
`log X ≤ log(xX)`. -/
theorem panMainSieve_log_ge_one {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (x X) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) := hlogX (eventually_ge_atTop 1)
  filter_upwards [hge, eventually_ge_atTop (1 : ℕ)] with X h1 hX1
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num) hX1r
  exact le_trans h1 (Real.log_le_log hXpos (hdom X))

/-- **Polylogarithmic product bound (natural powers)**: under
`(X : ℝ) ≤ x X`, eventually
`(1+log X)·log⁶(xX+2) ≤ 128·log⁷(xX)`.
The first factor is at most `2·log(xX)` once `1 ≤ log(xX)`;
the second is at most `(2·log(xX))^6`, by monotonicity,
`log(2·xX) = log 2 + log(xX)`, and `log 2 ≤ log(xX)`. -/
theorem panMainSieve_polylog_le {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    ∀ᶠ X : ℕ in atTop,
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 ≤
        128 * (Real.log (x X)) ^ 7 := by
  filter_upwards [panMainSieve_log_ge_one hdom, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop (2 : ℕ)] with X hL hX1 hX2
  have hxXgeX : (X : ℝ) ≤ x X := hdom X
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num) hX1r
  have hxXpos : (0 : ℝ) < x X := lt_of_lt_of_le hXpos hxXgeX
  have hlogXle : Real.log (X : ℝ) ≤ Real.log (x X) := Real.log_le_log hXpos hxXgeX
  have h1add : 1 + Real.log (X : ℝ) ≤ 2 * Real.log (x X) := by nlinarith [hL, hlogXle]
  have hX2r : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hxX2 : (2 : ℝ) ≤ x X := le_trans hX2r hxXgeX
  have hlogadd_le2 : Real.log (x X + 2) ≤ 2 * Real.log (x X) := by
    calc
      Real.log (x X + 2) ≤ Real.log (2 * x X) :=
        Real.log_le_log (by positivity : (0 : ℝ) < x X + 2) (by nlinarith [hxX2])
      _ = Real.log 2 + Real.log (x X) :=
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxXpos)
      _ ≤ Real.log (x X) + Real.log (x X) := by
        have hlog2le : Real.log 2 ≤ Real.log (x X) :=
          Real.log_le_log (by norm_num : (0 : ℝ) < 2) hxX2
        linarith
      _ = 2 * Real.log (x X) := by ring
  have hlogadd_nn : (0 : ℝ) ≤ Real.log (x X + 2) := by
    have hlogadd_ge : Real.log (x X) ≤ Real.log (x X + 2) :=
      Real.log_le_log hxXpos (by nlinarith)
    linarith
  have hpow6 : (Real.log (x X + 2)) ^ 6 ≤ (2 * Real.log (x X)) ^ 6 :=
    pow_le_pow_left₀ hlogadd_nn hlogadd_le2 6
  have hb : (0 : ℝ) ≤ 2 * Real.log (x X) := by nlinarith [hL]
  calc
    (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6
        ≤ (2 * Real.log (x X)) * (2 * Real.log (x X)) ^ 6 := by
      exact mul_le_mul h1add hpow6 (pow_nonneg hlogadd_nn 6) hb
    _ = 128 * (Real.log (x X)) ^ 7 := by ring

/-- **Polylogarithmic absorption under domination**: for `X ≤ x X`,
use `C = 128` and an eventual threshold covering `1 ≤ log(xX)`
and `X ≥ 1`. The fixed factor is dominated by a larger log power;
`eventually_atTop.mp` converts eventuality into an explicit `∃ x₀`. -/
theorem panMainSieveAbsorption_of_dom {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    PanMainSieveAbsorption x := by
  refine ⟨hdom, ?_⟩
  intro A hA
  refine ⟨128, by norm_num, ?_⟩
  have hpow7 : ∀ᶠ X : ℕ in atTop,
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
        128 * (Real.log (x X)) ^ (A + 7) := by
    filter_upwards [panMainSieve_polylog_le hdom, panMainSieve_log_ge_one hdom] with X hprod hL
    calc
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)
          ≤ (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 := by
        have heq : (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) =
            (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 := by
          simp
        exact le_of_eq heq
      _ ≤ 128 * (Real.log (x X)) ^ 7 := hprod
      _ ≤ 128 * (Real.log (x X)) ^ (A + 7) := by
        have h7 : (Real.log (x X)) ^ 7 = (Real.log (x X)) ^ (7 : ℝ) := by
          simp
        have hle : (Real.log (x X)) ^ (7 : ℝ) ≤ (Real.log (x X)) ^ (A + 7) :=
          Real.rpow_le_rpow_of_exponent_le hL (by linarith : (7 : ℝ) ≤ A + 7)
        rw [h7]
        exact mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 128)
  have hev : ∀ᶠ X : ℕ in atTop,
      x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
        128 * x X * (Real.log (x X)) ^ (A + 7) := by
    filter_upwards [hpow7, eventually_ge_atTop (1 : ℕ)] with X hpowX hX1
    have hX0r : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 0 ≤ X)
    have hxXnn : (0 : ℝ) ≤ x X := le_trans hX0r (hdom X)
    calc
      x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)
          = x X * ((1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)) := by ring
      _ ≤ x X * (128 * (Real.log (x X)) ^ (A + 7)) := by
        exact mul_le_mul_of_nonneg_left hpowX hxXnn
      _ = 128 * x X * (Real.log (x X)) ^ (A + 7) := by ring
  exact eventually_atTop.mp hev

/-- The scale `x X = (X : ℝ)` satisfies domination definitionally,
so it satisfies `PanMainSieveAbsorption`. -/
theorem panMainSieveAbsorption_natCast :
    PanMainSieveAbsorption (fun N : ℕ => (N : ℝ)) := by
  apply panMainSieveAbsorption_of_dom
  intro X
  rfl

/-- **Counterexample to logarithmic-saving absorption**:
for `x X = (X : ℝ)`, the assertion that the polylogarithmic factor
is bounded by `C·xX/log^A(xX)` is false.
Take `A = 1` and cancel `X > 0`; the inequality becomes
`(1+log X)·log⁶(X+2)·log X ≤ C`, with left side at least
`log X → ∞`. Thus every `C > 0` and threshold `x₀` are exceeded.
This is the obstruction in §6: the coarse pure-main-term bound
under `|f| ≤ 1`, after discarding coprimality weights, cannot yield
`x/log^A x`. The classical saving is a signed difference estimate
involving the sieve main term. -/
theorem not_panMainSieveAbsorption_old_natCast :
    ¬ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        (X : ℝ) * (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) ≤
          C * (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
  intro h
  rcases h 1 (by norm_num) with ⟨C, hC, x₀, hb⟩
  let f : ℕ → ℝ := fun X =>
    (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) *
      (Real.log (X : ℝ)) ^ (1 : ℝ)
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2X : Tendsto (fun X : ℕ => Real.log ((X : ℝ) + 2)) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    exact tendsto_atTop_mono (fun X => by linarith) tendsto_natCast_atTop_atTop
  have h2ge1 : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log ((X : ℝ) + 2) := hlog2X (eventually_ge_atTop 1)
  have h0ge : ∀ᶠ X : ℕ in atTop, 0 ≤ Real.log (X : ℝ) := hlogX (eventually_ge_atTop 0)
  have hfge : ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) ≤ f X := by
    filter_upwards [h2ge1, h0ge] with X h2 h0
    have h2p : (1 : ℝ) ≤ (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) :=
      Real.one_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 6)
    have h1 : (1 : ℝ) ≤ 1 + Real.log (X : ℝ) := by linarith
    dsimp [f]
    calc
      Real.log (X : ℝ) ≤
          (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) *
            (Real.log (X : ℝ)) := by
        calc
          Real.log (X : ℝ) = 1 * Real.log (X : ℝ) := by ring
          _ ≤ (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) *
              Real.log (X : ℝ) := by
            have h' : (1 : ℝ) ≤ (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) := by
              calc
                (1 : ℝ) ≤ (1 + Real.log (X : ℝ)) * 1 := by nlinarith [h1]
                _ ≤ (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) := by
                  exact mul_le_mul_of_nonneg_left h2p (by linarith : 0 ≤ 1 + Real.log (X : ℝ))
            exact mul_le_mul_of_nonneg_right h' h0
      _ = (1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ) *
          (Real.log (X : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_one]
  have hf_tend : Tendsto f atTop atTop := tendsto_atTop_mono' atTop hfge hlogX
  have hgt : ∀ᶠ X : ℕ in atTop, C + 1 ≤ f X := hf_tend (eventually_ge_atTop (C + 1))
  rcases eventually_atTop.mp hgt with ⟨x₁, hx₁⟩
  let X : ℕ := max x₀ (max x₁ 2)
  have hX₀ : x₀ ≤ X := by omega
  have hX₁ : x₁ ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hX1r : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_trans (by norm_num) hX1r
  have hBpos : 0 < (Real.log (X : ℝ)) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact Real.log_pos hX1r
  have hbX := hb X hX₀
  have hb' : (X : ℝ) * ((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) ≤
      C * (X : ℝ) / (Real.log (X : ℝ)) ^ (1 : ℝ) := by
    simpa [mul_assoc] using hbX
  have hb'' : (X : ℝ) * (((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) *
      (Real.log (X : ℝ)) ^ (1 : ℝ)) ≤ C * (X : ℝ) := by
    calc
      (X : ℝ) * (((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) *
          (Real.log (X : ℝ)) ^ (1 : ℝ))
          ≤ (C * (X : ℝ) / (Real.log (X : ℝ)) ^ (1 : ℝ)) *
              (Real.log (X : ℝ)) ^ (1 : ℝ) := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_right hb' (le_of_lt hBpos))
      _ = C * (X : ℝ) := by
        field_simp [ne_of_gt hBpos]
  have hA' : ((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) *
      (Real.log (X : ℝ)) ^ (1 : ℝ) ≤ C := by
    have hm : (X : ℝ) * (((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) *
        (Real.log (X : ℝ)) ^ (1 : ℝ)) ≤ (X : ℝ) * C := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hb''
    exact le_of_mul_le_mul_left hm hXpos
  have hfX : f X = ((1 + Real.log (X : ℝ)) * (Real.log ((X : ℝ) + 2)) ^ (6 : ℝ)) *
      (Real.log (X : ℝ)) ^ (1 : ℝ) := rfl
  have hgtX : C + 1 ≤ f X := hx₁ X hX₁
  linarith [hA', hgtX, hfX]

end PanMainSieveAbsorption_proof

/-- **Main-term sieve-bound assembly**:
`PanMainSieveAbsorption` implies `PanMainTermSieveBound`.
The proxy bound, harmonic sum, q-factor estimate, floor/square-root
reductions, and nonnegative weights are handled here; absorption is
the analytic input. The right side is the polylogarithmic
`C·xX·(log xX)^{A+7}`, not a logarithmic saving. -/
theorem PanMainTermSieveBound.of_innerSumBound {x : ℕ → ℝ} {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) (hAbs : PanMainSieveAbsorption x) :
    PanMainTermSieveBound x f := by
  rcases hAbs with ⟨hdom, hAbs'⟩
  obtain ⟨C₁, hC₁, hQ⟩ := panMainTotientWeightedSum_le_polylog
  refine ⟨hfb, fun A hA => ?_⟩
  obtain ⟨C₂, hC₂, x₀, hAbsX⟩ := hAbs' A hA
  let C : ℝ := C₁ * C₂ / log 2
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos hC₁ hC₂) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  -- Also require X ≥ 1 beyond the absorption threshold, so xX ≥ X ≥ 1 > 0.
  refine ⟨C, hCpos, (0 : ℝ), max x₀ 1, ?_⟩
  intro X hX
  have hX₀ : x₀ ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  let Q : ℕ := Nat.floor ((x X) ^ (1 / 2 : ℝ))
  have hQdef : Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ (0 : ℝ)) = Q := by
    simp [Q, Real.rpow_zero]
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
    linarith
  have hxXgeX : (X : ℝ) ≤ x X := hdom X
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hxXpos : (0 : ℝ) < x X :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hX1r) hxXgeX
  have hxXone : (1 : ℝ) ≤ x X := le_trans hX1r hxXgeX
  have hfloor : (Nat.floor (x X) : ℝ) ≤ x X := Nat.floor_le (le_of_lt hxXpos)
  have hsqrt : (x X) ^ (1 / 2 : ℝ) ≤ x X := by
    rw [← Real.sqrt_eq_rpow]
    calc
      √(x X) ≤ √((x X) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hxXone] : (x X : ℝ) ≤ (x X) ^ 2)
      _ = x X := Real.sqrt_sq (le_of_lt hxXpos)
  have hQle : (Q : ℝ) ≤ x X := by
    dsimp [Q]
    exact le_trans (Nat.floor_le (Real.rpow_nonneg (le_of_lt hxXpos) (1 / 2 : ℝ))) hsqrt
  have hQlog : Real.log (Q + 2) ≤ Real.log (x X + 2) := by
    have hpos : (0 : ℝ) < (Q : ℝ) + 2 := by positivity
    have hle : ((Q + 2 : ℕ) : ℝ) ≤ x X + 2 := by
      norm_num [Nat.cast_add]
      exact hQle
    exact Real.log_le_log hpos (by simpa [Nat.cast_add] using hle)
  have hlogle : (Real.log (Q + 2)) ^ (6 : ℝ) ≤ (Real.log (x X + 2)) ^ (6 : ℝ) := by
    have hlognn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    exact Real.rpow_le_rpow hlognn hQlog (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
  have hmain : mainTermInnerSumMax X (Nat.floor (x X)) ≤
      x X / log 2 * (1 + Real.log (X : ℝ)) := by
    calc
      mainTermInnerSumMax X (Nat.floor (x X)) ≤
          (Nat.floor (x X) : ℝ) / log 2 * (1 + Real.log (X : ℝ)) :=
        mainTermInnerSumMax_le X (Nat.floor (x X))
      _ ≤ x X / log 2 * (1 + Real.log (X : ℝ)) := by
        have hd : (Nat.floor (x X) : ℝ) / log 2 ≤ x X / log 2 :=
          div_le_div_of_nonneg_right hfloor (le_of_lt hlog2)
        exact mul_le_mul_of_nonneg_right hd hlogX
  calc
    mainTermInnerSumMax X (Nat.floor (x X)) *
        (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ (0 : ℝ)) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        = mainTermInnerSumMax X (Nat.floor (x X)) * panMainTotientWeightedSum Q := by
          rw [hQdef]
          rfl
    _ ≤ mainTermInnerSumMax X (Nat.floor (x X)) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hQ Q) (mainTermInnerSumMax_nonneg X (Nat.floor (x X)))
    _ ≤ (x X / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hmain (by
            have hlg : (0 : ℝ) ≤ Real.log (Q + 2) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
            exact mul_nonneg (le_of_lt hC₁) (Real.rpow_nonneg hlg (6 : ℝ)))
    _ ≤ (x X / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (x X + 2)) ^ (6 : ℝ)) := by
          have hcl : C₁ * (Real.log (Q + 2)) ^ (6 : ℝ) ≤
              C₁ * (Real.log (x X + 2)) ^ (6 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hlogle (le_of_lt hC₁)
          exact mul_le_mul_of_nonneg_left hcl (by
            have hnn : (0 : ℝ) ≤ x X / log 2 * (1 + Real.log (X : ℝ)) :=
              mul_nonneg (div_nonneg (le_of_lt hxXpos) (le_of_lt hlog2)) hlogX
            exact hnn)
    _ = (C₁ / log 2) * (x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)) := by
          ring
    _ ≤ (C₁ / log 2) * (C₂ * x X * (Real.log (x X)) ^ (A + 7)) := by
          exact mul_le_mul_of_nonneg_left (hAbsX X hX₀) (le_of_lt (div_pos hC₁ hlog2))
    _ = C * x X * (Real.log (x X)) ^ (A + 7) := by
          dsimp [C]
          ring

end AnalyticNumberTheory.Sieve
