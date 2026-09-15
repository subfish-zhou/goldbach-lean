import AnalyticNumberTheory.LargeSieve.BombieriDavenport
import AnalyticNumberTheory.Sieve.PanMainTerm
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.PanTypeIAssembly

## Primitive-to-all-character reductions for Type I mean values

This module relates the primitive-character Bombieri--Davenport estimate
`bombieriDavenport_vaughanFirst` in `BombieriDavenport.lean` to weighted
all-character Type I expressions. It proves structural reductions and
records further inputs as explicit propositions; it does not prove the
unrestricted uniform target below.

Available estimates:

- `bombieriDavenport_vaughanFirst (Q m u) (hQ : 0 < Q)`:
  `Σ_{1≤q≤Q} (q/φ(q))·Σ_{χ primitive mod q} ‖V_χ(m)‖²
   ≤ LSB(m+1, 1/Q²)·S(m)`, where
  `S(m) = Σ_{n≤m} vaughanFirst(n,u)²`.
- `panTypeICharSqSum_le_additiveSieve q m u hq`: for each modulus,
  `t_q(m) := Σ_{χ mod q} ‖V_χ(m)‖²
   ≤ (φ(q)/q)·LSB(m+1, 1/q²)·S(m)`.
- `panTypeI_charAbsSum_le_cs`:
  `Σ_χ‖V_χ‖ ≤ √φ(q)·√(t_q(m))`.
- `panTypeICharSqrtMeanMaxY_le_sieveSqrtSum`:
  `panTypeICharSqrtMeanMaxY X q x f u
   ≤ Σ_{y≤x}Σ_{a≤X} |f(a)|/|log(y/a)|
     ·√((φ/q)·LSB(y/a+1,1/q²))·√S(y/a)`.

The target `panTypeICharMeanSieveBound x f u` in `PanMeanValueBody.lean` is
`Σ_{q≤Q} μ²(q)3^{ω(q)}·√φ(q)·panTypeICharSqrtMeanMaxY X q (xX) f u
 ≤ C·xX/log^A(xX)`, with `Q = (xX)^{1/2}/log^B(xX)`.

## Limitation: the target is false uniformly over all |f| ≤ 1

Take `u = 1`, so `vaughanFirst(n,1) = log n`, and
`f = 1_{a = 1}` (`f(1) = 1`, zero elsewhere). Set `y = xX`, `a = 1`.
The principal character `χ₀ mod q` contributes to `t_q`:
`‖V_{χ₀}(xX)‖ = Σ_{n≤xX, (n,q)=1} log n
 ~ (φ(q)/q)·xX·log(xX)`, by elementary density estimates, without the PNT.
Since the maximum over `y` includes `y = xX` and all terms are nonnegative,

```text
LHS ≥ (1/log(xX))·Σ_{q≤Q} μ²(q)3^{ω(q)}·√φ(q)·‖V_{χ₀}(xX)‖
    ~ xX·Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)^{3/2}/q
    ≥ xX·Σ_{p≤Q, p prime} 3·(p−1)^{3/2}/p.
```

The prime sum has order `Q^{3/2}/log Q`, giving order
`(xX)^{7/4}/(log xX)^{1+3B/2}`. This exceeds `C·xX/log^A(xX)` for any
fixed `A, B, C` and sufficiently large `xX`. Thus uniformity over all
`(∀ a, |f a| ≤ 1)` is impossible. The classical Type I mean-value theorem
(Liu 2022 §III Lemma 1; HR 1974 Ch. 10) uses support conditions on `f`.
For Chen weights `f(a) = 1_{a = p₁p₂, z ≤ p₁ ≤ p₂}`, one has `f(1) = 0`
and control of `Σ_{a≤X}|f(a)|/a`. The proposed support-sensitive input
`panTypeI_charMeanSieveBound_chenWeight` is recorded in §S4; its precise
hypotheses still require comparison with the classical sources.

## S2: Conductor decomposition

For `χ mod q`, let `q' = χ.conductor`, with `q' | q`, and let `χ'` be its
unique primitive character. Mathlib provides `χ.FactorsThrough q'`,
`χ.primitiveCharacter`, and primitive-character induction. For `(n,q)=1`,
`χ(n) = χ'(n mod q')`; otherwise `χ(n) = 0`, by the convention for
nonunits. Consequently,

```text
V_χ(m) = Σ_{n≤m, (n,q)=1} vaughanFirst(n,u)·χ'(n mod q'),
‖V_χ(m)‖ ≤ ‖V_χ'(m)‖ + D_q(m),
D_q(m) = Σ_{n≤m, (n,q)>1} |vaughanFirst(n,u)|,
‖V_χ(m)‖² ≤ 2‖V_χ'(m)‖² + 2·D_q(m)².
```

Writing `P_{q'}(m) = Σ_{χ' primitive mod q'} ‖V_χ'(m)‖²`,
a sharper grouping argument with fiber bound `φ(q)/φ(q')` would give
`t_q(m) ≤ 2·Σ_{q'|q} (φ(q)/φ(q'))·P_{q'}(m) + 2·φ(q)·D_q(m)²`.
The theorem here instead proves the coarser coefficient `φ(q)`, by
termwise domination and fiber cardinality, without a dependent grouping
bijection. An injectivity-based coefficient 1 is not established here.
The related `star_conductor` and `star_isPrimitive` lemmas are used
elsewhere in the project.

- S2a `panTypeI_char_induced_by_primitive`: pointwise induction.
- S2b `panTypeI_sqSum_primitiveDecomposition`: square-sum decomposition
  with the coarse coefficient and the density term.
- S2c `panTypeI_nonCoprimeDensity_le_primePartition`: structural bound
  `D_q(m) ≤ Σ_{p|q} Σ_{n≤m, p|n} |vaughanFirst(n,u)|`.
  A quantitative density estimate would substitute `n = p·k`, use
  `vaughanFirst_abs_le`, namely `|vaughanFirst(n,u)| ≤ τ(n)·log(n+1)`,
  and estimate
  `Σ_{k≤m/p} τ(pk)·log(pk+1) ≤ C·(1/p)·m·log²(m+2)·polylog(p)`.
  The full density estimate is not proved in this module.

## S3: μ²3^ω weight estimates

The elementary estimates relevant to assembly have the following shapes:

```text
(W1) Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)/q ≤ C·Q·log⁶(Q+2)
     [φ(q)/q ≤ 1 and Σ μ²3^ω ≤ C·Q·log³(Q+2)]
(W2) Σ_{k≤Q/q'} μ²(q'k)3^{ω(q'k)}·(q'k)
     ≤ C·(Q²/q')·3^{ω(q')}·log⁶(Q+2)
     [q = q'·k, μ²(q'k) ≤ μ²(k),
      3^{ω(q'k)} ≤ 3^{ω(q')}·3^{ω(k)},
      Σ_{k≤K} μ²3^ω·k ≤ C·K²·log³(K+2)]
(W3) Σ_{q≤Q} μ²(q)3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2).
```

W1 and W2 use the same elementary ingredients as `PanMainTerm.lean` §4:
subset expansion, `sum_squarefree_prod_primeFactors_le_prod_one_add`,
and Mertens' second theorem `mertensSecond_nat`. W3 is supplied by
`panMainTotientWeightedSum_le_polylog`, restated here as
`panTypeI_totientWeightSum_polylog`. The definition
`panTypeI_threeOmegaWeightSums` records the estimate family; it is not
a proof of uniform W1 or W2.

## S4: Square-root reduction and assembly inputs

(1) **Cauchy--Schwarz algebra**: `csSqrtSum_le_card_mul_sum` proves
`(Σ_i √(a_i·b_i))² ≤ (card s)·Σ_i a_i·b_i` for `a_i·b_i ≥ 0`.
With `a_q = w_q·φ(q)/q`, `b_q = w_q·q·t_q(m)`, and `w_q = μ²3^ω`,
this yields
`(Σ_q w_q·√(φ(q)·t_q(m)))² ≤ (card)·Σ_q w_q²·φ(q)·t_q(m)`.
The related weighted Cauchy--Schwarz approach separates factors involving
`Σ_q (φ(q)/q)` and `Σ_q q·t_q(m)`; for `q ≤ Q`,
`q·t_q(m) ≤ Q·(q/φ(q))·t_q(m)` since `φ(q) ≤ q`.

(2) **All-character BD-shaped input**: `panTypeI_allCharSieveMean` records
`Σ_{q≤Q} μ²3^ω·(q/φ(q))·t_q(m)
 ≤ C·(m+Q²)·S(m)·log⁶(Q+2)`.
The proposed route is conductor decomposition, reordering with `q = q'·k`,
applying `bombieriDavenport_vaughanFirst` to `P_{q'}(m)` for `q' ≤ Q`,
and controlling the non-coprime term by a density estimate.
The weaker large-sieve constant has shape
`LSB(m+1, 1/Q²) ~ m + Q²·log Q`; see the discussion in
`BombieriDavenport.lean`. For a fixed divisor `q'`, weight transfer gives
`(φ(q)/φ(q'))·(q/φ(q)) = q/φ(q')`.
The W2 factor `Q²/q'` introduces an extra `Q²` in naive assembly.
An argument using the `(q'/φ(q'))`-weighted primitive bound together
with W1/W3 therefore requires precise weight bookkeeping; no uniform
all-character conclusion is supplied by this definition.

(3) **Outer `(y,a)` weights**: after replacing the maximum using
`panTypeICharSqrtMeanMaxY_le_sieveSqrtSum`, the remaining expression has
the form
`Σ_{y,a} |f(a)|/|log(y/a)|·(φ(q)/√q)·√LSB·√S`.
Control of `Σ_{a≤X}|f(a)|/a` for Chen weights is central to this step;
the counterexample above excludes uniformity under `|f| ≤ 1` alone.
References: Liu 2022 §III Lemma 1; HR 1974 Ch. 10.

The proved components are pointwise induction, the norm and square
reductions, the coarse fiber decomposition, the prime-partition density
bound, Cauchy--Schwarz algebra, and W3. Sharper fiber bookkeeping, quantitative
density control, uniform weight assembly, and the precise support-sensitive
mean-value input remain separate requirements.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open DirichletCharacter
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

set_option maxHeartbeats 4000000

/-! ## S3: The totient-weight sum -/

/-- **W3**, restated from `PanMainTerm`:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
This is one factor in the S3 weight assembly (`PanMainTerm.lean` §4). -/
theorem panTypeI_totientWeightSum_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
        C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  simpa [panMainTotientWeightedSum] using panMainTotientWeightedSum_le_polylog

/-! ## S2: Conductor decomposition and the structural density bound -/

/-! ### S2a: Pointwise induction via mathlib's primitiveCharacter

Mathlib provides `χ.primitiveCharacter` at level `χ.conductor`,
`changeLevel_primitiveCharacter`
(`χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter`),
`primitiveCharacter_isPrimitive`, and
`primitiveCharacter_apply_of_isCoprime`
(`(a,q)=1 ⟹ χ.primitiveCharacter a = χ a`). These give S2a directly. -/

/-- **Pointwise S2a**: if `(n,q) = 1`, then
`χ(n mod q) = χ.primitiveCharacter(n mod χ.conductor)`. -/
lemma dirichletChar_eq_primitiveCharacter_of_coprime {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hcop : n.Coprime q) :
    χ (n : ZMod q) = χ.primitiveCharacter (n : ZMod χ.conductor) := by
  simpa using
    (χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hcop)).symm

/-- **S2a**: each character `χ mod q` is induced by its unique primitive
character `χ.primitiveCharacter mod χ.conductor` (uniqueness follows from
injectivity of `changeLevel`). The pointwise equality holds for `(n,q)=1`;
on non-coprime arguments, `MulChar` uses the value 0. -/
theorem panTypeI_char_induced_by_primitive (q : ℕ) [NeZero q] :
    ∀ χ : DirichletCharacter ℂ q, ∃ q' : ℕ, q' ∣ q ∧
      ∃ χ' : DirichletCharacter ℂ q', χ'.IsPrimitive ∧
        ∀ n : ℕ, n.Coprime q → χ (n : ZMod q) = χ' (n : ZMod q') := by
  intro χ
  refine ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter,
    χ.primitiveCharacter_isPrimitive, ?_⟩
  intro n hn
  exact dirichletChar_eq_primitiveCharacter_of_coprime χ hn

/-! ### Pointwise components of the S2 square-sum decomposition -/

/-- Coprime-part decomposition of `V_χ(m)`: non-coprime terms vanish. -/
lemma panTypeIV1CharSum_eq_coprimePart {q m u : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    panTypeIV1CharSum q m u χ =
      ∑ n ∈ Finset.range (m + 1),
        (if n.Coprime q then (vaughanFirst n u : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)
         else 0) := by
  unfold panTypeIV1CharSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime q
  · simp [hc, dirichletChar_eq_primitiveCharacter_of_coprime χ hc]
  · have hnu : ¬ IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).not.mpr hc
    have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ hnu
    simp [hc, hz]

/-- Non-coprime density term:
`D_q(m) = Σ_{n ≤ m, (n,q) > 1} |vaughanFirst(n,u)|`. -/
noncomputable def panTypeI_nonCoprimeDensity (q m u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), if (n.gcd q) ≠ 1 then |vaughanFirst n u| else 0

/-- The non-coprime density term is nonnegative. -/
lemma panTypeI_nonCoprimeDensity_nonneg (q m u : ℕ) : 0 ≤ panTypeI_nonCoprimeDensity q m u := by
  unfold panTypeI_nonCoprimeDensity
  exact Finset.sum_nonneg (fun n hn => by
    by_cases hc : (n.gcd q) ≠ 1 <;> simp [hc, abs_nonneg])

/-- **Pointwise S2 bound**:
`‖V_χ(m)‖ ≤ ‖V_{χ.primitiveCharacter}(m)‖ + D_q(m)`. -/
lemma panTypeIV1CharSum_norm_le_primitive {q m u : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖panTypeIV1CharSum q m u χ‖ ≤
      ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ +
        panTypeI_nonCoprimeDensity q m u := by
  let ψ := χ.primitiveCharacter
  let S_not : ℂ :=
    ∑ n ∈ Finset.range (m + 1),
      if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor) else 0
  have hdiff : panTypeIV1CharSum q m u χ - panTypeIV1CharSum χ.conductor m u ψ = -S_not := by
    unfold panTypeIV1CharSum S_not ψ
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime q
    · simp [hc, dirichletChar_eq_primitiveCharacter_of_coprime χ hc]
    · have hnu : ¬ IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).not.mpr hc
      have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ hnu
      simp [hc, hz]
  have hnorm1 : ‖panTypeIV1CharSum q m u χ‖ ≤
      ‖panTypeIV1CharSum χ.conductor m u ψ‖ + ‖S_not‖ := by
    simpa only [hdiff, norm_neg] using
      (norm_le_norm_add_norm_sub'
        (panTypeIV1CharSum q m u χ)
        (panTypeIV1CharSum χ.conductor m u ψ))
  have hnorm2 : ‖S_not‖ ≤ panTypeI_nonCoprimeDensity q m u := by
    calc
      ‖S_not‖
          ≤ ∑ n ∈ Finset.range (m + 1),
              ‖(if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor) else 0)‖ := by
              simpa [S_not] using
                (norm_sum_le (s := Finset.range (m + 1))
                  (f := fun n =>
                    (if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)
                     else 0)))
      _ = ∑ n ∈ Finset.range (m + 1),
              (if ¬ n.Coprime q then ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖ else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              by_cases hc : n.Coprime q <;> simp [hc]
      _ ≤ ∑ n ∈ Finset.range (m + 1), (if ¬ n.Coprime q then |vaughanFirst n u| else 0) := by
              apply Finset.sum_le_sum
              intro n hn
              by_cases hc : n.Coprime q
              · simp [hc]
              · have hle : ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖ ≤ |vaughanFirst n u| := by
                  calc
                    ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖
                        ≤ ‖(vaughanFirst n u : ℂ)‖ * ‖ψ (n : ZMod χ.conductor)‖ := norm_mul_le _ _
                    _ = |vaughanFirst n u| * ‖ψ (n : ZMod χ.conductor)‖ := by
                          congr 1
                          exact RCLike.norm_ofReal (vaughanFirst n u)
                    _ ≤ |vaughanFirst n u| * 1 := by
                          exact mul_le_mul_of_nonneg_left
                            (dirichletChar_norm_le_one χ.conductor ψ (n : ZMod χ.conductor))
                            (abs_nonneg _)
                    _ = |vaughanFirst n u| := by simp
                simpa [hc] using hle
      _ = panTypeI_nonCoprimeDensity q m u := by
            unfold panTypeI_nonCoprimeDensity
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hc : n.Coprime q <;> simp [hc, Nat.Coprime]
  simpa [ψ] using le_trans hnorm1 (add_le_add_right hnorm2 (‖panTypeIV1CharSum χ.conductor m u ψ‖))

/-! ### S2b: Primitive-character decomposition by termwise bounds and fiber cardinality

This avoids `sum_bij` over a dependent Sigma type and conductor casts. -/

/-- Primitive-character part:
`P_{q'}(m) = Σ_{χ' primitive mod q'} ‖V_χ'(m)‖²`. -/
noncomputable def panTypeIPrimitiveSqSum (q' m u : ℕ) : ℝ :=
  ∑ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q')).filter (fun χ' => χ'.IsPrimitive),
    ‖panTypeIV1CharSum q' m u χ'‖ ^ 2

/-- `P_{q'}(m) ≥ 0`, since it is a sum of squares. -/
lemma panTypeIPrimitiveSqSum_nonneg (q' m u : ℕ) : 0 ≤ panTypeIPrimitiveSqSum q' m u := by
  unfold panTypeIPrimitiveSqSum
  exact Finset.sum_nonneg (fun χ' hχ' => sq_nonneg _)

/-- Place `χ mod q` at the fixed level `q'`: use its primitive character
if `χ.conductor = q'`, and the trivial character otherwise. -/
noncomputable def panTypeI_liftPrimitive (q' q : ℕ) (χ : DirichletCharacter ℂ q) : DirichletCharacter ℂ q' :=
  if h : χ.conductor = q' then (cast (by rw [h]) χ.primitiveCharacter) else 1

/-- At the matching conductor, the lift remains primitive:
`(panTypeI_liftPrimitive q' q χ).IsPrimitive`. -/
lemma panTypeI_liftPrimitive_isPrimitive {q q' : ℕ} (χ : DirichletCharacter ℂ q)
    (h : χ.conductor = q') : (panTypeI_liftPrimitive q' q χ).IsPrimitive := by
  cases h
  simpa [panTypeI_liftPrimitive, IsPrimitive] using (χ.primitiveCharacter_isPrimitive)

/-- There are `φ(q)` characters, using `hasEnoughRootsOfUnity` as in
`panTypeI_charAbsSum_le_cs`. -/
lemma panTypeI_charCard_eq_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- **S2 square bound**: `‖V_χ‖² ≤ 2‖V_{χ.prim}‖² + 2·D_q(m)²`. -/
lemma panTypeIV1CharSum_sq_le_primitive {q m u : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖panTypeIV1CharSum q m u χ‖ ^ 2 ≤
      2 * ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 +
        2 * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
  let V := panTypeIV1CharSum q m u χ
  let W := panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter
  let D := panTypeI_nonCoprimeDensity q m u
  have hnorm : ‖V‖ ≤ ‖W‖ + D := by
    simpa [V, W, D] using (panTypeIV1CharSum_norm_le_primitive (q := q) (m := m) (u := u) χ)
  have hnonneg : 0 ≤ ‖W‖ + D := add_nonneg (norm_nonneg _) (panTypeI_nonCoprimeDensity_nonneg q m u)
  change ‖V‖ ^ 2 ≤ 2 * ‖W‖ ^ 2 + 2 * D ^ 2
  calc
    ‖V‖ ^ 2 ≤ (‖W‖ + D) ^ 2 := (sq_le_sq₀ (norm_nonneg _) hnonneg).2 hnorm
    _ ≤ 2 * ‖W‖ ^ 2 + 2 * D ^ 2 := by
      simpa only [mul_add] using (add_sq_le (a := ‖W‖) (b := D))

/-- Fiber bound at level `q'`: the contribution of characters modulo `q`
with conductor `q'` is at most `φ(q)·P_{q'}(m)`. The fiber has cardinality
at most `φ(q)`, and each term satisfies `‖V_{χ.prim}‖² ≤ P_{q'}(m)`. -/
lemma panTypeI_primitiveFiberSqSum_le {q q' m u : ℕ} (hq : 0 < q) :
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
      ‖panTypeIV1CharSum q' m u (panTypeI_liftPrimitive q' q χ)‖ ^ 2) ≤
    (Nat.totient q : ℝ) * panTypeIPrimitiveSqSum q' m u := by
  let s₁ : Finset (DirichletCharacter ℂ q) :=
    (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q')
  have hterm : ∀ χ ∈ s₁, ‖panTypeIV1CharSum q' m u (panTypeI_liftPrimitive q' q χ)‖ ^ 2 ≤
      panTypeIPrimitiveSqSum q' m u := by
    intro χ hχ
    have hχ' : χ.conductor = q' := (Finset.mem_filter.mp hχ).2
    rw [panTypeIPrimitiveSqSum]
    exact Finset.single_le_sum (fun χ' hχ' => sq_nonneg ‖panTypeIV1CharSum q' m u χ'‖)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, panTypeI_liftPrimitive_isPrimitive χ hχ'⟩)
  have hsize : s₁.card ≤ Nat.totient q := by
    calc
      s₁.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by
            exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
      _ = Nat.totient q := panTypeI_charCard_eq_totient q hq
  calc
    (∑ χ ∈ s₁, ‖panTypeIV1CharSum q' m u (panTypeI_liftPrimitive q' q χ)‖ ^ 2)
        ≤ ∑ χ ∈ s₁, panTypeIPrimitiveSqSum q' m u := by
          exact Finset.sum_le_sum (fun χ hχ => hterm χ hχ)
    _ = (s₁.card : ℝ) * panTypeIPrimitiveSqSum q' m u := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.totient q : ℝ) * panTypeIPrimitiveSqSum q' m u := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (panTypeIPrimitiveSqSum_nonneg q' m u)

/-- **S2b**: primitive-character decomposition of the all-character
square sum, with the coarse coefficient `φ(q)`:
`t_q(m) ≤ 2·Σ_{q' | q} φ(q)·P_{q'}(m) + 2·φ(q)·D_q(m)²`.
A coefficient 1 would require injectivity of the primitive-character map
and conductor-cast handling, including dependent `sum_bij` and `Eq.ndrec`
transport. This theorem supplies the pointwise square bounds and fiber
grouping, but not that sharper coefficient. -/
theorem panTypeI_sqSum_primitiveDecomposition (q m u : ℕ) (hq : 0 < q) :
    panTypeICharSqSum q m u ≤
      2 * (∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIPrimitiveSqSum q' m u) +
        2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hpoint : ∀ χ : DirichletCharacter ℂ q,
      ‖panTypeIV1CharSum q m u χ‖ ^ 2 ≤
        2 * ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 +
          2 * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
    intro χ
    exact panTypeIV1CharSum_sq_le_primitive (q := q) (m := m) (u := u) χ
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := panTypeI_charCard_eq_totient q hq
  have h1 : panTypeICharSqSum q m u ≤
      2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) +
        2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
    unfold panTypeICharSqSum
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2)
          ≤ ∑ χ : DirichletCharacter ℂ q,
              (2 * ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 +
                2 * (panTypeI_nonCoprimeDensity q m u) ^ 2) := by
              exact Finset.sum_le_sum (fun χ hχ => hpoint χ)
      _ = 2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) +
            2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
              rw [Finset.sum_add_distrib]
              rw [← Finset.mul_sum]
              rw [Finset.sum_const, nsmul_eq_mul]
              rw [Finset.card_univ]
              rw [hcard]
              ring
  have h2 : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) ≤
      ∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIPrimitiveSqSum q' m u := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2)
          = ∑ χ : DirichletCharacter ℂ q,
              ∑ q' ∈ q.divisors, (if χ.conductor = q'
                  then ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 else 0) := by
              apply Finset.sum_congr rfl
              intro χ hχ
              have hmem : χ.conductor ∈ q.divisors := by
                exact Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, Nat.ne_of_gt hq⟩
              rw [Finset.sum_ite_eq]
              simp [hmem]
      _ = ∑ q' ∈ q.divisors,
            ∑ χ : DirichletCharacter ℂ q, (if χ.conductor = q'
                then ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ q' ∈ q.divisors,
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
              ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro q' hq'
            rw [← Finset.sum_filter]
      _ ≤ ∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIPrimitiveSqSum q' m u := by
            apply Finset.sum_le_sum
            intro q' hq'
            have hfiber_cast : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
                  ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) =
                (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
                  ‖panTypeIV1CharSum q' m u (panTypeI_liftPrimitive q' q χ)‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro χ hχ
              have hχ' : χ.conductor = q' := (Finset.mem_filter.mp hχ).2
              cases hχ'
              simp [panTypeI_liftPrimitive]
            rw [hfiber_cast]
            exact panTypeI_primitiveFiberSqSum_le (q := q) (q' := q') (m := m) (u := u) hq
  apply h1.trans
  exact add_le_add (mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl

/-! ### S2c: Structural non-coprime density bound -/

/-- **S2c structural bound**: prime divisors cover the non-coprime terms,
`D_q(m) ≤ Σ_{p | q} Σ_{n ≤ m, p | n} |vf(n)|`.
Use `(n,q) > 1 ⟹ ∃ p | q, p | n`, the pointwise bound
`|vf| ≤ Σ_p 1_{p|n}|vf|`, and exchange sums. -/
lemma panTypeI_nonCoprimeDensity_le_primePartition (q m u : ℕ) (hq : 0 < q) :
    panTypeI_nonCoprimeDensity q m u ≤
      ∑ p ∈ q.primeFactors,
        ∑ n ∈ Finset.range (m + 1), if p ∣ n then |vaughanFirst n u| else 0 := by
  unfold panTypeI_nonCoprimeDensity
  have hpoint : ∀ n : ℕ, ¬ n.Coprime q →
      (if ¬ n.Coprime q then |vaughanFirst n u| else 0) ≤
        ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
    intro n hc
    simp [hc]
    have hg : n.gcd q ≠ 1 := by simpa [Nat.Coprime] using hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpn : p ∣ n := dvd_trans hpd (Nat.gcd_dvd_left n q)
    have hpq : p ∣ q := dvd_trans hpd (Nat.gcd_dvd_right n q)
    have hp' : p ∈ q.primeFactors := (Nat.mem_primeFactors.mpr ⟨hp, hpq, Nat.ne_of_gt hq⟩)
    calc
      |vaughanFirst n u| = ∑ p ∈ ({p} : Finset ℕ), (if p ∣ n then |vaughanFirst n u| else 0) := by
            simp [hpn]
      _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
            simpa using Finset.single_le_sum (s := q.primeFactors)
              (f := fun p => if p ∣ n then |vaughanFirst n u| else 0)
              (fun p hp => by
                by_cases hpd : p ∣ n <;> simp [hpd, abs_nonneg]) hp'
  calc
    (∑ n ∈ Finset.range (m + 1), if ¬ n.Coprime q then |vaughanFirst n u| else 0)
        ≤ ∑ n ∈ Finset.range (m + 1),
            ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
            exact Finset.sum_le_sum (fun n hn => by
              by_cases hc : n.Coprime q
              · simp [hc]
                exact Finset.sum_nonneg (fun p hp => by
                  by_cases hpd : p ∣ n <;> simp [hpd, abs_nonneg])
              · exact hpoint n hc)
    _ = ∑ p ∈ q.primeFactors,
          ∑ n ∈ Finset.range (m + 1), (if p ∣ n then |vaughanFirst n u| else 0) := by
          rw [Finset.sum_comm]
/-! ## S3: Propositions recording μ²3^ω weight estimates -/

/-- **S3 estimate family** for weight assembly, with polylogarithmic factors:
(W1) `Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)/q ≤ C·Q·log⁶(Q+2)`,
using `φ(q)/q ≤ 1` and `Σ_{q≤Q} μ²3^ω ≤ C·Q·log³(Q+2)`.
The latter uses the `PanMainTerm` §4 method: subset expansion,
`sum_squarefree_prod_primeFactors_le_prod_one_add`, and Mertens' second theorem.
(W2) The transferred weight
`Σ_{k ≤ Q/q'} μ²(q'k)3^{ω(q'k)}·(q'k)
 ≤ C·(Q²/q')·3^{ω(q')}·log⁶(Q+2)`,
using `q = q'·k`, `μ²(q'k) ≤ μ²(k)`, and
`3^{ω(q'k)} ≤ 3^{ω(q')}·3^{ω(k)}`.
(W3) `Σ_{q≤Q} μ²(q)3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`,
supplied by `panTypeI_totientWeightSum_polylog`.
This definition records the propositions rather than proving W1 or W2. -/
def panTypeI_threeOmegaWeightSums (Q : ℕ) : Prop :=
  (∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        ((Nat.totient q : ℝ) / (q : ℝ))) ≤
      C * (Q : ℝ) * (Real.log (Q + 2)) ^ (6 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ q' : ℕ, 1 ≤ q' →
    (∑ k ∈ Finset.Icc 1 (Q / q'),
      ((μ (q' * k) : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ (q' * k).primeFactors.card *
        (q' * k : ℝ)) ≤
      C * ((Q : ℝ) ^ 2 / (q' : ℝ)) * (3 : ℝ) ^ q'.primeFactors.card *
        (Real.log (Q + 2)) ^ (6 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
      C * (Real.log (Q + 2)) ^ (6 : ℝ))

/-! ## S4: Square-root Cauchy--Schwarz and assembly inputs -/

/-- **S4a, square-root Cauchy--Schwarz algebra**:
`(Σ_i √(a_i·b_i))² ≤ (card s)·Σ_i a_i·b_i` when `a_i·b_i ≥ 0`.
Use `sq_sum_le_card_mul_sum_sq` (Chebyshev) and `Real.sq_sqrt`.
In BD mean-value assembly, take `a_q = w_q·φ(q)/q` and
`b_q = w_q·q·t_q(m)` to obtain
`(Σ_q w_q·√(φ(q)·t_q(m)))² ≤ (card)·Σ_q w_q²·φ(q)·t_q(m)`,
the algebraic content of Cauchy--Schwarz in `q`. -/
theorem csSqrtSum_le_card_mul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ a i * b i) :
    (∑ i ∈ s, Real.sqrt (a i * b i)) ^ 2 ≤ (s.card : ℝ) * (∑ i ∈ s, a i * b i) := by
  calc
    (∑ i ∈ s, Real.sqrt (a i * b i)) ^ 2
        ≤ (s.card : ℝ) * (∑ i ∈ s, (Real.sqrt (a i * b i)) ^ 2) := by
          simpa using (sq_sum_le_card_mul_sum_sq (s := s)
            (f := fun i => Real.sqrt (a i * b i)))
    _ = (s.card : ℝ) * (∑ i ∈ s, a i * b i) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (h i hi))

/-- **S4b input proposition**: an all-character weighted BD-shaped estimate,
`Σ_{1≤q≤Q} μ²(q)3^{ω(q)}·(q/φ(q))·t_q(m)
 ≤ C·(m+Q²)·S(m)·log⁶(Q+2)`.
The proposed route is (i) decompose `t_q(m)` using S2b; (ii) reorder with
`q = q'·k`, transferring `(φ(q)/φ(q'))·(q/φ(q))` to `q/φ(q')`
in a sharper grouping argument; (iii) apply
`bombieriDavenport_vaughanFirst` to `P_{q'}(m)` for `q' ≤ Q`, with
the weaker constant `LSB(m+1, 1/Q²) ~ m + Q²·log Q`
(see `BombieriDavenport.lean`); and (iv) control the non-coprime terms
through S2c. Naive reordering introduces `Q²/q'`, so precise weight
bookkeeping remains necessary. This is a definition, not a uniform
all-character estimate. -/
def panTypeI_allCharSieveMean (Q m u : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.Icc 1 Q,
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        ((q : ℝ) / (Nat.totient q : ℝ)) * panTypeICharSqSum q m u) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) *
        (Real.log (Q + 2)) ^ (6 : ℝ)

/-- **Proposed support-sensitive T1' input**: the classical Type I
mean-value theorem (Liu 2022 §III Lemma 1; HR 1974 Ch. 10) requires
support conditions on `f`. Chen weights satisfy `f(1) = 0` and admit
control of `Σ_{a≤X} |f(a)|/a`. The version of
`panTypeICharMeanSieveBound` uniform over `|f| ≤ 1` alone is false,
as explained in the module overview. This definition makes candidate
support conditions explicit; the precise hypotheses still require
comparison with the classical sources. -/
def panTypeI_charMeanSieveBound_chenWeight (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧ (f 1 = 0) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ X : ℕ,
      (∑ a ∈ Finset.Icc 1 X, |f a| / (a : ℝ)) ≤ C₀ * (Real.log (X + 2)) ^ (2 : ℝ)) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (Real.log (x X)) ^ A