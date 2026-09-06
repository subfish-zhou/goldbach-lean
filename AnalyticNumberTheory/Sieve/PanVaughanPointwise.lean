import AnalyticNumberTheory.Sieve.PanAssembly

/-! # AnalyticNumberTheory.Sieve.PanVaughanPointwise

## Pointwise Vaughan decomposition and analytic main-term interfaces

This module contains the finite algebra connecting
`PanAssembly.PanVaughanPointwiseSplit` to the pointwise
proposition `PanChebyshevApprox`. That proposition is an
assumption in the reduction, not a universally valid estimate;
the counterexamples and corrected signed block below explain
the necessary qualifications.

The finite steps are:
1. An all-`n` Vaughan identity, extending the `v < n` form by
   the correction `−(if n ≤ v then Λ n else 0)`.
2. AP sums `apMiddle` and `apSmall`.
3. The exact identity
   `apVonMangoldt y q l
    = apV1 y q l u − apMiddle y q l u v + apV3 y q l u v + apSmall y q l v`
   and its triangle bound
   `|apVonMangoldt| ≤ |apV1| + |apV3| + |apMiddle| + |apSmall|`.
4. The same decomposition after coprime scaling by `a`
   (`panWeightedVonMangoldt_abs_le`), retaining the signed
   middle/small block under one absolute value.
5. The pointwise proposition `PanChebyshevApprox`, with the
   AP Chebyshev/main-term comparison as its analytic content.
6. The finite max-composition implication
   `PanChebyshevApprox → PanVaughanPointwiseSplit`.

The exact prime-count identity is
`π(y;q,l) = Σ_{n≤y,n≡l(q)} Λ(n)/log n − primePowerCorrection`.
`apLogVonMangoldt`, `apPrimePowerCorrection`, and
`apLogVonMangoldt_eq_primesInAP_add_pp` implement this identity;
the correction is nonnegative. The prime evaluation
`vonMangoldt_eq_log_of_prime` reuses mathlib's
`ArithmeticFunction.vonMangoldt_apply_prime`.

The log-weighted Vaughan decomposition yields
`panDistributionSum_eq_mainStep`, under `f 0 = 0`, and the
conditional reduction `PanChebyshevApprox.of_mainStep`.
Neither the unrestricted original `PanChebyshevApprox`
nor the universally quantified pure-li `PanChebyshevMainStep`
is valid: explicit counterexamples are proved below.
The corrected shape retains middle/small and `li` in a single
signed block and keeps the prime-power correction explicit.

These identities do not prove the necessary uniform analytic
main-term comparison. The classical route uses AP distribution,
partial summation, suitable weight/support bounds, and the
large sieve; the genuine logarithmic integral must also be
distinguished from the `x/log x` proxy defined in
`PrimeNumberTheorem`. See Pan 1963, Halberstam--Richert 1974
Ch. 10, and Liu 2022 §II--III.

In `PanAssembly`, `PanVaughanPointwiseSplitSigned` and
`PanSignedMainTermBound` feed
`PanMeanValueUniform.of_signedAnalyticInputs`.
The pure-li split feeds only `PanVaughanSplitCrude`.
Even a small Moebius tail `Σ_{d>u} μ(d)/d` does not turn a
positive pure-li block into a logarithmic saving: the schematic
aggregate `(x/log x)·(1+log X)·log³Q` is too large.
The classical signed comparison has the shape
`|Σ f(a)·((apSmall−apMiddle)/log(y/a)−li(y/a)/φ(q))|`,
with the log-normalized identity treated exactly below.
Coprimality, harmonic-sum control for the Chen weights, and
subtraction of the sieve main term remain essential. See
`PanMainTermSieveBound`, `PanMainSieveAbsorption`, and
`PAN_PROOF_ATLAS.md`; the pure-li route establishes only
the separate coarse polylogarithmic bound.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000

noncomputable section

/-! ## 1. The Vaughan identity for all n -/

/-- **All-n Vaughan identity**: for any `n u v : ℕ`,
`Λ n = vaughanFirst n u − vaughanMiddle n u v + vaughanThird n u v
       + (if n ≤ v then Λ n else 0)`.
The existing `vaughanIdentity_threeTerm` covers `v < n`;
`vaughanFullSecondSum` identifies the small-range correction,
which combines with `vaughanIdentity` to give the all-n form.
This form can be summed over APs without imposing `v < n`. -/
theorem vaughanIdentity_threeTerm_general (n u v : ℕ) :
    vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v =
      if v < n then Λ n else 0 := by
  have hsplit : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) =
      (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => d ≤ u),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => u < d)]
    have hfil : n.divisors.filter (fun d => ¬ u < d) = n.divisors.filter (fun d => d ≤ u) := by
      ext d
      simp [not_lt]
    rw [hfil]
  have hsecond : vaughanSecond n u v =
      (if n ≤ v then Λ n else 0) - vaughanMiddle n u v := by
    unfold vaughanSecond vaughanMiddle
    have hfull : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = if n ≤ v then Λ n else 0 :=
      vaughanFullSecondSum n v
    have hAB : (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => d ≤ u),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) =
        if n ≤ v then Λ n else 0 := by
      rw [← hsplit]
      exact hfull
    linarith
  have hmain : vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v =
      Λ n - (if n ≤ v then Λ n else 0) := by
    have h1 := vaughanIdentity n u v
    linarith
  rw [hmain]
  by_cases hv : v < n
  · have hnle : ¬ n ≤ v := Nat.not_le_of_gt hv
    simp [hv, hnle]
  · have hnle : n ≤ v := Nat.not_lt.mp hv
    simp [hv, hnle]

/-! ## 2. AP middle and small terms -/

/-- AP sum of the Type I' middle term:
`Σ_{n≤y, n≡l [MOD q]} vaughanMiddle n u v`.
This counts the contribution from `a ≤ u` and `b ≤ v`
in Vaughan's identity. -/
noncomputable def apMiddle (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanMiddle n u v else 0

/-- AP sum of the small-factor exception:
`Σ_{n≤y, n≡l [MOD q], n≤v} Λ n`.
It occurs because the uncorrected Vaughan identity assumes `v < n`. -/
noncomputable def apSmall (y q l v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0

/-! ## 3. Finite Vaughan decomposition of apVonMangoldt -/

/-- **Exact AP Vaughan decomposition**:
`apVonMangoldt y q l
 = apV1 y q l u − apMiddle y q l u v + apV3 y q l u v + apSmall y q l v`
for arbitrary `y q l u v`. -/
theorem apVonMangoldt_eq_pieces (y q l u v : ℕ) :
    apVonMangoldt y q l =
      apV1 y q l u - apMiddle y q l u v + apV3 y q l u v + apSmall y q l v := by
  have hterm : ∀ n : ℕ,
      (if n ≡ l [MOD q] then Λ n else 0) =
        (if n ≡ l [MOD q] then vaughanFirst n u else 0) -
          (if n ≡ l [MOD q] then vaughanMiddle n u v else 0) +
          (if n ≡ l [MOD q] then vaughanThird n u v else 0) +
          (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0) := by
    intro n
    by_cases hmod : n ≡ l [MOD q]
    · simp [hmod]
      rw [vaughanIdentity_threeTerm_general n u v]
      by_cases hv : v < n
      · have hnle : ¬ n ≤ v := Nat.not_le_of_gt hv
        simp [hv, hnle]
      · have hnle : n ≤ v := Nat.not_lt.mp hv
        simp [hv, hnle]
    · simp [hmod]
  calc
    apVonMangoldt y q l
        = ∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then Λ n else 0) := rfl
    _ = ∑ n ∈ Finset.range (y + 1),
            ((if n ≡ l [MOD q] then vaughanFirst n u else 0) -
              (if n ≡ l [MOD q] then vaughanMiddle n u v else 0) +
              (if n ≡ l [MOD q] then vaughanThird n u v else 0) +
              (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0)) := by
          exact Finset.sum_congr rfl (fun n hn => hterm n)
    _ = (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanFirst n u else 0)) -
          (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanMiddle n u v else 0)) +
          (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanThird n u v else 0)) +
          (∑ n ∈ Finset.range (y + 1),
            (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = apV1 y q l u - apMiddle y q l u v + apV3 y q l u v + apSmall y q l v := rfl

/-- **Triangle bound for the AP decomposition**:
`|apVonMangoldt y q l| ≤ |apV1 y q l u| + |apV3 y q l u v|
                        + |apMiddle y q l u v| + |apSmall y q l v|`.
In the weighted refinement, the middle/small difference is
kept together for comparison with the main term. -/
theorem apVonMangoldt_abs_le_pieces (y q l u v : ℕ) :
    |apVonMangoldt y q l| ≤
      |apV1 y q l u| + |apV3 y q l u v| + |apMiddle y q l u v| + |apSmall y q l v| := by
  rw [apVonMangoldt_eq_pieces]
  have h1 : |apV1 y q l u - apMiddle y q l u v| ≤ |apV1 y q l u| + |apMiddle y q l u v| := by
    have h := abs_add_le (apV1 y q l u) (-apMiddle y q l u v)
    simpa [sub_eq_add_neg, abs_neg] using h
  have h2 : |(apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v| ≤
      |apV1 y q l u - apMiddle y q l u v| + |apV3 y q l u v| := by
    exact abs_add_le (apV1 y q l u - apMiddle y q l u v) (apV3 y q l u v)
  have h3 : |((apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v) + apSmall y q l v| ≤
      |(apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v| + |apSmall y q l v| := by
    exact abs_add_le ((apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v) (apSmall y q l v)
  linarith

/-! ## 4. Weighted triangle decomposition after absorbing a -/

/-- Triangle bound for three finite sums:
`|Σ (A+(B+C))| ≤ |Σ A| + (|Σ B|+|Σ C|)`. -/
private lemma abs_sum_add_add_le (s : Finset ℕ) (A B C : ℕ → ℝ) :
    |∑ a ∈ s, (A a + (B a + C a))| ≤ |∑ a ∈ s, A a| + (|∑ a ∈ s, B a| + |∑ a ∈ s, C a|) := by
  calc
    |∑ a ∈ s, (A a + (B a + C a))| ≤ |∑ a ∈ s, A a| + |∑ a ∈ s, (B a + C a)| := by
      rw [Finset.sum_add_distrib]
      exact abs_add_le (∑ a ∈ s, A a) (∑ a ∈ s, (B a + C a))
    _ ≤ |∑ a ∈ s, A a| + (|∑ a ∈ s, B a| + |∑ a ∈ s, C a|) := by
      have hBC : |∑ a ∈ s, (B a + C a)| ≤ |∑ a ∈ s, B a| + |∑ a ∈ s, C a| := by
        rw [Finset.sum_add_distrib]
        exact abs_add_le (∑ a ∈ s, B a) (∑ a ∈ s, C a)
      linarith

/-- **Weighted Vaughan decomposition after absorbing a**:
the coprime scaled AP sum satisfies
`|Σ f(a)·apVonMangoldt(y/a,q,l·a⁻¹)|
 ≤ |Σ f(a)·apV1(y/a,q,l·a⁻¹)|
 + |Σ f(a)·apV3(y/a,q,l·a⁻¹)|
 + |Σ f(a)·(−apMiddle+apSmall)(y/a,q,l·a⁻¹)|`.
This is the finite algebra underlying the analytic
Chebyshev/main-term comparison. -/
theorem panWeightedVonMangoldt_abs_le (y X q l u v : ℕ) (f : ℕ → ℝ) :
    |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0| ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
          apMiddle (y / a) q (natInvMod q a * l % q) u v) else 0| := by
  have hterm : ∀ a ∈ Finset.Icc 1 X,
      (if a.Coprime q then f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0) =
        (if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0) +
          ((if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0) +
            (if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0)) := by
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      rw [apVonMangoldt_eq_pieces]
      ring_nf
    · simp [hcop]
  calc
    |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0|
        = |∑ a ∈ Finset.Icc 1 X,
            ((if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0) +
              ((if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0) +
                (if a.Coprime q then
                    f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                      apMiddle (y / a) q (natInvMod q a * l % q) u v)
                  else 0)))| := by
          congr 1
          exact Finset.sum_congr rfl (fun a ha => hterm a ha)
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
          (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
            |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0|) := by
          exact abs_sum_add_add_le (Finset.Icc 1 X)
            (fun a => if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0)
            (fun a => if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0)
            (fun a => if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0)
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
              apMiddle (y / a) q (natInvMod q a * l % q) u v)
            else 0| := by
          linarith

/-! ## 5. Pointwise comparison proposition PanChebyshevApprox -/

/-- **Pointwise Chebyshev/main-term comparison proposition**:
for all `X,q,y,l` with `q > 0` and `(l,q)=1`,
`|panDistributionSum y X q l f|
 ≤ |panPieceSum (fun y q l => apV1 y q l u / log y)|
   + |panPieceSum (fun y q l => apV3 y q l u v / log y)|
   + |panPieceSum (fun y q l => li y / φ(q))|`,
with the common outer parameters suppressed.

The intended comparison starts from the AP Chebyshev relation
`π(y;q,l)·log y ≈ Σ_{n≤y,n≡l(q)} Λ(n)` and Vaughan's Type I,
Type II, and middle/small decomposition (Liu 2022 §III
Theorem 2; Halberstam--Richert 1974 Ch. 10).
The zero-index term, relevant only at `q=1`, and real-versus-
natural quotient rounding also have to be handled.
Here `li` is the working `x/log x` proxy.

This proposition is only an assumption in the coarse reduction.
`not_PanChebyshevApprox_of_f0` disproves its unrestricted form.
Furthermore, the pure-li block cannot supply inverse-log decay:
the outer sum `Σ_{q≤Q} μ²(q)3^{ω(q)}/φ(q)` grows
polylogarithmically, while positive choices such as `f=1`
leave the inner main term of the indicated
`y·log X/(φ(q)log y)` size in suitable ranges.
An arbitrary signed sum cannot be lower-bounded by its absolute
majorant; the positive example is enough to exhibit the
obstruction. See `PanMainTerm` and the corrected block in
`PanChebyshevApproxCorrected` and
`panDistributionSum_abs_le_logPieces_mainBlock`. -/
def PanChebyshevApprox (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    |panDistributionSum y X q l f| ≤
      |panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)|

/-! ## 6. Finite composition of the residue and truncation maxima -/

/-- **Residue-max reduction**: a pointwise `(y,l)` estimate gives
`panMaxL ≤` the sum of the three `panPieceMaxL` bounds.
All maxima are finite and use `unitResidues q`, with zero
for an empty residue set. -/
theorem panMaxL_le_pieces_sum (y X q : ℕ) (f : ℕ → ℝ) (g1 g2 g3 : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ l : ℕ, l.Coprime q →
      |panDistributionSum y X q l f| ≤
        |panPieceSum y X q l f g1| + |panPieceSum y X q l f g2| + |panPieceSum y X q l f g3|) :
    panMaxL y X q f ≤
      panPieceMaxL y X q f g1 + panPieceMaxL y X q f g2 + panPieceMaxL y X q f g3 := by
  unfold panMaxL panPieceMaxL
  dsimp only []
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlcop : l.Coprime q := (Finset.mem_filter.mp hl).2
    have hineq := h l hlcop
    have h1 : |panPieceSum y X q l f g1| ≤
        ((unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g1|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := (unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g1|))
        (x := |panPieceSum y X q l f g1|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h2 : |panPieceSum y X q l f g2| ≤
        ((unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g2|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := (unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g2|))
        (x := |panPieceSum y X q l f g2|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h3 : |panPieceSum y X q l f g3| ≤
        ((unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g3|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := (unitResidues q).image
          (fun l : ℕ => |panPieceSum y X q l f g3|))
        (x := |panPieceSum y X q l f g3|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    exact hineq.trans (add_le_add (add_le_add h1 h2) h3)
  · simp [dif_neg hS]

/-- **Truncation-max reduction**: a pointwise `(y,l)` estimate
gives `panMaxY ≤` the sum of the three `panPieceMaxY` bounds
by finite max composition. -/
theorem panMaxY_le_pieces_sum (X q x : ℕ) (f : ℕ → ℝ) (g1 g2 g3 : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ y' : ℕ, ∀ l : ℕ, l.Coprime q →
      |panDistributionSum y' X q l f| ≤
        |panPieceSum y' X q l f g1| + |panPieceSum y' X q l f g2| + |panPieceSum y' X q l f g3|) :
    panMaxY X q x f ≤
      panPieceMaxY X q x f g1 + panPieceMaxY X q x f g2 + panPieceMaxY X q x f g3 := by
  have hy : ∀ y' ∈ Finset.range (x + 1),
      panMaxL y' X q f ≤
        panPieceMaxL y' X q f g1 + panPieceMaxL y' X q f g2 + panPieceMaxL y' X q f g3 := by
    intro y' hy'
    exact panMaxL_le_pieces_sum y' X q f g1 g2 g3 (h y')
  unfold panMaxY panPieceMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y', hy', rfl⟩
  have h1 : panPieceMaxL y' X q f g1 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g1)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g1))
      (x := panPieceMaxL y' X q f g1)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  have h2 : panPieceMaxL y' X q f g2 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g2)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g2))
      (x := panPieceMaxL y' X q f g2)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  have h3 : panPieceMaxL y' X q f g3 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g3)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g3))
      (x := panPieceMaxL y' X q f g3)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  exact (hy y' hy').trans (add_le_add (add_le_add h1 h2) h3)

/-! ## 7. Reduction to PanVaughanPointwiseSplit -/

/-- The pointwise proposition `PanChebyshevApprox` implies
`PanVaughanPointwiseSplit` by finite max composition.
This conditional reduction does not prove the assumed estimate.
It introduces no extra logarithm-positivity assumption:
the log-normalized pieces are passed unchanged to the finite
maximum lemmas. -/
theorem PanVaughanPointwiseSplit.of_chebyshevApprox {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (h : PanChebyshevApprox f u v) : PanVaughanPointwiseSplit x f u v := by
  intro X q y hq
  exact panMaxY_le_pieces_sum X q y f
    (fun y q l => apV1 y q l u / Real.log (y : ℝ))
    (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
    (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)
    (fun y' l hl => h X q y' l hq hl)

/-! ## 8. Exact AP prime-count identity and the main-step reduction

The exact Chebyshev identity is
`π(y;q,l) = Σ_{n≤y,n≡l(q)} Λ(n)/log n − Σ_{p^k≤y,k≥2,p^k≡l(q)} 1/k`.
Together with Vaughan's identity, it exposes the middle/small
block whose cancellation against the main term is analytic,
not finite algebra.

`PrimeNumberTheorem.logarithmicIntegral` is the proxy `x/log x`,
not the actual logarithmic integral. The identity below does
not use PNT-AP, but an analytic main-term estimate must account
for this distinction and cannot treat the proxy as an exact
prime-count main term with arbitrary logarithmic savings.
-/

/-- Log-normalized AP von Mangoldt sum:
`Σ_{n≤y,n≡l [MOD q]} Λ(n)/log n`.
Primes contribute 1 and powers `p^k`, `k ≥ 2`, contribute `1/k`.
Removing the latter gives `π(y;q,l)`. -/
noncomputable def apLogVonMangoldt (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0

/-- Prime-power correction:
`Σ_{p^k≤y,k≥2,p^k≡l [MOD q]} 1/k`.
The implementation sums over nonprime `n` with von Mangoldt
weight; non-prime-powers contribute zero. -/
noncomputable def apPrimePowerCorrection (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then (if n.Prime then 0 else Λ n / Real.log (n : ℝ)) else 0

/-- For prime `p`, `Λ p = log p`, by mathlib's prime evaluation. -/
lemma vonMangoldt_eq_log_of_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log (p : ℝ) := by
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- The von Mangoldt function is nonnegative. -/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ Λ n := by
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- The real logarithm of a natural number is nonnegative,
including the totalized value at `n = 0`. -/
private lemma nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  exact Real.log_natCast_nonneg n

/-- The prime-power correction is nonnegative. -/
theorem apPrimePowerCorrection_nonneg (y q l : ℕ) : 0 ≤ apPrimePowerCorrection y q l := by
  unfold apPrimePowerCorrection
  refine Finset.sum_nonneg ?_
  intro n hn
  by_cases hmod : n ≡ l [MOD q]
  · simp [hmod]
    by_cases hp : n.Prime
    · simp [hp]
    · simp [hp]
      exact div_nonneg (vonMangoldt_nonneg n) (nat_log_nonneg n)
  · simp [hmod]

/-- The absolute weighted prime-power sum is bounded by the absolute weights,
since each prime-power correction is nonnegative. -/
private lemma abs_weighted_primePowerCorrection_le (y X q l : ℕ) (f : ℕ → ℝ) :
    |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| ≤
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop, abs_mul,
      abs_of_nonneg (apPrimePowerCorrection_nonneg _ _ _), le_refl]
  · simp [hcop]

/-- **Exact AP Chebyshev identity**:
`primesInAP y q l
 = apLogVonMangoldt y q l − apPrimePowerCorrection y q l`.
This is finite algebra and counting, with no analytic input. -/
theorem apLogVonMangoldt_eq_primesInAP_add_pp (y q l : ℕ) :
    apLogVonMangoldt y q l = (primesInAP y q l : ℝ) + apPrimePowerCorrection y q l := by
  have hprimes : (primesInAP y q l : ℝ) =
      ∑ n ∈ Finset.range (y + 1), if (n.Prime ∧ n ≡ l [MOD q]) then (1 : ℝ) else 0 := by
    unfold primesInAP
    calc
      ((((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card : ℕ) : ℝ)
          = ∑ x ∈ (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q]), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ Finset.range (y + 1), if (n.Prime ∧ n ≡ l [MOD q]) then (1 : ℝ) else 0 := by
            rw [Finset.sum_filter]
  rw [hprimes]
  unfold apPrimePowerCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmod : n ≡ l [MOD q]
  · simp [hmod]
    by_cases hp : n.Prime
    · have hΛ : Λ n = Real.log (n : ℝ) := vonMangoldt_eq_log_of_prime hp
      have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (Nat.Prime.one_lt hp))).ne'
      rw [hΛ]
      rw [div_self hlog]
      simp [hp]
    · simp [hp]
  · simp [hmod]

/-- **Chebyshev identity after absorbing a**:
if `(a,q)=1` and `a ≥ 1`,
`primesInAPBelow y a q l
 = apLogVonMangoldt(y/a,q,l·a⁻¹)
   − apPrimePowerCorrection(y/a,q,l·a⁻¹)`. -/
theorem apLogVonMangoldt_eq_primesInAPBelow_inv (y a q l : ℕ) (ha : 0 < a) (hcop : a.Coprime q) :
    apLogVonMangoldt (y / a) q (natInvMod q a * l % q) =
      (primesInAPBelow y a q l : ℝ) +
        apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) := by
  rw [apLogVonMangoldt_eq_primesInAP_add_pp (y / a) q (natInvMod q a * l % q)]
  congr 1
  rw [primesInAPBelow_eq_primesInAP_inv y a q l ha hcop]

/-- Log-weighted form of the Type I piece. -/
noncomputable def apV1Log (y q l u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0

/-- Log-weighted form of the Type II (V3) piece. -/
noncomputable def apV3Log (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0

/-- Log-weighted form of the Type I' middle term. -/
noncomputable def apMiddleLog (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0

/-- Log-weighted form of the small-factor exception. -/
noncomputable def apSmallLog (y q l v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1),
    if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0

/-- **Log-weighted Vaughan decomposition**:
`apLogVonMangoldt = apV1Log − apMiddleLog + apV3Log + apSmallLog`.
This follows by dividing the pointwise identity by `log n`
and summing. -/
theorem apLogVonMangoldt_eq_logPieces (y q l u v : ℕ) :
    apLogVonMangoldt y q l =
      apV1Log y q l u - apMiddleLog y q l u v + apV3Log y q l u v + apSmallLog y q l v := by
  have hterm : ∀ n : ℕ, (if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0) =
      (if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0) -
        (if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0) +
        (if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0) +
        (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0) := by
    intro n
    by_cases hmod : n ≡ l [MOD q]
    · simp [hmod]
      have hsub : Λ n = vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v +
          (if n ≤ v then Λ n else 0) := by
        have h1 := vaughanIdentity_threeTerm_general n u v
        by_cases hv : v < n
        · rw [if_pos hv] at h1
          have hsmall : (if n ≤ v then Λ n else 0) = 0 := by
            have : ¬ n ≤ v := Nat.not_le_of_gt hv
            simp [this]
          rw [hsmall]
          linarith
        · rw [if_neg hv] at h1
          have hsmall : (if n ≤ v then Λ n else 0) = Λ n := by
            have : n ≤ v := Nat.not_lt.mp hv
            simp [this]
          rw [hsmall]
          linarith
      calc
        Λ n / Real.log (n : ℝ) =
            (vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v +
              (if n ≤ v then Λ n else 0)) / Real.log (n : ℝ) := by
          conv_lhs => rw [hsub]
        _ = vaughanFirst n u / Real.log (n : ℝ) - vaughanMiddle n u v / Real.log (n : ℝ) +
              vaughanThird n u v / Real.log (n : ℝ) +
              (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) := by
          ring
    · simp [hmod]
  calc
    apLogVonMangoldt y q l
        = ∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0) := rfl
    _ = ∑ n ∈ Finset.range (y + 1),
            ((if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0) -
              (if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0) +
              (if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0) +
              (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0)) := by
          exact Finset.sum_congr rfl (fun n hn => hterm n)
    _ = apV1Log y q l u - apMiddleLog y q l u v + apV3Log y q l u v + apSmallLog y q l v := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rfl

/-- **Triangle reduction**:
`|panDistributionSum| ≤ |prime-count sum| + |li main-term sum|`.
This is the coarse separation used in the original comparison;
it does not supply the signed main-term cancellation. -/
theorem panDistributionSum_abs_le_primes_li (y X q l : ℕ) (f : ℕ → ℝ) :
    |panDistributionSum y X q l f| ≤
      |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (primesInAPBelow y a q l : ℝ) else 0| +
        |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| := by
  unfold panDistributionSum panDistributionError
  have hsplit : (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * ((primesInAPBelow y a q l : ℝ) - logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) =
      (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (primesInAPBelow y a q l : ℝ) else 0) -
        (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · rw [if_pos hcop, if_pos hcop, if_pos hcop]
      ring
    · rw [if_neg hcop, if_neg hcop, if_neg hcop]
      ring
  rw [hsplit]
  exact abs_sub _ _

/-! ## Exact main-step identity and its conditional reduction -/

/-- **Exact main-step identity**: if `f 0 = 0`, then
`panDistributionSum` is
`Σ_{(a,q)=1} f(a)·(V1Log − MiddleLog + V3Log + SmallLog
                   − PrimePowerCorrection − li((y:ℝ)/a)/φ(q))`.
This is finite algebra via the scaled Chebyshev identity.
The condition `f 0 = 0` removes the zero-index exception:
`primesInAPBelow y 0 q l` need not agree with the AP expression
at `y/0 = 0`, which cannot represent its prime count. -/
theorem panDistributionSum_eq_mainStep (y X q l : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    panDistributionSum y X q l f =
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
        f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
      else 0 := by
  rw [panDistributionSum_eq_weighted]
  have h0 : (if (0 : ℕ).Coprime q then f 0 * panDistributionError y 0 q l else 0) = 0 := by
    simp [hf0]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hπ : (primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) =
        apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) := by
      have h1 := apLogVonMangoldt_eq_primesInAPBelow_inv y a q l (by omega) hcop
      rw [primesInAPBelow_eq_primesInAP_inv y a q l (by omega) hcop] at h1
      linarith
    rw [hπ]
    ring
  · simp only [if_neg hcop]

/-- **Pure-li main-step proposition**:
for `q > 0` and `(l,q)=1`,
`|Σ f·(Λlog−li_ℝ/φ)| + Σ |f|·PPC
 ≤ |panPieceSum(V1/log)| + |panPieceSum(V3/log)| + |panPieceSum(li_ℤ/φ)|`,
where the sums run over `1 ≤ a ≤ X`, `(a,q)=1`,
`Λlog = apLogVonMangoldt(y/a,q,a⁻¹l)`, and the pieces
divide by `log(y/a)`, not by a fixed `log u`.
For given `f,u,v`, this can be assumed to obtain a conditional
reduction. It is not valid for all `f,u,v`:
`not_PanChebyshevMainStep` supplies a counterexample.
The intended comparison treats the middle/small terms,
prime powers, and the real/natural `li` rounding difference
using Moebius inversion and PNT-level estimates (Liu 2022 §III
Theorem 2; Halberstam--Richert 1974 Ch. 10).
The finite decomposition does not establish those comparisons
or validate this pure-li right side. -/
def PanChebyshevMainStep (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) ≤
      |panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)|

/-- **Conditional reduction to PanChebyshevApprox**:
`PanChebyshevMainStep` and `f 0 = 0` imply
`PanChebyshevApprox`, by `panDistributionSum_eq_mainStep`.
No analytic estimate is proved by this substitution. -/
theorem PanChebyshevApprox.of_mainStep {f : ℕ → ℝ} {u v : ℕ} (hf0 : f 0 = 0)
    (hms : PanChebyshevMainStep f u v) : PanChebyshevApprox f u v := by
  intro X q y l hq hlcop
  let A : ℝ := panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let B : ℝ := panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let M : ℝ := panPieceSum y X q l f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)
  calc
    |panDistributionSum y X q l f|
        = |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
            else 0| := by
          rw [panDistributionSum_eq_mainStep y X q l f hf0]
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          have hsplit : (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                  logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
                f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
              else 0) =
              (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
                (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hcop : a.Coprime q
            · simp only [if_pos hcop]
              try ring
            · simp only [if_neg hcop]
              try ring
          rw [hsplit]
          exact abs_sub _ _
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
          exact add_le_add le_rfl (abs_weighted_primePowerCorrection_le y X q l f)
    _ ≤ |A| + |B| + |M| := by
          simpa [A, B, M] using hms X q y l hq hlcop

/-- **Zero-index counterexample to unrestricted PanChebyshevApprox**:
take `f = 1_{a=0}`, `X=1`, `q=1`, `y=2`, `l=0`.
The left side is 1, since `primesInAPBelow 2 0 1 0 = 1`
(only the prime 2 is counted), whereas the right side is 0.
At `a=0`, each piece uses the natural quotient `y/a = 0`,
so the Type I, Type II, and pure-li pieces vanish.
Thus the scaled identity requires a condition such as `f 0 = 0`. -/
theorem not_PanChebyshevApprox_of_f0 :
    ¬ PanChebyshevApprox (fun a : ℕ => if a = 0 then 1 else 0) 0 0 := by
  intro h
  have hinst := h 1 1 2 0 (by norm_num) (by rw [Nat.coprime_zero_left])
  have hP : ∀ g : ℕ → ℕ → ℕ → ℝ,
      panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0) g = 0 := by
    intro g
    unfold panPieceSum
    simp
  have hRHS : |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q l => apV1 y q l 0 / Real.log (y : ℝ))| +
      |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q l => apV3 y q l 0 0 / Real.log (y : ℝ))| +
      |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)| = 0 := by
    rw [hP (fun y q l => apV1 y q l 0 / Real.log (y : ℝ)),
        hP (fun y q l => apV3 y q l 0 0 / Real.log (y : ℝ)),
        hP (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)]
    norm_num
  have hsum : panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0) =
      (primesInAPBelow 2 0 1 0 : ℝ) := by
    unfold panDistributionSum panDistributionError
    simp [logarithmicIntegral, Nat.totient_one]
  have hge1 : 1 ≤ |panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)| := by
    rw [hsum]
    have hπ : 1 ≤ (primesInAPBelow 2 0 1 0 : ℝ) := by
      unfold primesInAPBelow
      have hmem : 2 ∈ (Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 0 * p ≤ 2 ∧ 0 * p ≡ 0 [MOD 1]) := by
        rw [Finset.mem_filter]
        norm_num
      have hcard0 : 0 < ((Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 0 * p ≤ 2 ∧ 0 * p ≡ 0 [MOD 1])).card :=
        Finset.card_pos.mpr ⟨2, hmem⟩
      exact_mod_cast (Nat.succ_le_of_lt hcard0)
    exact le_trans hπ (le_abs_self _)
  rw [hRHS] at hinst
  have hnot : ¬ |panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)| ≤ 0 := by
    linarith [hge1]
  exact hnot hinst

/-- **Corrected third block, as an exact structural bound**:
the identities above give
`|panDistributionSum| ≤ |Σ f·V1Log| + |Σ f·V3Log|
  + |Σ f·(MiddleLog−SmallLog+li((y:ℝ)/a)/φ)|
  + Σ |f|·PPC`.
The third block must retain the middle/small terms and `li`
under the same absolute value. A pure `|Σ f·li/φ|`
replacement cannot capture their cancellation. -/
theorem panDistributionSum_abs_le_logPieces_mainBlock (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    |panDistributionSum y X q l f| ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
  have hmain := panDistributionSum_eq_mainStep y X q l f hf0
  have hlog : (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
        f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) =
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0) +
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0) -
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      have hvp := apLogVonMangoldt_eq_logPieces (y / a) q (natInvMod q a * l % q) u v
      rw [hvp]
      ring
    · simp only [if_neg hcop]
      ring
  calc
    |panDistributionSum y X q l f|
        = |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          rw [hmain]
    _ = |(∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0) +
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0) -
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| := by
          rw [hlog]
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          have htri : ∀ x y z w : ℝ, |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
            intro x y z w
            calc
              |x + y - z - w| ≤ |x + y - z| + |w| := abs_sub _ _
              _ ≤ (|x + y| + |z|) + |w| := add_le_add (abs_sub _ _) le_rfl
              _ ≤ |x| + |y| + |z| + |w| :=
                add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
          exact htri _ _ _ _
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
          exact add_le_add le_rfl (abs_weighted_primePowerCorrection_le y X q l f)

/-! ## 9. The corrected signed middle/small and li block

The natural exact third block is
`|Σ f·(MiddleLog−SmallLog+li((y:ℝ)/a)/φ)|`.
The earlier pure-li block
`panPieceSum (fun y' => li(y')/φ(q))` cannot absorb the signed
middle/small terms by itself.
`panDistributionSum_abs_le_logPieces_mainBlock` proves the exact
triangle decomposition. The propositions below distinguish
the subsequent analytic comparisons from that finite result.
-/

/-- **Corrected comparison proposition in panPieceSum form**:
use the third piece
`apMiddleLog y' q l' u v − apSmallLog y' q l' v
 + logarithmicIntegral y'/φ(q)`
and an explicit prime-power correction.
The Type I and Type II pieces here are already `apV1Log`
and `apV3Log`. Relating the exact corrected-block bound to this
form requires `f 0 = 0` and control of the conversion from real
division in `li((y:ℝ)/a)` to the natural quotient in
`panPieceSum`. The classical main-term comparison also uses
`li(x) = x/log x + O(x/log²x)` for the genuine logarithmic
integral; that relation does not identify the proxy with it.
These are additional inputs, not consequences of the definition. -/
def PanChebyshevApproxCorrected (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    |panDistributionSum y X q l f| ≤
      |panPieceSum y X q l f (fun y q l => apV1Log y q l u)| +
      |panPieceSum y X q l f (fun y q l => apV3Log y q l u v)| +
      |panPieceSum y X q l f (fun y q l => apMiddleLog y q l u v - apSmallLog y q l v +
          logarithmicIntegral (y : ℝ) / Nat.totient q)| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0

/-- **Corrected main-term bound T3'**, an analytic-input proposition:
the `3^{ω(q)}`-weighted maximum sum of the combined
`li + middle − small` block is bounded by
`C·x/log^A x`, with constants preceding all sufficiently large
`X`. This replaces the pure-li `PanMainTermBound`.
The intended classical mechanism is the comparison
`ψ(x;q,l)/log x ≈ li(x)/φ(q)`, matching the smooth Vaughan
contributions to `x/φ(q)` and cancelling at the `x/log x`
scale (Halberstam--Richert 1974 Ch. 10; Liu 2022 §III).
The remainder estimate `O(x/log^A x)` is analytic input,
not a conclusion proved by this proposition. -/
def PanMainTermAbsorbedBound (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apMiddleLog y q l u v - apSmallLog y q l v +
              logarithmicIntegral (y : ℝ) / Nat.totient q) ≤
        C * x X / (log (x X)) ^ A

/-! ## 10. Exact main-step decomposition and a counterexample

The results above identify both the exact third block and the
failure caused by allowing `f 0 ≠ 0`. This section also gives
an explicit counterexample to universal `PanChebyshevMainStep`.

### Exact decomposition and analytic limitations

`panDistributionSum_eq_mainStep` gives
`Σ f·(V1Log−MiddleLog+V3Log+SmallLog−PPC−li((y:ℝ)/a)/φ)`.
The main-step left side instead majorizes the prime powers:
`|Σ f·(Λlog−li_ℝ/φ)| + Σ |f|·PPC`.
Finite algebra does not control this by
`|panPieceSum(V1/log)| + |panPieceSum(V3/log)| + |panPieceSum(li_ℤ/φ)|`
for arbitrary `f,u,v`, even with `f 0 = 0`.
Signed weights can cancel the pure-li sum while leaving
the middle/small contribution nonzero.
Separating two large main terms by the triangle inequality also
loses the cancellation needed for logarithmic savings.
The exact prime-count statement is
`panDistributionSum_abs_le_logPieces_mainBlock`;
`panChebyshevMainStepLHS_abs_le_corrected` gives the matching
bound for the main-step left side.

The separate analytic requirements are:
1. **Small term**:
   `SmallLog_a = π(min(y/a,v);q,a⁻¹l) + PPC(min(y/a,v);q,a⁻¹l)`.
   This is the small-range version of
   `apLogVonMangoldt_eq_primesInAP_add_pp`.
   If `v=o(y/a)`, its prime-count main term is expected to be
   small relative to `li(y/a)/φ(q)` in an appropriate AP range.
   If `y/a ≤ v`, it is the whole log-normalized AP sum and
   PNT-AP would compare it with `li(y/a)/φ(q)`.
2. **Middle term and Moebius tails**: the heuristic after
   Moebius inversion has the shape
   `MiddleLog_a ≈ (y/a/φ(q))·Σ_{d≤u}μ(d)/d·(1+o(1))`.
   The PNT-equivalent cancellation `Σ_{d≤u}μ(d)/d → 0`
   and a quantitative tail estimate are relevant. Neither this
   heuristic nor an `o(li)` bound follows from the finite
   identity; uniformity, truncation, and the logarithmic
   normalization have to be justified.
3. **Prime powers**: the proposed estimate
   `PPC(y/a) = O(sqrt(y/a)·log(y/a)) = o(li(y/a))`
   at large arguments concerns prime-power counting.
   Its `Σ |f|·PPC` and modulus aggregates need separate bounds.
4. **Quotient rounding**: the real division in
   `li((y:ℝ)/a)` differs from the natural quotient in
   `panPieceSum`. The proposed real-analysis estimate is
   `|li_ℝ−li_ℤ| ≤ 3/log(y/a)` for the `t/log t` proxy,
   in a suitable range bounded away from the singular point 1.
   The necessary range and small-argument exceptions must be
   stated; the estimate is not an unrestricted identity.

Even an asymptotic main block of size
`li_ℝ/φ(q)·(1+o(1))` is not itself an inverse-log error.
After weighting by the Chen coefficients, subtraction of the
sieve main term and quantitative uniform remainders are needed
to reach the target `PanMainTermAbsorbedBound`.

The remaining counterexample is not just a sign heuristic.
Take `X=2`, `q=1`, `y=4`, `l=0`, `u=4`, `v=0`, and
`f(1)=c`, `f(2)=−c`, with `c=2/log 2` and `f=0` otherwise.
For the proxy `li(t)=t/log t`, `li(4)=li(2)=c`,
so the pure-li piece vanishes. The left side is `2c`, while
the right side is `c·log 3/(2 log 2) < 2c`.
The strict inequality is `log 3 < log 16 = 4 log 2`.
This disproves the universally quantified main-step proposition
despite `f 0 = 0`.
More generally, the cancellation choice
`f(1)=li(⌊y/2⌋)`, `f(2)=−li(⌊y⌋)` at `X=2,q=1`
annuls the pure-li block without annulling `Σ |f|·PPC`.
For `u ≥ y`, `apV1 = apVonMangoldt` and `apV3 = 0`
throughout the relevant sums.

### Requirements for the corrected analytic route

`PanChebyshevApproxCorrected` and `PanMainTermAbsorbedBound`
state comparisons with the combined signed third block.
They separate finite algebra from the analytic estimates;
they are not proofs of those estimates.

1. **PNT-AP or Siegel--Walfisz**: a suitable uniform version of
   `π(x;q,l) = li(x)/φ(q) + O(x/(φ(q)log^A x))` for
   `q ≤ log^B x`, with the genuine logarithmic integral and
   correctly quantified constants. The fixed-parameter theorem
   `BombieriVinogradov.bombieri_vinogradov` is not a genuine
   averaged BV estimate and does not provide this input.
2. **Quantitative Moebius tail**:
   `|Σ_{d≤u} μ(d)/d| = O(1/log u)`, a PNT-level input
   not proved by the finite reductions.
3. **Weighted main-term comparison**:
   `PanMainTermAbsorbedBound`, including the signed main block
   and the weight/support requirements, remains an assumption.
4. **Rounding lemma**: establish the proposed
   `3/log(y/a)` bound under explicit domain hypotheses for
   the proxy, and handle the excluded small arguments separately.

The original universal comparison is therefore not an analytic
input that can simply be filled in. The corrected route must
retain these signed, support, and error requirements.
-/

/-- Small logarithmic constant: `0 < log 2`. -/
private lemma log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- Small logarithmic constant: `0 < log 3`. -/
private lemma log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 3)

/-- Small logarithmic constant: `log 2 ≠ 0`. -/
private lemma log_two_ne_zero : Real.log 2 ≠ 0 := log_two_pos.ne'

/-- Small logarithmic constant: `2·log 2 ≠ 0`. -/
private lemma two_mul_log_two_ne_zero : 2 * Real.log 2 ≠ 0 :=
  mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) log_two_ne_zero

/-- `log 4 = 2·log 2`. -/
private lemma log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- The von Mangoldt arithmetic function vanishes at zero. -/
private lemma vonMangoldt_zero : Λ 0 = 0 := by
  simp only [ArithmeticFunction.map_zero]

/-- `Λ 4 = log 2` (4 = 2², `vonMangoldt_apply_pow`). -/
private lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h := ArithmeticFunction.vonMangoldt_apply_pow (n := 2) (k := 2) (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at h
  rw [h]
  exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime)

/-- If `u ≥ n`, then `vaughanFirst n u = Λ n`,
by Vaughan's identity and the empty remaining terms. -/
private lemma vaughanFirst_eq_vonMangoldt_of_ge {n u : ℕ} (hu : n ≤ u) :
    vaughanFirst n u = Λ n := by
  have h := vaughanIdentity n u 0
  have h2 : vaughanSecond n u 0 = 0 := by
    unfold vaughanSecond
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro e he
    exfalso
    have he' : e ∈ (n / d).divisors := (Finset.mem_filter.mp he).1
    have hmd : 0 < n / d := Nat.pos_of_ne_zero (Nat.mem_divisors.mp he').2
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he').1 hmd
    have hele : e ≤ 0 := (Finset.mem_filter.mp he).2
    omega
  have h3 : vaughanThird n u 0 = 0 := by
    unfold vaughanThird
    by_cases hn : n = 0
    · subst n
      simp [Nat.divisors_zero]
    · apply Finset.sum_eq_zero
      intro d hd
      exfalso
      have hd' : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
      have hdg : u < d := (Finset.mem_filter.mp hd).2
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd').1
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
      omega
  linarith

/-- If `u ≥ n`, then `vaughanThird n u v = 0`,
since its outer filter is empty. -/
private lemma vaughanThird_zero_of_u_ge {n u v : ℕ} (hu : n ≤ u) :
    vaughanThird n u v = 0 := by
  unfold vaughanThird
  by_cases hn : n = 0
  · subst n
    simp [Nat.divisors_zero]
  · apply Finset.sum_eq_zero
    intro d hd
    exfalso
    have hd' : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
    have hdg : u < d := (Finset.mem_filter.mp hd).2
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd').1
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    omega

/-- `li(2) = 2/log 2` for the working definition `li x = x/log x`. -/
private lemma logIntegral_two : logarithmicIntegral (2 : ℝ) = (2 : ℝ) / Real.log 2 := by
  simp [logarithmicIntegral]

/-- `li(4) = 2/log 2 = li(2)`, since `4/log 4 = 2/log 2`. -/
private lemma logIntegral_four : logarithmicIntegral (4 : ℝ) = (2 : ℝ) / Real.log 2 := by
  simp [logarithmicIntegral]
  rw [log_four_eq_two_log_two]
  field_simp [log_two_ne_zero, two_mul_log_two_ne_zero]; ring

/-- `apLogVonMangoldt 2 1 0 = 1`: the prime 2 contributes 1. -/
private lemma apLogVonMangoldt_two : apLogVonMangoldt 2 1 0 = 1 := by
  unfold apLogVonMangoldt
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    log_two_ne_zero]

/-- `apLogVonMangoldt 4 1 0 = 5/2`: the primes 2 and 3
contribute 1 each, and 4 contributes `1/2`. -/
private lemma apLogVonMangoldt_four : apLogVonMangoldt 4 1 0 = (5 : ℝ) / 2 := by
  unfold apLogVonMangoldt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hdiv : Real.log 2 / (2 * Real.log 2) = (1 : ℝ) / 2 := by
    field_simp [log_two_ne_zero, two_mul_log_two_ne_zero]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (3 : ℕ).Prime),
    vonMangoldt_four, log_four_eq_two_log_two, log_two_ne_zero, hdiv]

/-- `apPrimePowerCorrection 2 1 0 = 0`. -/
private lemma apPrimePowerCorrection_two : apPrimePowerCorrection 2 1 0 = 0 := by
  unfold apPrimePowerCorrection
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one, log_two_ne_zero]

/-- `apPrimePowerCorrection 4 1 0 = 1/2`, from `4 = 2²`. -/
private lemma apPrimePowerCorrection_four : apPrimePowerCorrection 4 1 0 = (1 : ℝ) / 2 := by
  unfold apPrimePowerCorrection
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hdiv : Real.log 2 / (2 * Real.log 2) = (1 : ℝ) / 2 := by
    field_simp [log_two_ne_zero, two_mul_log_two_ne_zero]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one, vonMangoldt_four,
    log_four_eq_two_log_two, log_two_ne_zero, hdiv]

/-- `apV1 2 1 0 4 = log 2`, since `u=4 ≥ n`
makes `vaughanFirst = Λ` on the summation range. -/
private lemma apV1_two : apV1 2 1 0 4 = Real.log 2 := by
  unfold apV1
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanFirst 0 4 = Λ 0 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanFirst 1 4 = Λ 1 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanFirst 2 4 = Λ 2 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (2 : ℕ) ≤ 4)
  norm_num [h0, h1, h2, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime)]

/-- `apV1 4 1 0 4 = 2·log 2 + log 3 = ψ(4)`. -/
private lemma apV1_four : apV1 4 1 0 4 = 2 * Real.log 2 + Real.log 3 := by
  unfold apV1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanFirst 0 4 = Λ 0 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanFirst 1 4 = Λ 1 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanFirst 2 4 = Λ 2 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (2 : ℕ) ≤ 4)
  have h3 : vaughanFirst 3 4 = Λ 3 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (3 : ℕ) ≤ 4)
  have h4 : vaughanFirst 4 4 = Λ 4 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (4 : ℕ) ≤ 4)
  norm_num [h0, h1, h2, h3, h4, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (3 : ℕ).Prime),
    vonMangoldt_four]; ring_nf

/-- `apV3 2 1 0 4 0 = 0`, since `u=4 ≥ n`. -/
private lemma apV3_two : apV3 2 1 0 4 0 = 0 := by
  unfold apV3
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanThird 0 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanThird 1 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanThird 2 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (2 : ℕ) ≤ 4)
  simp [h0, h1, h2]

/-- `apV3 4 1 0 4 0 = 0`. -/
private lemma apV3_four : apV3 4 1 0 4 0 = 0 := by
  unfold apV3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanThird 0 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanThird 1 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanThird 2 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (2 : ℕ) ≤ 4)
  have h3 : vaughanThird 3 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (3 : ℕ) ≤ 4)
  have h4 : vaughanThird 4 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (4 : ℕ) ≤ 4)
  simp [h0, h1, h2, h3, h4]

/-- A sum over `Icc 1 2` is a two-term sum. -/
private lemma sum_Icc_1_2 (g : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 2, g a) = g 1 + g 2 := by
  rw [show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) by decide]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- **Exact decomposition of the main-step left side**:
for arbitrary `f,u,v`,
`|Σ f·(Λlog−li_ℝ/φ)| + Σ |f|·PPC
 ≤ |Σ f·V1Log| + |Σ f·V3Log|
   + |Σ f·(MiddleLog−SmallLog+li_ℝ/φ)| + Σ |f|·PPC`.
Substitute `apLogVonMangoldt_eq_logPieces` termwise and apply
the triangle inequality. This finite bound requires no condition
on `f 0`, since the sums here start at 1. It retains the signed
`middle − small + li` block rather than the pure-li piece. -/
theorem panChebyshevMainStepLHS_abs_le_corrected (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
  let A : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0
  let B : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0
  let C : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
        apSmallLog (y / a) q (natInvMod q a * l % q) v +
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0
  let P : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0
  let S : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0
  have hsplit : S = A + B - C := by
    dsimp [S, A, B, C]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      have hvp := apLogVonMangoldt_eq_logPieces (y / a) q (natInvMod q a * l % q) u v
      rw [hvp]
      ring
    · simp only [if_neg hcop]
      ring
  have htri : ∀ x y z : ℝ, |x + y - z| ≤ |x| + |y| + |z| := by
    intro x y z
    have h1 : |x + y - z| ≤ |x + y| + |z| := by
      have h := abs_add_le (x + y) (-z)
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    have h2 : |x + y| ≤ |x| + |y| := abs_add_le x y
    linarith
  calc
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)
        = |S| + P := by
          simp [S, P]
    _ ≤ (|A| + |B| + |C|) + P := by
          have htri' : |A + B - C| ≤ |A| + |B| + |C| := htri A B C
          have hS : |S| = |A + B - C| := by rw [hsplit]
          linarith
    _ = |A| + |B| + |C| + P := by ring

/-- **Counterexample to universal PanChebyshevMainStep**:
let `X=2`, `q=1`, `y=4`, `l=0`, `u=4`, `v=0`, and
`f(1)=2/log 2`, `f(2)=−2/log 2`, with `f=0` otherwise.
Since `li(4)=li(2)`, the pure-li right-hand piece is zero.
The remaining right side is `c·log 3/(2 log 2)`,
while the left side is `|3c/2|+c/2 = 2c`, with `c=2/log 2`.
The strict inequality follows from `log 16 > log 3`.
The necessary third block must retain middle/small and `li`
inside one absolute value
(`panDistributionSum_abs_le_logPieces_mainBlock`). -/
theorem not_PanChebyshevMainStep :
    ¬ PanChebyshevMainStep (fun a : ℕ =>
        if a = 1 then (2 : ℝ) / Real.log 2
        else if a = 2 then -((2 : ℝ) / Real.log 2) else 0) 4 0 := by
  intro h
  let c : ℝ := (2 : ℝ) / Real.log 2
  let f : ℕ → ℝ := fun a => if a = 1 then c else if a = 2 then -c else 0
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (by norm_num) log_two_pos
  have hinst := h 2 1 4 0 (by norm_num) (by rw [Nat.coprime_zero_left])
  change (|∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| +
      ∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) ≤
      |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)| at hinst
  have hS1 : (∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0) =
      c * (3 : ℝ) / 2 := by
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [apLogVonMangoldt_four, apLogVonMangoldt_two, logIntegral_four, logIntegral_two]
    ring_nf
  have hS1abs : |∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| =
      c * (3 : ℝ) / 2 := by
    rw [hS1]
    exact abs_of_pos (div_pos (mul_pos hcpos (by norm_num : (0 : ℝ) < 3)) (by norm_num : (0 : ℝ) < 2))
  have hS2 : (∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) =
      c * (1 : ℝ) / 2 := by
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [apPrimePowerCorrection_four, apPrimePowerCorrection_two]
    simp [abs_of_pos hcpos]; ring_nf
  have hT1 : panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ)) =
      c * Real.log 3 / (2 * Real.log 2) := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apV1 (4 / a) 1 (natInvMod 1 a * 0 % 1) 4 / Real.log ((4 / a : ℕ) : ℝ)) else 0)]
    norm_num [f]
    rw [apV1_four, apV1_two, log_four_eq_two_log_two]
    have hdiv1 : Real.log 2 / Real.log 2 = 1 := div_self log_two_ne_zero
    have hsplit : (2 * Real.log 2 + Real.log 3) / (2 * Real.log 2) =
        1 + Real.log 3 / (2 * Real.log 2) := by
      field_simp [two_mul_log_two_ne_zero]
    rw [hdiv1, hsplit]
    ring
  have hT1pos : 0 < c * Real.log 3 / (2 * Real.log 2) := by
    exact div_pos (mul_pos hcpos log_three_pos) (mul_pos (by norm_num) log_two_pos)
  have hT1abs : |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| =
      c * Real.log 3 / (2 * Real.log 2) := by
    rw [hT1]
    exact abs_of_pos hT1pos
  have hT2 : panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ)) = 0 := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apV3 (4 / a) 1 (natInvMod 1 a * 0 % 1) 4 0 / Real.log ((4 / a : ℕ) : ℝ)) else 0)]
    norm_num [f]
    rw [apV3_four, apV3_two]
    simp
  have hT3 : panPieceSum 4 2 1 0 f
      (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q) = 0 := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (logarithmicIntegral ((4 / a : ℕ) : ℝ) / Nat.totient 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [logIntegral_four, logIntegral_two]
    simp
  have hLHS : (|∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| +
      ∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) = c * 2 := by
    rw [hS1abs, hS2]
    ring_nf
  have hRHS : |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q _ => logarithmicIntegral (y : ℝ) / Nat.totient q)| =
      c * Real.log 3 / (2 * Real.log 2) := by
    rw [hT1abs, hT2, hT3]
    simp
  rw [hLHS, hRHS] at hinst
  have hlt : c * Real.log 3 / (2 * Real.log 2) < c * 2 := by
    have hlog16 : Real.log (16 : ℝ) = (4 : ℝ) * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
      norm_num
    have h34 : Real.log 3 < (4 : ℝ) * Real.log 2 := by
      have hltl := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 16)
      rw [hlog16] at hltl
      exact hltl
    have h2log : 0 < 2 * Real.log 2 := mul_pos (by norm_num) log_two_pos
    have hfrac : Real.log 3 / (2 * Real.log 2) < (2 : ℝ) := by
      have hd := div_lt_div_of_pos_right h34 h2log
      have hcancel : (4 * Real.log 2) / (2 * Real.log 2) = (2 : ℝ) := by
        field_simp [log_two_ne_zero, two_mul_log_two_ne_zero]; ring
      linarith
    calc
      c * Real.log 3 / (2 * Real.log 2) = c * (Real.log 3 / (2 * Real.log 2)) := by ring
      _ < c * 2 := mul_lt_mul_of_pos_left hfrac hcpos
  linarith


end

/-! ## 11. Source-faithful signed kernels

Liu's Theorem 2 (PDF p.2) only sums over `(a,q)=1`.  The main term in
`eqn-m1` and the signed error in `eqn-r` are on PDF p.5; the omitted
non-coprime contribution is the separate `R₁` term in `eqn-r0` on PDF p.6.
Accordingly, the kernels below do not encode coprimality: that restriction is
visible in the surrounding finite sums.

The aggregate kernels used by the existing type I/II estimates are
`apV1 y q l u / log y` and `apV3 y q l u v / log y`.  Vaughan's exact
identity instead produces the termwise-log kernels `apV1Log` and `apV3Log`.
The signed main kernel records this conversion exactly, together with the
middle/small pieces and Liu's real-argument logarithmic integral. -/

/-- The exact signed residual after removing the aggregate type I and type II
kernels.  Coprimality is deliberately not part of this function. -/
noncomputable def panSignedMainKernel
    (y a q l u v : ℕ) : ℝ :=
  let ya := y / a
  let la := natInvMod q a * l % q
  (apV1Log ya q la u - apV1 ya q la u / Real.log (ya : ℝ)) +
    (apV3Log ya q la u v - apV3 ya q la u v / Real.log (ya : ℝ)) -
    apMiddleLog ya q la u v + apSmallLog ya q la v -
    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q

/-- The prime-power correction kernel in the exact `ψ/log` to `π`
conversion.  It is nonnegative and contains no coprimality convention. -/
noncomputable def panSignedCorrectionKernel (y a q l : ℕ) : ℝ :=
  apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)

/-- Signed main residual, with Liu's `(a,q)=1` restriction displayed at the
sum rather than hidden in the kernel. -/
noncomputable def panSignedMainSum
    (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
    f a * panSignedMainKernel y a q l u v else 0

/-- Signed prime-power correction in the exact decomposition. -/
noncomputable def panSignedCorrectionSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
    f a * panSignedCorrectionKernel y a q l else 0

/-- Nonnegative majorant for the signed prime-power correction. -/
noncomputable def panSignedCorrectionBound
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
    |f a| * panSignedCorrectionKernel y a q l else 0

/-- The separate prime-power correction majorant is nonnegative. -/
theorem panSignedCorrectionBound_nonneg
    (y X q l : ℕ) (f : ℕ → ℝ) :
    0 ≤ panSignedCorrectionBound y X q l f := by
  unfold panSignedCorrectionBound
  apply Finset.sum_nonneg
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    exact mul_nonneg (abs_nonneg _) (apPrimePowerCorrection_nonneg _ _ _)
  · simp [hcop]

/-- Exact finite signed decomposition.  This is the strongest statement
available from the existing Vaughan and Chebyshev identities: no analytic
estimate or triangle inequality has yet been used. -/
theorem panDistributionSum_eq_sourceFaithfulSigned
    (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hf0 : f 0 = 0) :
    panDistributionSum y X q l f =
      panPieceSum y X q l f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceSum y X q l f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        panSignedMainSum y X q l f u v -
        panSignedCorrectionSum y X q l f := by
  rw [panDistributionSum_eq_mainStep y X q l f hf0]
  unfold panPieceSum panSignedMainSum panSignedCorrectionSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    rw [apLogVonMangoldt_eq_logPieces]
    simp only [panSignedMainKernel, panSignedCorrectionKernel]
    ring
  · simp [hcop]

/-- The signed prime-power correction is bounded by its separate nonnegative
majorant. -/
theorem abs_panSignedCorrectionSum_le
    (y X q l : ℕ) (f : ℕ → ℝ) :
    |panSignedCorrectionSum y X q l f| ≤
      panSignedCorrectionBound y X q l f := by
  exact abs_weighted_primePowerCorrection_le y X q l f

/-- Pointwise triangle form of the exact signed decomposition. -/
theorem abs_panDistributionSum_le_sourceFaithfulSigned
    (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hf0 : f 0 = 0) :
    |panDistributionSum y X q l f| ≤
      |panPieceSum y X q l f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
        |panPieceSum y X q l f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
        (|panSignedMainSum y X q l f u v| +
          panSignedCorrectionBound y X q l f) := by
  rw [panDistributionSum_eq_sourceFaithfulSigned y X q l f u v hf0]
  have htri : ∀ a b c d : ℝ,
      |a + b + c - d| ≤ |a| + |b| + (|c| + |d|) := by
    intro a b c d
    calc
      |a + b + c - d| ≤ |a + b| + |c - d| := by
        have heq : a + b + c - d = (a + b) + (c - d) := by ring
        rw [heq]
        exact abs_add_le _ _
      _ ≤ (|a| + |b|) + (|c| + |d|) := by
        gcongr
        · exact abs_add_le _ _
        · simpa [sub_eq_add_neg, abs_neg] using abs_add_le c (-d)
      _ = |a| + |b| + (|c| + |d|) := by ring
  have hcorr := abs_panSignedCorrectionSum_le y X q l f
  exact le_trans (htri _ _ _ _) (by linarith)

private noncomputable def panScoreMaxL
    (q : ℕ) (score : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image score).max' (Finset.image_nonempty.mpr h)
  else 0

@[simp] private theorem panScoreMaxL_zero (score : ℕ → ℝ) :
    panScoreMaxL 0 score = 0 := by
  simp [panScoreMaxL]

@[simp] private theorem panScoreMaxL_one (score : ℕ → ℝ) :
    panScoreMaxL 1 score = score 0 := by
  simp [panScoreMaxL]

private noncomputable def panScoreMaxY
    (q x : ℕ) (score : ℕ → ℕ → ℝ) : ℝ :=
  ((Finset.range (x + 1)).image
      (fun y => panScoreMaxL q (score y))).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] private theorem panScoreMaxY_zero
    (x : ℕ) (score : ℕ → ℕ → ℝ) :
    panScoreMaxY 0 x score = 0 := by
  unfold panScoreMaxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · simpa using Finset.le_max'
      ((Finset.range (x + 1)).image
        (fun y => panScoreMaxL 0 (score y)))
      (panScoreMaxL 0 (score 0))
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)

private theorem panScoreMaxY_one
    (x : ℕ) (score : ℕ → ℕ → ℝ) :
    panScoreMaxY 1 x score =
      ((Finset.range (x + 1)).image (fun y => score y 0)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  simp only [panScoreMaxY, panScoreMaxL_one]

private theorem panScoreMaxL_nonneg
    (q : ℕ) (score : ℕ → ℝ) (hscore : ∀ l, 0 ≤ score l) :
    0 ≤ panScoreMaxL q score := by
  unfold panScoreMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    rcases hS with ⟨l, hl⟩
    exact le_trans (hscore l)
      (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  · simp [hS]

private theorem panScoreMaxY_nonneg
    (q x : ℕ) (score : ℕ → ℕ → ℝ)
    (hscore : ∀ y l, 0 ≤ score y l) :
    0 ≤ panScoreMaxY q x score := by
  unfold panScoreMaxY
  have hzero : 0 ∈ Finset.range (x + 1) := by
    rw [Finset.mem_range]
    omega
  exact le_trans (panScoreMaxL_nonneg q (score 0) (hscore 0))
    (Finset.le_max'
      ((Finset.range (x + 1)).image
        (fun y => panScoreMaxL q (score y)))
      (panScoreMaxL q (score 0))
      (Finset.mem_image.mpr ⟨0, hzero, rfl⟩))

/-- The double maximum of the concrete signed main plus its separate
prime-power correction. -/
noncomputable def panSignedResidualMaxY
    (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  panScoreMaxY q x (fun y l =>
    |panSignedMainSum y X q l f u v| +
      panSignedCorrectionBound y X q l f)

@[simp] theorem panSignedResidualMaxY_zero
    (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panSignedResidualMaxY X 0 x f u v = 0 := by
  simp [panSignedResidualMaxY]

theorem panSignedResidualMaxY_one
    (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panSignedResidualMaxY X 1 x f u v =
      ((Finset.range (x + 1)).image (fun y =>
        |panSignedMainSum y X 1 0 f u v| +
          panSignedCorrectionBound y X 1 0 f)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  exact panScoreMaxY_one x _

/-- The concrete residual double maximum is nonnegative. -/
theorem panSignedResidualMaxY_nonneg
    (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ panSignedResidualMaxY X q x f u v := by
  apply panScoreMaxY_nonneg
  intro y l
  exact add_nonneg (abs_nonneg _)
    (panSignedCorrectionBound_nonneg y X q l f)

private theorem panScoreMaxL_le_three
    (q : ℕ) (s t₁ t₂ t₃ : ℕ → ℝ)
    (h : ∀ l, l.Coprime q → s l ≤ t₁ l + t₂ l + t₃ l) :
    panScoreMaxL q s ≤
      panScoreMaxL q t₁ + panScoreMaxL q t₂ + panScoreMaxL q t₃ := by
  unfold panScoreMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hcop : l.Coprime q := (Finset.mem_filter.mp hl).2
    have h₁ := Finset.le_max'
      ((unitResidues q).image t₁)
      (t₁ l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h₂ := Finset.le_max'
      ((unitResidues q).image t₂)
      (t₂ l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h₃ := Finset.le_max'
      ((unitResidues q).image t₃)
      (t₃ l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    linarith [h l hcop]
  · simp [hS]

private theorem panScoreMaxY_le_three
    (q x : ℕ) (s t₁ t₂ t₃ : ℕ → ℕ → ℝ)
    (h : ∀ y l, l.Coprime q →
      s y l ≤ t₁ y l + t₂ y l + t₃ y l) :
    panScoreMaxY q x s ≤
      panScoreMaxY q x t₁ + panScoreMaxY q x t₂ +
        panScoreMaxY q x t₃ := by
  unfold panScoreMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hpoint := panScoreMaxL_le_three q (s y) (t₁ y) (t₂ y) (t₃ y) (h y)
  have h₁ := Finset.le_max'
    ((Finset.range (x + 1)).image (fun y => panScoreMaxL q (t₁ y)))
    (panScoreMaxL q (t₁ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have h₂ := Finset.le_max'
    ((Finset.range (x + 1)).image (fun y => panScoreMaxL q (t₂ y)))
    (panScoreMaxL q (t₂ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have h₃ := Finset.le_max'
    ((Finset.range (x + 1)).image (fun y => panScoreMaxL q (t₃ y)))
    (panScoreMaxL q (t₃ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  linarith

/-- Finite max bridge from the exact pointwise identity to the concrete
source-faithful signed kernels. -/
theorem panMaxY_le_sourceFaithfulSigned
    (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hf0 : f 0 = 0) :
    panMaxY X q x f ≤
      panPieceMaxY X q x f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceMaxY X q x f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        panSignedResidualMaxY X q x f u v := by
  change panScoreMaxY q x (fun y l => |panDistributionSum y X q l f|) ≤
    panScoreMaxY q x (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ))|) +
    panScoreMaxY q x (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ))|) +
    panScoreMaxY q x (fun y l =>
      |panSignedMainSum y X q l f u v| +
        panSignedCorrectionBound y X q l f)
  exact panScoreMaxY_le_three q x _ _ _ _
    (fun y l hl =>
      abs_panDistributionSum_le_sourceFaithfulSigned y X q l f u v hf0)

/-- The exact inverse-log paper input remaining after all finite identities,
maxima, and conversion residuals have been made explicit.  Its quantifiers
match Liu, Theorem 2 (PDF p.2); the main/error separation is `eqn-m1` and
`eqn-r` (PDF p.5). -/
def PanSourceFaithfulSignedMainBound
    (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (Real.log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panSignedResidualMaxY X q (Nat.floor (x X)) f u v ≤
        C * x X / (Real.log (x X)) ^ A

/-- Conditional finite assembly using the concrete source-faithful residual.
Unlike `PanMeanValueUniform.of_signedAnalyticInputs`, this theorem constructs
the pointwise signed split from Vaughan's exact identity; its only signed-main
hypothesis is the narrow inverse-log paper input above. -/
theorem PanMeanValueUniform.of_sourceFaithfulSignedInputs
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hI : PanTypeICharacterMeanValue x f u)
    (hII : PanTypeIICharacterMeanValue x f u v)
    (hM : PanSourceFaithfulSignedMainBound x f u v)
    (hfin : PanLogEventuallyLarge x)
    (hf0 : f 0 = 0) :
    PanMeanValueUniform x f := by
  have hI' : PanTypeIWeightedBound x f u :=
    PanTypeIWeightedBound.of_characterMeanValue hI
  have hII' : PanTypeIIWeightedBound x f u v :=
    PanTypeIIWeightedBound.of_characterMeanValue hII
  rcases hfin with ⟨X₀, hX₀⟩
  intro A hA
  rcases hI' A hA with ⟨C1, hC1, B1, x₀1, hI1⟩
  rcases hII' A hA with ⟨C2, hC2, B2, x₀2, hII1⟩
  rcases hM A hA with ⟨C3, hC3, B3, x₀3, hM1⟩
  refine ⟨C1 + C2 + C3, add_pos (add_pos hC1 hC2) hC3,
    max B1 (max B2 B3), max (max x₀1 (max x₀2 x₀3)) X₀, ?_⟩
  intro X hX
  have hX1 : x₀1 ≤ X := by omega
  have hX2 : x₀2 ≤ X := by omega
  have hX3 : x₀3 ≤ X := by omega
  have hX0 : X₀ ≤ X := by omega
  have hL : 1 ≤ Real.log (x X) := hX₀ X hX0
  have hsqrt : 0 ≤ (x X) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  let B : ℝ := max B1 (max B2 B3)
  let Q : ℕ :=
    Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B)
  have hQ1 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_max_left _ _)
  have hQ2 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_trans (le_max_left _ _) (le_max_right _ _))
  have hQ3 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
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
    panSignedResidualMaxY X q (Nat.floor (x X)) f u v
  have hw : ∀ q, 0 ≤ w q := fun q => panTypeI_weight_nonneg q
  have hpI : ∀ q, 0 ≤ pI q := by
    intro q
    change 0 ≤ panScoreMaxY q (Nat.floor (x X)) (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ))|)
    exact panScoreMaxY_nonneg _ _ _ (fun y l => abs_nonneg _)
  have hpII : ∀ q, 0 ≤ pII q := by
    intro q
    change 0 ≤ panScoreMaxY q (Nat.floor (x X)) (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ))|)
    exact panScoreMaxY_nonneg _ _ _ (fun y l => abs_nonneg _)
  have hpM : ∀ q, 0 ≤ pM q := fun q =>
    panSignedResidualMaxY_nonneg _ _ _ _ _ _
  have hI2 : (∑ q ∈ Finset.range (Q + 1), w q * pI q) ≤
      C1 * x X / (Real.log (x X)) ^ A :=
    le_trans
      (panAssembly_sum_le_sum Q _ _ hQ1
        (fun q => mul_nonneg (hw q) (hpI q)))
      (by simpa [w, pI] using hI1 X hX1)
  have hII2 : (∑ q ∈ Finset.range (Q + 1), w q * pII q) ≤
      C2 * x X / (Real.log (x X)) ^ A :=
    le_trans
      (panAssembly_sum_le_sum Q _ _ hQ2
        (fun q => mul_nonneg (hw q) (hpII q)))
      (by simpa [w, pII] using hII1 X hX2)
  have hM2 : (∑ q ∈ Finset.range (Q + 1), w q * pM q) ≤
      C3 * x X / (Real.log (x X)) ^ A :=
    le_trans
      (panAssembly_sum_le_sum Q _ _ hQ3
        (fun q => mul_nonneg (hw q) (hpM q)))
      (by simpa [w, pM] using hM1 X hX3)
  calc
    (∑ q ∈ Finset.range (Q + 1),
        w q * panMaxY X q (Nat.floor (x X)) f) ≤
        ∑ q ∈ Finset.range (Q + 1),
          w q * (pI q + pII q + pM q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (panMaxY_le_sourceFaithfulSigned X q (Nat.floor (x X)) f u v hf0)
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

end AnalyticNumberTheory.Sieve
