

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIBilinear
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanPrefixReduction

/-!
 # Vaughan Type I in the long variable

The first and middle prefixes are rearranged before any square is taken.  Their
literal divisor sums become finite sums over the short variables `d` and
`(d,e)`, while the remaining character sum is in the long variable `m`.

The final ledger deliberately freezes only the resulting coefficient moment.
It does not assume a Type-I character estimate, and it does not reuse the
pointwise divisor-cardinality energy from `VaughanTypeIEnergy`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The positive short-variable range occurring in a prefix of length `y`. -/
def vaughanTypeIShortRange (y u : ℕ) : Finset ℕ := Finset.Icc 1 (min y u)

@[simp] theorem mem_vaughanTypeIShortRange {y u d : ℕ} :
    d ∈ vaughanTypeIShortRange y u ↔ 0 < d ∧ d ≤ y ∧ d ≤ u := by
  simp [vaughanTypeIShortRange, Nat.succ_le_iff]

/-- Complex form of the first Vaughan divisor factor. -/
def vaughanTypeIFirstAt (n u : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    (((ArithmeticFunction.moebius d : ℤ) : ℂ) * Real.log ((n / d : ℕ) : ℝ))

/-- Complex form of the middle Vaughan divisor factor. -/
def vaughanTypeIMiddleAt (n u v : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
      (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (ArithmeticFunction.vonMangoldt e : ℂ))

@[simp] theorem vaughanTypeIFirstAt_eq_cast (n u : ℕ) :
    vaughanTypeIFirstAt n u = (Sieve.vaughanFirst n u : ℂ) := by
  unfold vaughanTypeIFirstAt Sieve.vaughanFirst
  push_cast
  rfl

@[simp] theorem vaughanTypeIMiddleAt_eq_cast (n u v : ℕ) :
    vaughanTypeIMiddleAt n u v = (Sieve.vaughanMiddle n u v : ℂ) := by
  unfold vaughanTypeIMiddleAt Sieve.vaughanMiddle
  push_cast
  rfl

/-- On `0 < n ≤ y`, the first divisor factor has a fixed short support. -/
theorem vaughanTypeIFirstAt_eq_bounded {n y u : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    vaughanTypeIFirstAt n u =
      ∑ d ∈ vaughanTypeIShortRange y u,
        if d ∣ n then
          (((ArithmeticFunction.moebius d : ℤ) : ℂ) * Real.log ((n / d : ℕ) : ℝ))
        else 0 := by
  unfold vaughanTypeIFirstAt
  have hdset : n.divisors.filter (fun d => d ≤ u) =
      (vaughanTypeIShortRange y u).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdu⟩
      have hdpos := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨mem_vaughanTypeIShortRange.mpr
        ⟨hdpos, (Nat.le_of_dvd hn hdn).trans hny, hdu⟩, hdn⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩, (mem_vaughanTypeIShortRange.mp hd).2.2⟩
  rw [hdset, Finset.sum_filter]

/-- On `0 < n ≤ y`, the middle factor is a fixed short `(d,e)` rectangle.
The condition `e ∣ n/d` has become the single product condition `d*e ∣ n`. -/
theorem vaughanTypeIMiddleAt_eq_bounded {n y u v : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    vaughanTypeIMiddleAt n u v =
      ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          if d * e ∣ n then
            (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (ArithmeticFunction.vonMangoldt e : ℂ))
          else 0 := by
  unfold vaughanTypeIMiddleAt
  have hdset : n.divisors.filter (fun d => d ≤ u) =
      (vaughanTypeIShortRange y u).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdu⟩
      have hdpos := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨mem_vaughanTypeIShortRange.mpr
        ⟨hdpos, (Nat.le_of_dvd hn hdn).trans hny, hdu⟩, hdn⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩, (mem_vaughanTypeIShortRange.mp hd).2.2⟩
  rw [hdset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdpos : 0 < d := (mem_vaughanTypeIShortRange.mp hd).1
    have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have heset : (n / d).divisors.filter (fun e => e ≤ v) =
        (vaughanTypeIShortRange y v).filter (fun e => d * e ∣ n) := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hed, _⟩, hev⟩
        have hmul : d * e ∣ n := (Nat.dvd_div_iff_mul_dvd hdn).mp hed
        have hepos : 0 < e := Nat.pos_of_dvd_of_pos hed hndpos
        have hen : e ≤ n := Nat.le_of_dvd hn ((dvd_mul_left e d).trans hmul)
        exact ⟨mem_vaughanTypeIShortRange.mpr
          ⟨hepos, hen.trans hny, hev⟩, hmul⟩
      · rintro ⟨he, hmul⟩
        have hed : e ∣ n / d := (Nat.dvd_div_iff_mul_dvd hdn).mpr hmul
        exact ⟨⟨hed, hndpos.ne'⟩,
          (mem_vaughanTypeIShortRange.mp he).2.2⟩
    rw [heset, Finset.sum_filter]
  · have hde : ∀ e : ℕ, ¬ d * e ∣ n := by
      intro e h
      exact hdn ((dvd_mul_right d e).trans h)
    simp [hdn, hde]

/-- The first Type-I prefix before rearrangement. -/
def vaughanTypeIFirstPrefix
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIFirstAt n u

/-- The first prefix after `n=d*m`; the character sum is long in `m`. -/
def vaughanTypeIFirstLong
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanTypeIShortRange y u,
    ((((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ.1 (d : ZMod q)) *
      ∑ m ∈ Finset.Icc 1 (y / d),
        (b (d * m) * Real.log (m : ℝ)) * χ.1 (m : ZMod q))

/-- Exact first-prefix rearrangement into a short `d` coefficient and a long
`m` character sum. -/
theorem vaughanTypeIFirstPrefix_eq_long
    (b : ℕ → ℂ) (y u q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIFirstPrefix b y u q χ = vaughanTypeIFirstLong b y u q χ := by
  unfold vaughanTypeIFirstPrefix vaughanTypeIFirstLong
  calc
    (∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) * vaughanTypeIFirstAt n u) =
        ∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) *
          ∑ d ∈ vaughanTypeIShortRange y u,
            if d ∣ n then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              Real.log ((n / d : ℕ) : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIFirstAt_eq_bounded (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2]
    _ = ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ n ∈ Finset.Icc 1 y,
          if d ∣ n then b n * χ.1 (n : ZMod q) *
            (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              Real.log ((n / d : ℕ) : ℝ)) else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := (mem_vaughanTypeIShortRange.mp hd).1
      rw [← Finset.sum_filter]
      rw [sum_multiples_Icc_reindex
        (fun n => b n * χ.1 (n : ZMod q) *
          (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            Real.log ((n / d : ℕ) : ℝ))) hdpos]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m hdpos]
      rw [show ((d * m : ℕ) : ZMod q) = (d : ZMod q) * (m : ZMod q) by
        simp only [Nat.cast_mul], map_mul]
      ring

/-- The middle Type-I prefix before rearrangement. -/
def vaughanTypeIMiddlePrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIMiddleAt n u v

/-- The middle prefix after `n=d*e*m`; `(d,e)` are short and `m` is long. -/
def vaughanTypeIMiddleLong
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanTypeIShortRange y u,
    ∑ e ∈ vaughanTypeIShortRange y v,
      (((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (ArithmeticFunction.vonMangoldt e : ℂ)) *
          χ.1 (d : ZMod q) * χ.1 (e : ZMod q)) *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          b (d * e * m) * χ.1 (m : ZMod q))

/-- Exact middle-prefix rearrangement into short `(d,e)` coefficients and a
long `m` character sum. -/
theorem vaughanTypeIMiddlePrefix_eq_long
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIMiddlePrefix b y u v q χ =
      vaughanTypeIMiddleLong b y u v q χ := by
  unfold vaughanTypeIMiddlePrefix vaughanTypeIMiddleLong
  calc
    (∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) * vaughanTypeIMiddleAt n u v) =
        ∑ n ∈ Finset.Icc 1 y, b n * χ.1 (n : ZMod q) *
          ∑ d ∈ vaughanTypeIShortRange y u,
            ∑ e ∈ vaughanTypeIShortRange y v,
              if d * e ∣ n then (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (ArithmeticFunction.vonMangoldt e : ℂ)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIMiddleAt_eq_bounded (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2]
    _ = ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          ∑ n ∈ Finset.Icc 1 y,
            if d * e ∣ n then b n * χ.1 (n : ZMod q) *
              ((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
                (ArithmeticFunction.vonMangoldt e : ℂ))) else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hdpos := (mem_vaughanTypeIShortRange.mp hd).1
      have hepos := (mem_vaughanTypeIShortRange.mp he).1
      have hde : 0 < d * e := Nat.mul_pos hdpos hepos
      rw [← Finset.sum_filter]
      rw [sum_multiples_Icc_reindex
        (fun n => b n * χ.1 (n : ZMod q) *
          ((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (ArithmeticFunction.vonMangoldt e : ℂ)))) hde]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [show ((d * e * m : ℕ) : ZMod q) =
        (d : ZMod q) * (e : ZMod q) * (m : ZMod q) by
          simp only [Nat.cast_mul], map_mul, map_mul]
      ring

/-- The signed Type-I prefix, exactly equal to first minus middle. -/
def vaughanTypeILongPrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  vaughanTypeIFirstLong b y u q χ - vaughanTypeIMiddleLong b y u v q χ

/-- Exact replacement of the packaged Type-I prefix by its long-variable form. -/
theorem vaughanTypeIPrefix_eq_long
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    (∑ n ∈ Finset.Icc 1 y,
      b n * χ.1 (n : ZMod q) * (vaughanTypeI n u v : ℂ)) =
      vaughanTypeILongPrefix b y u v q χ := by
  simp only [vaughanTypeI]
  push_cast
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold vaughanTypeILongPrefix
  exact congrArg₂ (· - ·)
    (by simpa [vaughanTypeIFirstPrefix] using
      vaughanTypeIFirstPrefix_eq_long b y u q χ)
    (by simpa [vaughanTypeIMiddlePrefix] using
      vaughanTypeIMiddlePrefix_eq_long b y u v q χ)

/-- Character-free Type-I coefficient produced by the exact long-variable
rearrangement.  This is the smallest coefficient moment needed by the
primitive prefix large sieve. -/
def vaughanTypeILongCoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeI n.toNat u v : ℂ)

/-- The literal finite coefficient moment; no pointwise divisor-cardinality
majorant has been inserted. -/
def vaughanTypeILongCoeffMoment (b : ℤ → ℂ) (N u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeILongCoeff b u v n‖ ^ 2

/-- Prefix maximum written on the rearranged long-variable forms themselves. -/
def vaughanTypeILongPrefixMaxSquare
    (b : ℤ → ℂ) (N u v q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image (fun y =>
      ‖vaughanTypeILongPrefix (fun n => b n) y u v q χ‖ ^ 2)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Every prefix of the collected coefficient sequence is literally the
previously rearranged short-times-long expression. -/
theorem primitiveCharacterPrefixSquare_typeI_eq_long
    (b : ℤ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare (vaughanTypeILongCoeff b u v) 0 y q χ =
      ‖vaughanTypeILongPrefix (fun n => b n) y u v q χ‖ ^ 2 := by
  unfold primitiveCharacterPrefixSquare
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 y
    (fun z => vaughanTypeILongCoeff b u v z * χ.1 (z : ZMod q))
  have hsum' :
      (∑ n ∈ Finset.Ioc 0 y,
        vaughanTypeILongCoeff b u v (n : ℤ) * χ.1 (n : ZMod q)) =
      ∑ z ∈ Finset.Icc (1 : ℤ) y,
        vaughanTypeILongCoeff b u v z * χ.1 (z : ZMod q) := by
    simpa using hsum
  rw [← hsum']
  have hset : Finset.Ioc 0 y = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  rw [← vaughanTypeIPrefix_eq_long (fun n => b n) y u v q χ]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  simp only [vaughanTypeILongCoeff, Int.toNat_natCast]
  ring

/-- The generic prefix maximum and the maximum of the exact long-variable
forms are equal, not merely comparable. -/
theorem primitiveCharacterPrefixMaxSquare_typeI_eq_long
    (b : ℤ → ℂ) (N u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixMaxSquare (vaughanTypeILongCoeff b u v) 0 N q χ =
      vaughanTypeILongPrefixMaxSquare b N u v q χ := by
  unfold primitiveCharacterPrefixMaxSquare vaughanTypeILongPrefixMaxSquare
  congr 2
  funext y
  exact primitiveCharacterPrefixSquare_typeI_eq_long b y u v q χ

/-- Minimal BV-scale scalar hypothesis.  It is a coefficient moment only, not a
Type-I character-sum conclusion.  All of `u,v,N` remain explicit. -/
def VaughanTypeILongCoeffMomentBound
    (b : ℤ → ℂ) (N u v : ℕ) (C : ℝ) (κ : ℕ) : Prop :=
  vaughanTypeILongCoeffMoment b N u v ≤
    C * (N : ℝ) * Real.log (N + 1 : ℕ) ^ κ

/-- Primitive large sieve applied only after the exact long-variable
rearrangement. -/
theorem weighted_primitive_vaughanTypeILong
    (b : ℤ → ℂ) (N Q u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanTypeILongCoeff b u v) 0 N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          vaughanTypeILongCoeffMoment b N u v := by
  simpa [vaughanTypeILongCoeffMoment] using
    weighted_primitive_prefix_maximal (vaughanTypeILongCoeff b u v) 0 N Q hQ

/-- Primitive large sieve in the publication-facing, genuinely rearranged
form: its left side is a maximum of short-variable coefficients multiplying
long-variable character sums. -/
theorem weighted_primitive_vaughanTypeILong_rearranged
    (b : ℤ → ℂ) (N Q u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          vaughanTypeILongPrefixMaxSquare b N u v q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          vaughanTypeILongCoeffMoment b N u v := by
  simpa only [← primitiveCharacterPrefixMaxSquare_typeI_eq_long] using
    weighted_primitive_vaughanTypeILong b N Q u v hQ

/-- Explicit BV-compatible `N * log^κ` coefficient scale.  The only premise is
the minimal coefficient moment above. -/
theorem weighted_primitive_vaughanTypeILong_of_moment
    (b : ℤ → ℂ) (N Q u v : ℕ) (C : ℝ) (κ : ℕ) (hQ : 0 < Q)
    (hMoment : VaughanTypeILongCoeffMomentBound b N u v C κ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanTypeILongCoeff b u v) 0 N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          (C * (N : ℝ) * Real.log (N + 1 : ℕ) ^ κ) := by
  refine (weighted_primitive_vaughanTypeILong b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left hMoment
  unfold primitiveLargeSieveConstant
  positivity

/-- Weighted Vaughan ledger with the old pointwise Type-I energy removed.
Type I is charged by the exact long-variable coefficient moment; Type II and
the small range retain their existing coefficient moments. -/
theorem weighted_vaughan_prefix_large_sieve_long_typeI_ledger
    (b : ℤ → ℂ) (N Q u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanLambdaCoeff b) 0 N q χ) ≤
      3 * (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
        (vaughanTypeILongCoeffMoment b N u v +
          (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeIICoeff b u v n‖ ^ 2) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2)) := by
  simpa [vaughanTypeILongCoeffMoment, vaughanTypeILongCoeff,
    vaughanTypeICoeff] using
      weighted_vaughan_prefix_large_sieve_ledger b N Q u v hQ

/-- The integrated weighted Vaughan ledger after inserting precisely the
BV-scale coefficient-moment premise.  No Type-I character-sum estimate is
assumed: the primitive large sieve was proved above from the coefficient
moment. -/
theorem weighted_vaughan_prefix_large_sieve_long_typeI_ledger_of_moment
    (b : ℤ → ℂ) (N Q u v : ℕ) (C : ℝ) (κ : ℕ) (hQ : 0 < Q)
    (hMoment : VaughanTypeILongCoeffMomentBound b N u v C κ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanLambdaCoeff b) 0 N q χ) ≤
      3 * (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
        ((C * (N : ℝ) * Real.log (N + 1 : ℕ) ^ κ) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeIICoeff b u v n‖ ^ 2) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2)) := by
  refine (weighted_vaughan_prefix_large_sieve_long_typeI_ledger
    b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · gcongr
    exact hMoment
  · have hLS : 0 ≤ primitiveLargeSieveConstant N Q := by
      unfold primitiveLargeSieveConstant
      positivity
    positivity

end

end AnalyticNumberTheory.LargeSieve
