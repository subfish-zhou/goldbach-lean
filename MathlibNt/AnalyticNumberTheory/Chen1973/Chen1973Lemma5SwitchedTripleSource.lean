/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma1PerronKernel
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma4CharacterSum
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Chen 1973, Lemma 5: the actual switched triple source

This file freezes the opening of Lemma 5 on pp. 116--119 of Chen's original
scan.  It keeps the actual von Mangoldt coefficient, Chen's finite Perron kernel
`Φ(x/(p₁p₂n))`, and the reciprocal logarithmic weight.  In particular it does
not replace the source by an arbitrary coefficient sequence.

The analytic estimates in Lemmas 5--6 are not asserted here.  The first layer is
the exact finite bookkeeping used before those estimates: the prime-triple
carrier, the Selberg-square expansion, the principal/nonprincipal partition,
and the resulting `M₁-M₃+M₄` identity.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- A natural cutoff version of Chen's `Q=∏_{2≤p<x^(1/4)}p`.
The relation to the real fourth root is carried separately, so the finite
product never uses a fake real-indexed finset. -/
def chen1973Lemma5Q (z4 : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z4).filter (fun p => 2 ≤ p ∧ p.Prime), p

/-- An honest natural cutoff realizes the source's strict real fourth-root
cutoff when these membership predicates agree. -/
def Chen1973FourthRootCutoff (x : ℕ) (z4 : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    (p < z4 ↔ (p : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 4))

/-- Under the explicit cutoff bridge, membership in the finite `Q` carrier is
exactly the source condition `2 ≤ p < x^(1/4)`. -/
theorem mem_chen1973Lemma5QCarrier_iff
    {x z4 p : ℕ} (hz : Chen1973FourthRootCutoff x z4) (hp : p.Prime) :
    p ∈ (Finset.range z4).filter (fun q => 2 ≤ q ∧ q.Prime) ↔
      2 ≤ p ∧ (p : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 4) := by
  simp only [Finset.mem_filter, Finset.mem_range, hp, and_true]
  constructor
  · rintro ⟨hpz, hp2⟩
    exact ⟨hp2, (hz p hp).mp hpz⟩
  · rintro ⟨hp2, hroot⟩
    exact ⟨(hz p hp).mpr hroot, hp2⟩

/-- The finite pair carrier printed at the start of Lemma 5:
`x^(1/10)<p₁≤x^(1/3)<p₂≤(x/p₁)^(1/2)`. -/
def chen1973Lemma5PrimePairs (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (x + 1)).product (Finset.range (x + 1))).filter fun pp =>
    pp.1.Prime ∧ pp.2.Prime ∧
    (x : ℝ) ^ ((1 : ℝ) / 10) < pp.1 ∧
    (pp.1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) ∧
    (x : ℝ) ^ ((1 : ℝ) / 3) < pp.2 ∧
    (pp.2 : ℝ) ≤ ((x : ℝ) / pp.1) ^ ((1 : ℝ) / 2)

/-- The actual finite triple carrier counted by `Ω`, before the coprimality
sieve is imposed. -/
def chen1973Lemma5PrimeTriples (x : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((chen1973Lemma5PrimePairs x).product (Finset.range (x + 1))).filter fun t =>
    t.2.Prime ∧ t.2 ≤ x / (t.1.1 * t.1.2)

/-- Chen's `Ω`: prime triples in the printed carrier for which
`(x-p₁p₂p₃,Q)=1`. -/
def chen1973Lemma5OmegaCarrier (x z4 : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (chen1973Lemma5PrimeTriples x).filter fun t =>
    Nat.Coprime (x - t.1.1 * t.1.2 * t.2) (chen1973Lemma5Q z4)

/-- The integer counted by the source symbol `Ω`. -/
def chen1973Lemma5Omega (x z4 : ℕ) : ℕ :=
  (chen1973Lemma5OmegaCarrier x z4).card

/-- Literal membership conditions for the finite `Ω` carrier. -/
theorem mem_chen1973Lemma5OmegaCarrier_iff {x z4 : ℕ} {t : (ℕ × ℕ) × ℕ} :
    t ∈ chen1973Lemma5OmegaCarrier x z4 ↔
      t.1 ∈ chen1973Lemma5PrimePairs x ∧ t.2 < x + 1 ∧ t.2.Prime ∧
        t.2 ≤ x / (t.1.1 * t.1.2) ∧
        Nat.Coprime (x - t.1.1 * t.1.2 * t.2) (chen1973Lemma5Q z4) := by
  simp [chen1973Lemma5OmegaCarrier, chen1973Lemma5PrimeTriples]
  tauto

/-- Chen p. 115: `f(k)=φ(k)∏_{p∣k}(p-2)/(p-1)`. -/
def chen1973Lemma5SelbergF (k : ℕ) : ℝ :=
  Nat.totient k * ∏ p ∈ k.primeFactors, ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- The normalized finite denominator in Chen's literal Selberg coefficient. -/
def chen1973Lemma5SelbergDenominator (x R : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (R + 1)).filter (fun k => 1 ≤ k ∧ Nat.Coprime k x),
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / chen1973Lemma5SelbergF k

/-- The actual coefficient `λ_d` defined immediately before Lemma 5 (p. 115).
`R` is the honest natural version of `x^(1/4-ε/2)`. -/
def chen1973Lemma5SelbergLambda (x R d : ℕ) : ℝ :=
  if d = 1 then 1 else if R < d then 0 else
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        (chen1973Lemma5SelbergF d * (Nat.totient d : ℝ)⁻¹)) *
      (∑ k ∈ (Finset.range (R / d + 1)).filter
          (fun k => 1 ≤ k ∧ Nat.Coprime k (x * d)),
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 /
          chen1973Lemma5SelbergF k) *
      (chen1973Lemma5SelbergDenominator x R)⁻¹

@[simp] theorem chen1973Lemma5SelbergLambda_one (x R : ℕ) :
    chen1973Lemma5SelbergLambda x R 1 = 1 := by
  simp [chen1973Lemma5SelbergLambda]

theorem chen1973Lemma5SelbergLambda_eq_zero_of_cutoff
    {x R d : ℕ} (hR : 1 ≤ R) (hd : R < d) :
    chen1973Lemma5SelbergLambda x R d = 0 := by
  by_cases hd1 : d = 1
  · subst d
    omega
  · simp [chen1973Lemma5SelbergLambda, hd1, hd]

/-- The finite `n≤x/(p₁p₂)` carrier used after switching `p₃` to `Λ(n)`. -/
def chen1973Lemma5NCarrier (x : ℕ) (pp : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n => n ≤ x / (pp.1 * pp.2)

/-- The literal source weight
`Λ(n) Φ(x/(p₁p₂n)) / log(x/(p₁p₂))`.
The value at a zero denominator is totalized by Lean's field operations; on the
prime-pair carrier the later analytic development proves the required
positivity separately. -/
def chen1973Lemma5SmoothedWeight (x : ℕ) (pp : ℕ × ℕ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    chen1973PerronKernelFinite (x : ℝ)
      ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) /
    Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))

/-- The unsmoothed switched main sum `M` printed on p. 116. -/
def chen1973Lemma5M (x z4 : ℕ) : ℝ :=
  ∑ pp ∈ chen1973Lemma5PrimePairs x,
    (1 / Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))) *
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        if Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4) then
          ArithmeticFunction.vonMangoldt n
        else 0

/-- The divisor support in the Selberg square: `d∣Q`, `(d,x)=1`. -/
def chen1973Lemma5DivisorCarrier (x z4 : ℕ) : Finset ℕ :=
  (chen1973Lemma5Q z4).divisors.filter fun d => Nat.Coprime d x

/-- The finite Selberg divisor sum appearing inside the square in (5). -/
def chen1973Lemma5DivisorSum
    (x z4 : ℕ) (lambda : ℕ → ℝ) (pp : ℕ × ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma5DivisorCarrier x z4,
    if d ∣ x - pp.1 * pp.2 * n then lambda d else 0

/-- The exact smoothed Selberg square before expanding in `d₁,d₂`. -/
def chen1973Lemma5SelbergSquare
    (x z4 : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ pp ∈ chen1973Lemma5PrimePairs x,
    ∑ n ∈ chen1973Lemma5NCarrier x pp,
      chen1973Lemma5SmoothedWeight x pp n *
        (chen1973Lemma5DivisorSum x z4 lambda pp n) ^ 2

/-- The literal switched `Λ·Φ/log` mass on the `Ω` carrier.  Keeping this
quantity separate avoids silently replacing Chen's smoothed source by a bare
cardinality. -/
def chen1973Lemma5OmegaSmoothed (x z4 : ℕ) : ℝ :=
  ∑ t ∈ chen1973Lemma5OmegaCarrier x z4,
    chen1973Lemma5SmoothedWeight x t.1 t.2

/-- The source weight is nonnegative once its (printed) logarithmic denominator
is known to be nonnegative.  The nonnegativity of `Λ` and of Chen's finite
Perron kernel are discharged internally. -/
theorem chen1973Lemma5SmoothedWeight_nonneg
    {x : ℕ} (hx : 1 < x) {pp : ℕ × ℕ} {n : ℕ}
    (hlog : 0 ≤ Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))) :
    0 ≤ chen1973Lemma5SmoothedWeight x pp n := by
  unfold chen1973Lemma5SmoothedWeight
  apply div_nonneg
  · apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    exact (chen1973PerronKernelFinite_mem_Icc (by exact_mod_cast hx) (by positivity)).1
  · exact hlog

/-- The finite product defining `Q` is nonzero. -/
theorem chen1973Lemma5Q_ne_zero (z4 : ℕ) : chen1973Lemma5Q z4 ≠ 0 := by
  unfold chen1973Lemma5Q
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact hp.2.2.ne_zero

/-- On an `Ω` residue, every divisor of `Q` which divides the residue is one;
therefore a Selberg divisor sum normalized by `λ₁=1` is exactly one. -/
theorem chen1973Lemma5DivisorSum_eq_one_of_coprime
    {x z4 : ℕ} {lambda : ℕ → ℝ} (hlambda : lambda 1 = 1)
    {pp : ℕ × ℕ} {n : ℕ}
    (hcop : Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4)) :
    chen1973Lemma5DivisorSum x z4 lambda pp n = 1 := by
  classical
  unfold chen1973Lemma5DivisorSum
  rw [Finset.sum_eq_single 1]
  · simp [hlambda]
  · intro d hd hd1
    have hdQ : d ∣ chen1973Lemma5Q z4 :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    by_cases hdr : d ∣ x - pp.1 * pp.2 * n
    · exact (hd1 (Nat.eq_one_of_dvd_coprimes hcop hdr hdQ)).elim
    · simp [hdr]
  · intro h1
    exact (h1 (by simp [chen1973Lemma5DivisorCarrier,
      chen1973Lemma5Q_ne_zero])).elim

/-- Exact reindexing of the smoothed `Ω` source into the switched pair/`n`
coordinates used by the Selberg square. -/
theorem chen1973Lemma5OmegaSmoothed_eq_switched (x z4 : ℕ) :
    chen1973Lemma5OmegaSmoothed x z4 =
      ∑ pp ∈ chen1973Lemma5PrimePairs x,
        ∑ n ∈ chen1973Lemma5NCarrier x pp,
          if n.Prime ∧
              Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4) then
            chen1973Lemma5SmoothedWeight x pp n
          else 0 := by
  classical
  simp only [chen1973Lemma5OmegaSmoothed, chen1973Lemma5OmegaCarrier,
    chen1973Lemma5PrimeTriples, chen1973Lemma5NCarrier, Finset.sum_filter]
  calc
    _ = ∑ pp ∈ chen1973Lemma5PrimePairs x,
          ∑ n ∈ Finset.range (x + 1),
            if n.Prime ∧ n ≤ x / (pp.1 * pp.2) then
              if Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4) then
                chen1973Lemma5SmoothedWeight x pp n else 0
            else 0 := by
      exact Finset.sum_product _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pp hpp
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hle : n ≤ x / (pp.1 * pp.2)
      · by_cases hp : n.Prime
        · by_cases hcop : Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4)
          · simp [hle, hp]
          · simp [hle, hp]
        · simp [hle, hp]
      · simp [hle]

/-- The actual smoothed `Ω` mass is bounded by the actual Selberg square.  The
only hypotheses are `λ₁=1` and nonnegativity of the source weights; the latter
is supplied by `chen1973Lemma5SmoothedWeight_nonneg` from the genuine
`Λ·Φ/log` definition. -/
theorem chen1973Lemma5OmegaSmoothed_le_SelbergSquare
    {x z4 : ℕ} {lambda : ℕ → ℝ} (hlambda : lambda 1 = 1)
    (hw : ∀ pp ∈ chen1973Lemma5PrimePairs x,
      ∀ n ∈ chen1973Lemma5NCarrier x pp,
        0 ≤ chen1973Lemma5SmoothedWeight x pp n) :
    chen1973Lemma5OmegaSmoothed x z4 ≤
      chen1973Lemma5SelbergSquare x z4 lambda := by
  rw [chen1973Lemma5OmegaSmoothed_eq_switched]
  unfold chen1973Lemma5SelbergSquare
  apply Finset.sum_le_sum
  intro pp hpp
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · by_cases hcop : Nat.Coprime (x - pp.1 * pp.2 * n) (chen1973Lemma5Q z4)
    · rw [if_pos ⟨hp, hcop⟩,
        chen1973Lemma5DivisorSum_eq_one_of_coprime hlambda hcop]
      simp
    · rw [if_neg (fun h => hcop h.2)]
      exact mul_nonneg (hw pp hpp n hn) (sq_nonneg _)
  · rw [if_neg (fun h => hp h.1)]
    exact mul_nonneg (hw pp hpp n hn) (sq_nonneg _)

/-- A separate, honest cardinal bridge.  It applies when the retained smoothed
weight is pointwise at least one; this condition is deliberately explicit and
is not conflated with mere nonnegativity of the Perron weight. -/
theorem chen1973Lemma5Omega_le_OmegaSmoothed
    {x z4 : ℕ}
    (hw1 : ∀ t ∈ chen1973Lemma5OmegaCarrier x z4,
      (1 : ℝ) ≤ chen1973Lemma5SmoothedWeight x t.1 t.2) :
    (chen1973Lemma5Omega x z4 : ℝ) ≤ chen1973Lemma5OmegaSmoothed x z4 := by
  unfold chen1973Lemma5Omega chen1973Lemma5OmegaSmoothed
  have hcard : ((chen1973Lemma5OmegaCarrier x z4).card : ℝ) =
      ∑ _t ∈ chen1973Lemma5OmegaCarrier x z4, (1 : ℝ) := by simp
  rw [hcard]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum hw1

/-- Cardinal form of the `Ω`--Selberg-square bridge, with the genuinely stronger
pointwise lower bound isolated from the internally proved sign condition. -/
theorem chen1973Lemma5Omega_le_SelbergSquare
    {x z4 : ℕ} {lambda : ℕ → ℝ} (hlambda : lambda 1 = 1)
    (hw0 : ∀ pp ∈ chen1973Lemma5PrimePairs x,
      ∀ n ∈ chen1973Lemma5NCarrier x pp,
        0 ≤ chen1973Lemma5SmoothedWeight x pp n)
    (hw1 : ∀ t ∈ chen1973Lemma5OmegaCarrier x z4,
      (1 : ℝ) ≤ chen1973Lemma5SmoothedWeight x t.1 t.2) :
    (chen1973Lemma5Omega x z4 : ℝ) ≤
      chen1973Lemma5SelbergSquare x z4 lambda :=
  (chen1973Lemma5Omega_le_OmegaSmoothed hw1).trans
    (chen1973Lemma5OmegaSmoothed_le_SelbergSquare hlambda hw0)

/-- The progression sum denoted `N_[d₁,d₂]` in (5). -/
def chen1973Lemma5ProgressionTerm
    (x : ℕ) (d1 d2 : ℕ) : ℝ :=
  ∑ pp ∈ chen1973Lemma5PrimePairs x,
    ∑ n ∈ chen1973Lemma5NCarrier x pp,
      if Nat.lcm d1 d2 ∣ x - pp.1 * pp.2 * n then
        chen1973Lemma5SmoothedWeight x pp n
      else 0

/-- Expansion of Chen's Selberg square into the two divisor variables. -/
theorem chen1973Lemma5SelbergSquare_eq_expanded
    (x z4 : ℕ) (lambda : ℕ → ℝ) :
    chen1973Lemma5SelbergSquare x z4 lambda =
      ∑ d1 ∈ chen1973Lemma5DivisorCarrier x z4,
        ∑ d2 ∈ chen1973Lemma5DivisorCarrier x z4,
          lambda d1 * lambda d2 * chen1973Lemma5ProgressionTerm x d1 d2 := by
  classical
  let S := chen1973Lemma5DivisorCarrier x z4
  let P := chen1973Lemma5PrimePairs x
  let A := fun pp : ℕ × ℕ => chen1973Lemma5NCarrier x pp
  let w := chen1973Lemma5SmoothedWeight x
  let a := fun (d : ℕ) (pp : ℕ × ℕ) (n : ℕ) =>
    if d ∣ x - pp.1 * pp.2 * n then lambda d else 0
  have hsquare (pp : ℕ × ℕ) (n : ℕ) :
      (∑ d ∈ S, a d pp n) ^ 2 =
        ∑ d1 ∈ S, ∑ d2 ∈ S, a d1 pp n * a d2 pp n := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hcomm (f : (ℕ × ℕ) → ℕ → ℕ → ℕ → ℝ) :
      (∑ pp ∈ P, ∑ n ∈ A pp, ∑ d1 ∈ S, ∑ d2 ∈ S, f pp n d1 d2) =
        ∑ d1 ∈ S, ∑ d2 ∈ S, ∑ pp ∈ P, ∑ n ∈ A pp, f pp n d1 d2 := by
    calc
      _ = ∑ pp ∈ P, ∑ d1 ∈ S, ∑ d2 ∈ S, ∑ n ∈ A pp, f pp n d1 d2 := by
        apply Finset.sum_congr rfl
        intro pp hpp
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d1 hd1
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d1 hd1
        rw [Finset.sum_comm]
  change (∑ pp ∈ P, ∑ n ∈ A pp, w pp n * (∑ d ∈ S, a d pp n) ^ 2) = _
  simp_rw [hsquare, Finset.mul_sum]
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro d1 hd1
  apply Finset.sum_congr rfl
  intro d2 hd2
  simp only [chen1973Lemma5ProgressionTerm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pp hpp
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [a, w]
  by_cases h1 : d1 ∣ x - pp.1 * pp.2 * n
  · by_cases h2 : d2 ∣ x - pp.1 * pp.2 * n
    · simp [h1, h2, Nat.lcm_dvd_iff]
      ring
    · simp [h1, h2, Nat.lcm_dvd_iff]
  · simp [h1, Nat.lcm_dvd_iff]

/-- Principal-character sum with no coprimality deletion. -/
def chen1973Lemma5PrincipalAll (x d1 d2 : ℕ) : ℝ :=
  (Nat.totient (Nat.lcm d1 d2) : ℝ)⁻¹ *
    ∑ pp ∈ chen1973Lemma5PrimePairs x,
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        chen1973Lemma5SmoothedWeight x pp n

/-- The part of the principal sum satisfying `(p₁p₂n,d₁d₂)=1`. -/
def chen1973Lemma5PrincipalGood (x d1 d2 : ℕ) : ℝ :=
  (Nat.totient (Nat.lcm d1 d2) : ℝ)⁻¹ *
    ∑ pp ∈ chen1973Lemma5PrimePairs x,
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        if Nat.Coprime (pp.1 * pp.2 * n) (d1 * d2) then
          chen1973Lemma5SmoothedWeight x pp n
        else 0

/-- The complementary principal contribution `(p₁p₂n,d₁d₂)>1`, source `M₃`. -/
def chen1973Lemma5PrincipalBad (x d1 d2 : ℕ) : ℝ :=
  (Nat.totient (Nat.lcm d1 d2) : ℝ)⁻¹ *
    ∑ pp ∈ chen1973Lemma5PrimePairs x,
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        if Nat.Coprime (pp.1 * pp.2 * n) (d1 * d2) then 0
        else chen1973Lemma5SmoothedWeight x pp n

/-- Pure finite partition of the principal sum into good and bad gcd lanes. -/
theorem chen1973Lemma5PrincipalAll_eq_good_add_bad (x d1 d2 : ℕ) :
    chen1973Lemma5PrincipalAll x d1 d2 =
      chen1973Lemma5PrincipalGood x d1 d2 +
        chen1973Lemma5PrincipalBad x d1 d2 := by
  classical
  unfold chen1973Lemma5PrincipalAll chen1973Lemma5PrincipalGood
    chen1973Lemma5PrincipalBad
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pp hpp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : Nat.Coprime (pp.1 * pp.2 * n) (d1 * d2)
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- Source `M₁`: the unrestricted principal-character main term. -/
def chen1973Lemma5M1
    (x z4 : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ chen1973Lemma5DivisorCarrier x z4,
    ∑ d2 ∈ chen1973Lemma5DivisorCarrier x z4,
      lambda d1 * lambda d2 * chen1973Lemma5PrincipalAll x d1 d2

/-- Source `M₃`: the non-coprime correction removed from `M₁`. -/
def chen1973Lemma5M3
    (x z4 : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ chen1973Lemma5DivisorCarrier x z4,
    ∑ d2 ∈ chen1973Lemma5DivisorCarrier x z4,
      lambda d1 * lambda d2 * chen1973Lemma5PrincipalBad x d1 d2

/-- Source `M₄` at the finite pre-contour level: the exact progression
remainder after subtracting the coprime principal-character term. -/
def chen1973Lemma5M4
    (x z4 : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ chen1973Lemma5DivisorCarrier x z4,
    ∑ d2 ∈ chen1973Lemma5DivisorCarrier x z4,
      lambda d1 * lambda d2 *
        (chen1973Lemma5ProgressionTerm x d1 d2 -
          chen1973Lemma5PrincipalGood x d1 d2)

/-- The actual twisted switched source at modulus `q`; the coefficient remains
literally `Λ(n) Φ(x/(p₁p₂n)) / log(x/(p₁p₂))`. -/
def chen1973Lemma5PrimitiveTwist
    (x q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  star (χ.1 (x : ZMod q)) *
    ∑ pp ∈ chen1973Lemma5PrimePairs x,
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        (chen1973Lemma5SmoothedWeight x pp n : ℂ) *
          χ.1 ((pp.1 * pp.2 * n : ℕ) : ZMod q)

/-- The pointwise Dirichlet-character orthogonality relation needed to turn a
progression condition into a character sum.  Unlike a black-box source
premise, this finite step is proved directly from Mathlib's orthogonality API. -/
theorem chen1973Lemma5_character_orthogonality
    {q x a : ℕ} [NeZero q] (hxq : Nat.Coprime x q) :
    (∑ χ : DirichletCharacter ℂ q,
        star (χ (x : ZMod q)) * χ (a : ZMod q)) =
      if (x : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0 := by
  have hxu : IsUnit (x : ZMod q) := (ZMod.isUnit_iff_coprime x q).2 hxq
  rw [← DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hxu (a : ZMod q)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [← MulChar.star_apply, MulChar.star_eq_inv, MulChar.inv_apply_eq_inv']
  congr 1
  apply inv_eq_of_mul_eq_one_right
  rw [mul_comm, ← map_mul]
  rw [(ZMod.inv_mul_eq_one_of_isUnit hxu (x : ZMod q)).2 rfl, map_one]

/-- The old one-conductor signed ledger.  It is useful as the inner
character majorant, but it is not Chen's p. 117--119 source `M₂`: that source
still has an outer squarefree `d`-sum and the restriction `(p₁p₂,d)=1`. -/
def chen1973Lemma5M2Signed (x D : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (D + 1)).filter (fun l => Nat.Coprime l x ∧ Squarefree l),
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 *
      (3 : ℝ) ^ l.primeFactors.card / Nat.totient l *
      (∑ χ : PrimitiveCharacter l,
        if χ.1 = 1 then 0 else chen1973Lemma5PrimitiveTwist x l χ).re

/-- Compatibility name for the old one-conductor norm ledger.  This is only an
inner majorant (the shape later denoted `N_m` after inserting a prime-pair
filter), not the source `M₂` of Lemma 5.  The source-faithful object is
`chen1973Lemma5M2Source` below. -/
def chen1973Lemma5M2InnerMajorant (x D : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (D + 1)).filter (fun l => Nat.Coprime l x ∧ Squarefree l),
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 *
      (3 : ℝ) ^ l.primeFactors.card / Nat.totient l *
      ‖∑ χ : PrimitiveCharacter l,
        if χ.1 = 1 then 0 else chen1973Lemma5PrimitiveTwist x l χ‖

/-- Legacy API retained for downstream files.  Semantically this is the
one-conductor inner majorant, not source `M₂`. -/
def chen1973Lemma5M2 (x D : ℕ) : ℝ :=
  chen1973Lemma5M2InnerMajorant x D

/-- The p. 119 outer squarefree-divisor carrier. -/
def chen1973Lemma5M2OuterDivisors (x D : ℕ) : Finset ℕ :=
  (Finset.Icc 2 D).filter fun d => Nat.Coprime d x ∧ Squarefree d

/-- The p. 119 outer weight `3^ν(d)|μ(d)|/φ(d)`. -/
def chen1973Lemma5M2OuterWeight (d : ℕ) : ℝ :=
  (3 : ℝ) ^ d.primeFactors.card *
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / Nat.totient d

/-- The literal primitive twist after retaining the source condition
`(p₁p₂,d)=1`.  The character conductor is the independent inner variable `l`. -/
def chen1973Lemma5PrimitiveTwistCoprime
    (x l d : ℕ) (χ : PrimitiveCharacter l) : ℂ :=
  star (χ.1 (x : ZMod l)) *
    ∑ pp ∈ (chen1973Lemma5PrimePairs x).filter
        (fun pp => Nat.Coprime (pp.1 * pp.2) d),
      ∑ n ∈ chen1973Lemma5NCarrier x pp,
        (chen1973Lemma5SmoothedWeight x pp n : ℂ) *
          χ.1 ((pp.1 * pp.2 * n : ℕ) : ZMod l)

/-- The inner conductor sum at a fixed outer divisor `d`. -/
def chen1973Lemma5M2SourceInner (x D d : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (D + 1)).filter (fun l => Nat.Coprime l x ∧ Squarefree l),
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 *
      (3 : ℝ) ^ l.primeFactors.card / Nat.totient l *
      ‖∑ χ : PrimitiveCharacter l,
        if χ.1 = 1 then 0 else chen1973Lemma5PrimitiveTwistCoprime x l d χ‖

/-- Source-faithful `M₂` on pp. 117--119: first the outer `d` weight, then the
independent inner conductor `l` primitive-character sum, with
`(p₁p₂,d)=1` inside the prime-pair carrier. -/
def chen1973Lemma5M2Source (x D : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma5M2OuterDivisors x D,
    chen1973Lemma5M2OuterWeight d * chen1973Lemma5M2SourceInner x D d

/-- Signed pre-norm form of the same two-layer source.  This is the exact finite
target for the Selberg/character expansion of the actual `M₄` remainder. -/
def chen1973Lemma5M2SourceSigned (x D : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma5M2OuterDivisors x D,
    chen1973Lemma5M2OuterWeight d *
      ∑ l ∈ (Finset.range (D + 1)).filter
          (fun l => Nat.Coprime l x ∧ Squarefree l),
        ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 *
          (3 : ℝ) ^ l.primeFactors.card / Nat.totient l *
          (∑ χ : PrimitiveCharacter l,
            if χ.1 = 1 then 0 else
              chen1973Lemma5PrimitiveTwistCoprime x l d χ).re

/-- The old one-conductor real-part ledger is bounded by its norm ledger. -/
theorem chen1973Lemma5M2Signed_le_M2 (x D : ℕ) :
    chen1973Lemma5M2Signed x D ≤ chen1973Lemma5M2 x D := by
  classical
  unfold chen1973Lemma5M2Signed chen1973Lemma5M2
    chen1973Lemma5M2InnerMajorant
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
  positivity

/-- Taking norms conductor-by-conductor bounds the signed two-layer source. -/
theorem chen1973Lemma5M2SourceSigned_le_source (x D : ℕ) :
    chen1973Lemma5M2SourceSigned x D ≤ chen1973Lemma5M2Source x D := by
  classical
  unfold chen1973Lemma5M2SourceSigned chen1973Lemma5M2Source
    chen1973Lemma5M2SourceInner
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro l hl
    apply mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    positivity
  · unfold chen1973Lemma5M2OuterWeight
    positivity

/-- Finite `M₄ ≤ M₂` connector with the correct source object.  The premise is
exactly the still-separate Selberg-coefficient/imprimitive-character expansion;
the norm step itself is proved here. -/
theorem chen1973Lemma5M4_le_M2_of_conductor_grouping
    {x z4 D : ℕ} {lambda : ℕ → ℝ}
    (hgroup : chen1973Lemma5M4 x z4 lambda ≤ chen1973Lemma5M2SourceSigned x D) :
    chen1973Lemma5M4 x z4 lambda ≤ chen1973Lemma5M2Source x D :=
  hgroup.trans (chen1973Lemma5M2SourceSigned_le_source x D)

/-- The preceding connector specialized to Chen's actual p. 115 Selberg
coefficient, making the link to the concrete `M₄` remainder explicit. -/
theorem chen1973Lemma5ActualM4_le_M2Source_of_character_expansion
    {x z4 R D : ℕ}
    (hexpand : chen1973Lemma5M4 x z4 (chen1973Lemma5SelbergLambda x R) ≤
      chen1973Lemma5M2SourceSigned x D) :
    chen1973Lemma5M4 x z4 (chen1973Lemma5SelbergLambda x R) ≤
      chen1973Lemma5M2Source x D :=
  chen1973Lemma5M4_le_M2_of_conductor_grouping hexpand

/-- Exact finite `M₁-M₃+M₄` decomposition of the expanded Selberg square. -/
theorem chen1973Lemma5_expanded_eq_M1_sub_M3_add_M4
    (x z4 : ℕ) (lambda : ℕ → ℝ) :
    (∑ d1 ∈ chen1973Lemma5DivisorCarrier x z4,
      ∑ d2 ∈ chen1973Lemma5DivisorCarrier x z4,
        lambda d1 * lambda d2 * chen1973Lemma5ProgressionTerm x d1 d2) =
      chen1973Lemma5M1 x z4 lambda - chen1973Lemma5M3 x z4 lambda +
        chen1973Lemma5M4 x z4 lambda := by
  classical
  unfold chen1973Lemma5M1 chen1973Lemma5M3 chen1973Lemma5M4
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d1 hd1
  apply Finset.sum_congr rfl
  intro d2 hd2
  rw [chen1973Lemma5PrincipalAll_eq_good_add_bad]
  ring

/-- Equation (5), now as a kernel-checked finite identity. -/
theorem chen1973Lemma5SelbergSquare_eq_M1_sub_M3_add_M4
    (x z4 : ℕ) (lambda : ℕ → ℝ) :
    chen1973Lemma5SelbergSquare x z4 lambda =
      chen1973Lemma5M1 x z4 lambda - chen1973Lemma5M3 x z4 lambda +
        chen1973Lemma5M4 x z4 lambda := by
  rw [chen1973Lemma5SelbergSquare_eq_expanded,
    chen1973Lemma5_expanded_eq_M1_sub_M3_add_M4]

/-- Equation (5) specialized to Chen's actual p. 115 Selberg coefficient. -/
theorem chen1973Lemma5ActualSelbergSquare_eq_M1_sub_M3_add_M4
    (x z4 R : ℕ) :
    chen1973Lemma5SelbergSquare x z4 (chen1973Lemma5SelbergLambda x R) =
      chen1973Lemma5M1 x z4 (chen1973Lemma5SelbergLambda x R) -
        chen1973Lemma5M3 x z4 (chen1973Lemma5SelbergLambda x R) +
          chen1973Lemma5M4 x z4 (chen1973Lemma5SelbergLambda x R) := by
  exact chen1973Lemma5SelbergSquare_eq_M1_sub_M3_add_M4 x z4
    (chen1973Lemma5SelbergLambda x R)

end AnalyticNumberTheory.LargeSieve
