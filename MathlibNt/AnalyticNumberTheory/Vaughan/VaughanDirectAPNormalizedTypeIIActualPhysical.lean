

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualDecomposition
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
 # Physical AP-normalized bounds for actual Vaughan Type-II shells

This file starts with the genuine collected hyperbolic-prefix maximum.  It applies
prefix-maximal large sieve row by row, sums the rows after paying the Möbius
energy, and only then uses Cauchy in primitive characters and moduli.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Primitive characters form a subtype of all characters, whose cardinality is
`φ(q)`.  This discharges the elementary cardinality side condition in direct
Cauchy estimates. -/
theorem card_primitiveCharacter_le_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq

/-- Double Cauchy for one actual collected shell.  The first Cauchy is over
primitive characters at fixed modulus; the second uses `q⁻¹/²`, producing the
exact `q/φ(q)` weight consumed by the prefix large sieve. -/
theorem apNormalizedVaughanActualCollectedShellMean_sq_le
    (N Q u v k l : ℕ) :
    apNormalizedVaughanActualCollectedShellMean N Q u v k l ^ 2 ≤
      conductorHarmonicFactor Q *
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) := by
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ
  let T : ℕ → ℝ := fun q => ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, Real.sqrt (F q χ)
  let Bq : ℕ → ℝ := fun q => ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q, F q χ
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :
      (q : ℝ) * T q ^ 2 ≤ Bq q := by
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hchars := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter q)))
      (f := fun χ => Real.sqrt (F q χ))
    have hsquares : (∑ χ : PrimitiveCharacter q, Real.sqrt (F q χ)) ^ 2 ≤
        (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, F q χ := by
      calc
        _ ≤ (Fintype.card (PrimitiveCharacter q) : ℝ) *
            ∑ χ : PrimitiveCharacter q, (Real.sqrt (F q χ)) ^ 2 := hchars
        _ ≤ (q.totient : ℝ) *
            ∑ χ : PrimitiveCharacter q, (Real.sqrt (F q χ)) ^ 2 := by
              gcongr
              exact_mod_cast card_primitiveCharacter_le_totient q hq0
        _ = (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, F q χ := by
              congr 1
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [Real.sq_sqrt]
              exact vaughanCanonicalCollectedPrefixMaxSquare_nonneg N u v k l q χ
    dsimp [T, Bq]
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedVaughanActualCollectedShellMean N Q u v k l =
      ∑ q ∈ Finset.Icc 1 Q,
        (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt (q : ℝ) * T q) := by
    unfold apNormalizedVaughanActualCollectedShellMean
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hsne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hq0
    dsimp [T, F]
    field_simp
  rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 Q)
    (fun q => (Real.sqrt (q : ℝ))⁻¹)
    (fun q => Real.sqrt (q : ℝ) * T q)).trans ?_
  have hfirst : (∑ q ∈ Finset.Icc 1 Q,
      (Real.sqrt (q : ℝ))⁻¹ ^ 2) = conductorHarmonicFactor Q := by
    unfold conductorHarmonicFactor
    apply Finset.sum_congr rfl
    intro q hq
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  rw [hfirst]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ q ∈ Finset.Icc 1 Q, (Real.sqrt (q : ℝ) * T q) ^ 2) ≤
          ∑ q ∈ Finset.Icc 1 Q, Bq q := by
            apply Finset.sum_le_sum
            intro q hq
            rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
            exact hT q hq
      _ = _ := rfl
  · exact conductorHarmonicFactor_nonneg Q

/-- Rowwise prefix-maximal large sieve, followed by Möbius energy and the
unconditional divisor-square tensor-energy estimate. -/
theorem apNormalizedVaughanActualCollectedShellMean_sq_le_rowPrefixEnergy
    (N Q u v k l : ℕ) (hQ : 0 < Q) :
    apNormalizedVaughanActualCollectedShellMean N Q u v k l ^ 2 ≤
      conductorHarmonicFactor Q *
        (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2 *
        ((N : ℝ) + ((2 ^ k : ℕ) : ℝ) *
          ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
            (Q : ℝ) ^ 2)) *
        (27 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)) := by
  refine (apNormalizedVaughanActualCollectedShellMean_sq_le N Q u v k l).trans ?_
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ) ≤
        ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            (vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
              (vaughanCanonicalDyadicBlock N u k) *
             vaughanCanonicalTensorPrefixMaxEnergy
              (fun _ => 1) N N u v k l q χ) := by
          gcongr with q hq χ hχ
          exact vaughanCanonicalCollectedPrefixMaxSquare_le_rowPrefixMax
            N u v k l q χ
      _ ≤ (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2 *
          ((N : ℝ) + ((2 ^ k : ℕ) : ℝ) *
            ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              (Q : ℝ) ^ 2)) *
          vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff
            (fun _ => 1) N N u v k l) :=
        weighted_primitive_vaughanCanonicalTensorPrefix_explicit
          (fun _ => 1) N N u v k l Q hQ
      _ ≤ (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2 *
          ((N : ℝ) + ((2 ^ k : ℕ) : ℝ) *
            ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              (Q : ℝ) ^ 2)) *
          (27 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)) := by
        gcongr
        rw [← vaughanBilinearTensorEnergy_canonical_eq_short]
        simpa using
          (vaughanBilinearTensorEnergy_canonical_le_BVScale_unconditional
            (fun _ => 1) N N u v k l 1 (by intro n hn; simp))
  · exact conductorHarmonicFactor_nonneg Q

/-- On an active rectangle, the lower `d` endpoint times `u+1` is at most
`2N`, provided the second Vaughan cutoff is at least the first.  The factor two
is exactly the price of the cutoff-truncated dyadic `e` shell. -/
theorem pow_mul_cutoff_succ_le_two_mul_of_active
    {N u v k l : ℕ} (huv : u ≤ v)
    (hkl : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    2 ^ k * (u + 1) ≤ 2 * N := by
  have hlbase : l ∈ vaughanCanonicalDyadicBases N v := by
    exact (Finset.mem_product.mp (mem_vaughanTypeIIActiveCanonicalRectangles.mp hkl).1).2
  obtain ⟨e, he, -⟩ := (mem_vaughanCanonicalDyadicBases_iff.mp hlbase)
  have hve : v < e := (mem_vaughanCanonicalDyadicBlock.mp he).2.2.1
  have heupper : e < 2 ^ (l + 1) := (vaughanCanonicalDyadicBlock_pow_bounds he).2
  have hcut : u + 1 ≤ 2 * 2 ^ l := by
    rw [Nat.pow_succ] at heupper
    omega
  have hactive := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hkl).2
  calc
    2 ^ k * (u + 1) ≤ 2 ^ k * (2 * 2 ^ l) := Nat.mul_le_mul_left _ hcut
    _ = 2 * (2 ^ k * 2 ^ l) := by ring
    _ ≤ 2 * N := Nat.mul_le_mul_left 2 hactive

/-- Explicit polylogarithmic payment for every actual Type-II shell. -/
def vaughanActualTypeIILogPay (N Q : ℕ) : ℝ :=
  Real.sqrt (27 * conductorHarmonicFactor Q *
    (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
    (1 + 2 * (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12)) *
    Real.log (N + 1 : ℕ) ^ 5)

lemma vaughanActualTypeIILogPay_nonneg (N Q : ℕ) :
    0 ≤ vaughanActualTypeIILogPay N Q := Real.sqrt_nonneg _

/-- Physical bound for a genuine hyperbolic shell.  Its proof uses the actual
collected-prefix square, row-prefix maximal large sieve, Möbius energy, and
only afterwards double Cauchy.  No shell estimate occurs among the premises. -/
theorem apNormalizedVaughanActualCollectedShellMean_physical
    (N Q u v k l : ℕ) (hQ : 0 < Q) (huv : u ≤ v)
    (hkl : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    apNormalizedVaughanActualCollectedShellMean N Q u v k l ≤
      vaughanActualTypeIILogPay N Q *
        ((N : ℝ) + (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ)) := by
  let D : ℝ := ((2 ^ k : ℕ) : ℝ)
  let C : ℝ := 2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12
  let U : ℝ := ((u + 1 : ℕ) : ℝ)
  let T : ℝ := (Q : ℝ) * N / Real.sqrt U

  let L : ℝ := Real.log (N + 1 : ℕ)
  let R : ℝ := vaughanActualTypeIILogPay N Q
  have hN : 0 < N := by
    have ha := (mem_vaughanTypeIIActiveCanonicalRectangles.mp hkl).2
    have : 0 < 2 ^ k * 2 ^ l := by positivity
    exact this.trans_le ha
  have hU : 0 < U := by dsimp [U]; positivity
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.2 hU
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  have hDNnat := pow_mul_cutoff_succ_le_two_mul_of_active huv hkl
  have hDN : D * U ≤ 2 * (N : ℝ) := by
    dsimp [D, U]
    exact_mod_cast hDNnat
  have hTid : T ^ 2 * U = (Q : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    dsimp [T]
    rw [div_pow, Real.sq_sqrt hU.le]
    field_simp
  have htail : D * (Q : ℝ) ^ 2 * (N : ℝ) ≤ 2 * T ^ 2 := by
    apply (mul_le_mul_iff_left₀ hU).mp
    calc
      (D * (Q : ℝ) ^ 2 * (N : ℝ)) * U =
          (D * U) * ((Q : ℝ) ^ 2 * (N : ℝ)) := by ring
      _ ≤ (2 * (N : ℝ)) * ((Q : ℝ) ^ 2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hDN (by positivity)
      _ = (2 * T ^ 2) * U := by rw [mul_assoc 2 (T ^ 2) U, hTid]; ring
  have hpoly :
      ((N : ℝ) + D * (C * (Q : ℝ) ^ 2)) * (N : ℝ) ≤
        (1 + 2 * C) * ((N : ℝ) + T) ^ 2 := by
    have hNsq : (N : ℝ) ^ 2 ≤ ((N : ℝ) + T) ^ 2 := by
      gcongr
      exact le_add_of_nonneg_right hT
    have hTsq : T ^ 2 ≤ ((N : ℝ) + T) ^ 2 := by
      gcongr
      exact le_add_of_nonneg_left (Nat.cast_nonneg N)
    calc
      _ = (N : ℝ) ^ 2 + C * (D * (Q : ℝ) ^ 2 * (N : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ 2 + 2 * C * T ^ 2 := by
        simpa only [mul_left_comm, mul_assoc] using
          add_le_add_right (mul_le_mul_of_nonneg_left htail hC) ((N : ℝ) ^ 2)
      _ ≤ ((N : ℝ) + T) ^ 2 + 2 * C * ((N : ℝ) + T) ^ 2 :=
        add_le_add hNsq (mul_le_mul_of_nonneg_left hTsq (by positivity))
      _ = _ := by ring
  have hlen : vaughanCanonicalTensorLength N k ≤ N :=
    Nat.div_le_self N (2 ^ k)
  have hlog2nat : Nat.log2 (vaughanCanonicalTensorLength N k) ≤ Nat.log2 N := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right hlen
  have hlog2 :
      (((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2) ≤
        (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) := by
    gcongr
  have hsquare := apNormalizedVaughanActualCollectedShellMean_sq_le_rowPrefixEnergy
    N Q u v k l hQ
  have hsqR : R ^ 2 = 27 * conductorHarmonicFactor Q *
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * (1 + 2 * C) * L ^ 5 := by
    dsimp [R, vaughanActualTypeIILogPay, C, L]
    rw [Real.sq_sqrt]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (conductorHarmonicFactor_nonneg Q))
          (sq_nonneg _))
        (by positivity))
      (pow_nonneg hL 5)
  have hledger :
      apNormalizedVaughanActualCollectedShellMean N Q u v k l ^ 2 ≤
        R ^ 2 * ((N : ℝ) + T) ^ 2 := by
    rw [hsqR]
    calc
      _ ≤ conductorHarmonicFactor Q *
          ((((Nat.log2 (vaughanCanonicalTensorLength N k) + 1 : ℕ) : ℝ) ^ 2) *
          ((N : ℝ) + D * (C * (Q : ℝ) ^ 2)) *
          (27 * (N : ℝ) * L ^ 5)) := by simpa [D, C, L] using hsquare
      _ ≤ conductorHarmonicFactor Q *
          ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
          ((N : ℝ) + D * (C * (Q : ℝ) ^ 2)) *
          (27 * (N : ℝ) * L ^ 5)) := by
            gcongr
            exact conductorHarmonicFactor_nonneg Q
      _ ≤ 27 * conductorHarmonicFactor Q *
          (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * (1 + 2 * C) * L ^ 5 *
          ((N : ℝ) + T) ^ 2 := by
            have hfac : 0 ≤ conductorHarmonicFactor Q *
                (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * 27 * L ^ 5 := by
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg (conductorHarmonicFactor_nonneg Q) (sq_nonneg _))
                  (by positivity))
                (pow_nonneg hL 5)
            calc
              _ = (conductorHarmonicFactor Q *
                  (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * 27 * L ^ 5) *
                  (((N : ℝ) + D * (C * (Q : ℝ) ^ 2)) * (N : ℝ)) := by ring
              _ ≤ (conductorHarmonicFactor Q *
                  (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * 27 * L ^ 5) *
                  ((1 + 2 * C) * ((N : ℝ) + T) ^ 2) :=
                    mul_le_mul_of_nonneg_left hpoly hfac
              _ = _ := by ring
  have hmean0 := apNormalizedVaughanActualCollectedShellMean_nonneg N Q u v k l
  have hRT0 : 0 ≤ R * ((N : ℝ) + T) := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hmean : apNormalizedVaughanActualCollectedShellMean N Q u v k l ≤
      R * ((N : ℝ) + T) := by
    apply (sq_le_sq₀ hmean0 hRT0).mp
    simpa [mul_pow] using hledger
  calc
    apNormalizedVaughanActualCollectedShellMean N Q u v k l ≤
        R * ((N : ℝ) + T) := hmean
    _ = _ := by rfl

/-- Unconditional analytic Type-II input: all shell estimates are produced in
this module.  The only parameter relation is the standard Vaughan choice
`u ≤ v`; there is no per-shell premise. -/
theorem vaughanDirectAPNormalizedTypeIIInput_unconditional
    (N Q u v : ℕ) (hQ : 0 < Q) (huv : u ≤ v) :
    VaughanDirectAPNormalizedTypeIIInput N Q u v
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ)
      (vaughanActualTypeIILogPay N Q) := by
  apply vaughanDirectAPNormalizedTypeIIInput_of_actual_collected_shells
  intro kl hkl
  exact apNormalizedVaughanActualCollectedShellMean_physical
    N Q u v kl.1 kl.2 hQ huv hkl

end

end AnalyticNumberTheory.LargeSieve
