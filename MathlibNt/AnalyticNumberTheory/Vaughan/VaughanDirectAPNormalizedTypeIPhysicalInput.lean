

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedAssembly
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongVariablePrimitiveMaximal

/-!
 # AP-normalized Vaughan Type-I shell input

This file isolates the weighted Cauchy step needed by the physical Type-I
argument.  In particular, Cauchy in the modulus variable is weighted by
`q^{-1/2}`.  The resulting first factor is the harmonic conductor ledger, not
the cardinality of the modulus interval.  Every row on the square side keeps
its own length, so this module never forms a length-`N` global coefficient
moment.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- An AP-normalized shell of long rows with their literal short coefficients. -/
def apNormalizedWeightedRowShellMean
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ)
    (c : ι → ℤ → ℂ) (L : ι → ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
      ‖w r‖ * Real.sqrt
        (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)

/-- Literal square energy of the short coefficients in one shell. -/
def rowShellShortEnergy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ) : ℝ :=
  ∑ r ∈ S, ‖w r‖ ^ 2

lemma apNormalizedWeightedRowShellMean_nonneg
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ)
    (c : ι → ℤ → ℂ) (L : ι → ℕ) (Q : ℕ) :
    0 ≤ apNormalizedWeightedRowShellMean S w c L Q := by
  unfold apNormalizedWeightedRowShellMean
  positivity

lemma rowShellShortEnergy_nonneg
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ) :
    0 ≤ rowShellShortEnergy S w := by
  unfold rowShellShortEnergy
  positivity

/-- Weighted Cauchy, first over primitive characters and then over the rows,
with the *correct* `q^{-1/2}` outer weight.  The square ledger on the right has
exactly the `q / φ(q)` weight consumed by the primitive large sieve. -/
theorem apNormalizedWeightedRowShellMean_sq_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ)
    (c : ι → ℤ → ℂ) (L : ι → ℕ) (Q : ℕ)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedWeightedRowShellMean S w c L Q ^ 2 ≤
      conductorHarmonicFactor Q * rowShellShortEnergy S w *
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) := by
  let T : ℕ → ℝ := fun q => ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
      ‖w r‖ * Real.sqrt
        (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)
  let B : ℕ → ℝ := fun q => ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
      primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ
  let E : ℝ := rowShellShortEnergy S w
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :
      (q : ℝ) * T q ^ 2 ≤ E * B q := by
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    let A : PrimitiveCharacter q → ℝ := fun χ => ∑ r ∈ S,
      ‖w r‖ * Real.sqrt
        (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ)
    have hchars := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter q))) (f := A)
    have hrows (χ : PrimitiveCharacter q) : A χ ^ 2 ≤
        E * ∑ r ∈ S,
          primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
      have hr := Finset.sum_mul_sq_le_sq_mul_sq S
        (fun r => ‖w r‖)
        (fun r => Real.sqrt
          (primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ))
      simpa only [A, E, rowShellShortEnergy,
        Real.sq_sqrt (primitiveCharacterPrefixMaxSquare_nonneg ..)] using hr
    have hsq : (∑ χ : PrimitiveCharacter q, A χ) ^ 2 ≤
        (q.totient : ℝ) * E *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
      calc
        _ ≤ (Fintype.card (PrimitiveCharacter q) : ℝ) * ∑ χ, A χ ^ 2 := hchars
        _ ≤ (q.totient : ℝ) * ∑ χ, A χ ^ 2 := by
          gcongr
          exact_mod_cast hcard q hq
        _ ≤ (q.totient : ℝ) * ∑ χ,
              (E * ∑ r ∈ S,
                primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) := by
          gcongr with χ
          exact hrows χ
        _ = _ := by
          simp_rw [Finset.mul_sum]
          ring
    dsimp [T, B]
    change (q : ℝ) * (((q.totient : ℝ)⁻¹) * ∑ χ, A χ) ^ 2 ≤ _
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedWeightedRowShellMean S w c L Q =
      ∑ q ∈ Finset.Icc 1 Q,
        (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt (q : ℝ) * T q) := by
    unfold apNormalizedWeightedRowShellMean
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hsne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hq0
    dsimp [T]
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
  calc
    conductorHarmonicFactor Q *
        ∑ q ∈ Finset.Icc 1 Q, (Real.sqrt (q : ℝ) * T q) ^ 2
      ≤ conductorHarmonicFactor Q *
          ∑ q ∈ Finset.Icc 1 Q, E * B q := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro q hq
          rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
          exact hT q hq
        · exact conductorHarmonicFactor_nonneg Q
    _ = conductorHarmonicFactor Q * E *
          (∑ q ∈ Finset.Icc 1 Q, B q) := by
        simp_rw [Finset.mul_sum]
        ring
    _ = _ := by rfl

/-- The previous shell square estimate with the variable-length primitive
maximal large sieve inserted.  This is the no-global-moment producer. -/
theorem apNormalizedWeightedRowShellMean_sq_le_budget
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ)
    (c : ι → ℤ → ℂ) (L : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedWeightedRowShellMean S w c L Q ^ 2 ≤
      conductorHarmonicFactor Q * rowShellShortEnergy S w *
        variableLengthPrimitivePrefixBudget S c L Q := by
  refine (apNormalizedWeightedRowShellMean_sq_le S w c L Q hcard).trans ?_
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ∑ r ∈ S,
            primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ) =
        ∑ r ∈ S, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              primitiveCharacterPrefixMaxSquare (c r) 0 (L r) q χ := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
      _ ≤ variableLengthPrimitivePrefixBudget S c L Q :=
        weighted_primitive_variableLength_prefix_maximal S c L Q hQ
  · exact mul_nonneg (conductorHarmonicFactor_nonneg Q)
      (rowShellShortEnergy_nonneg S w)

/-! ## The two literal Vaughan Type-I lanes -/

/-- One `d`-shell in the first (`μ * log`) lane.  Its row has the physical
length `N / d`; no coefficient is collected back at ambient length `N`. -/
def apNormalizedVaughanTypeIFirstShellMean
    (DS : Finset ℕ) (N Q : ℕ) : ℝ :=
  apNormalizedWeightedRowShellMean DS
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (vaughanTypeIFirstRowCoeff fun _ => 1)
    (vaughanTypeIFirstRowLength N) Q

/-- One `(d,e)`-shell in the middle (`μ * Λ`) lane.  Its row has the physical
length `N / (d*e)`. -/
def apNormalizedVaughanTypeIMiddleShellMean
    (DS ES : Finset ℕ) (N Q : ℕ) : ℝ :=
  apNormalizedWeightedRowShellMean (DS ×ˢ ES)
    (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))
    (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
    (vaughanTypeIMiddlePairRowLength N) Q

theorem apNormalizedVaughanTypeIFirstShellMean_sq_le_budget
    (DS : Finset ℕ) (N Q : ℕ) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanTypeIFirstShellMean DS N Q ^ 2 ≤
      conductorHarmonicFactor Q * vaughanTypeIFirstShortEnergy DS *
        variableLengthPrimitivePrefixBudget DS
          (vaughanTypeIFirstRowCoeff fun _ => 1)
          (vaughanTypeIFirstRowLength N) Q := by
  simpa [apNormalizedVaughanTypeIFirstShellMean,
    rowShellShortEnergy, vaughanTypeIFirstShortEnergy] using
    apNormalizedWeightedRowShellMean_sq_le_budget DS
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))
      (vaughanTypeIFirstRowCoeff fun _ => 1)
      (vaughanTypeIFirstRowLength N) Q hQ hcard

theorem apNormalizedVaughanTypeIMiddleShellMean_sq_le_budget
    (DS ES : Finset ℕ) (N Q : ℕ) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanTypeIMiddleShellMean DS ES N Q ^ 2 ≤
      conductorHarmonicFactor Q *
        rowShellShortEnergy (DS ×ˢ ES)
          (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
            (ArithmeticFunction.vonMangoldt de.2 : ℂ)) *
        variableLengthPrimitivePrefixBudget (DS ×ˢ ES)
          (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
          (vaughanTypeIMiddlePairRowLength N) Q := by
  simpa [apNormalizedVaughanTypeIMiddleShellMean] using
    apNormalizedWeightedRowShellMean_sq_le_budget (DS ×ˢ ES)
      (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
        (ArithmeticFunction.vonMangoldt de.2 : ℂ))
      (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
      (vaughanTypeIMiddlePairRowLength N) Q hQ hcard

/-- Scalar optimization used on each dyadic short-variable shell.  Reopening
the square ledger gives the exact short-scale term `Q * sqrt (N*D)`.  The older
`Q²*sqrt N` is only what results after the lossy substitution `D ≤ Q²`; it is
not intrinsic to double Cauchy. -/
theorem apNormalized_typeI_shell_physical
    (shellMean H E B D W R C N Q : ℝ)
    (hmean : 0 ≤ shellMean) (hH : 0 ≤ H) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hD : 0 < D) (hW : 0 ≤ W) (hR : 0 ≤ R) (hC : 1 ≤ C)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hsq : shellMean ^ 2 ≤ H * E * B)
    (henergy : E ≤ D * W ^ 2)
    (hrow : D * B ≤ R ^ 2 * (N ^ 2 + C * Q ^ 2 * N * D)) :
    shellMean ≤ W * R * Real.sqrt (H * C) *
      (N + Q * Real.sqrt (N * D)) := by
  have hHC : 0 ≤ H * C := mul_nonneg hH (le_trans (by norm_num) hC)
  have hND : 0 ≤ N * D := mul_nonneg hN hD.le
  have hsND : (Real.sqrt (N * D)) ^ 2 = N * D := Real.sq_sqrt hND
  have hcancel : E * B ≤ W ^ 2 * R ^ 2 *
      (N ^ 2 + C * Q ^ 2 * N * D) := by
    calc
      E * B ≤ (D * W ^ 2) * B := mul_le_mul_of_nonneg_right henergy hB
      _ = W ^ 2 * (D * B) := by ring
      _ ≤ W ^ 2 * (R ^ 2 * (N ^ 2 + C * Q ^ 2 * N * D)) :=
        mul_le_mul_of_nonneg_left hrow (sq_nonneg W)
      _ = _ := by ring
  have hinside : N ^ 2 + C * Q ^ 2 * N * D ≤
      C * (N + Q * Real.sqrt (N * D)) ^ 2 := by
    have hN2C : N ^ 2 ≤ C * N ^ 2 := by nlinarith [sq_nonneg N]
    have hcross : 0 ≤ 2 * N * Q * Real.sqrt (N * D) := by positivity
    have hexpand : (N + Q * Real.sqrt (N * D)) ^ 2 =
        N ^ 2 + 2 * N * Q * Real.sqrt (N * D) + Q ^ 2 * N * D := by
      calc
        _ = N ^ 2 + 2 * N * Q * Real.sqrt (N * D) +
            Q ^ 2 * (Real.sqrt (N * D)) ^ 2 := by ring
        _ = _ := by rw [hsND]; ring
    rw [hexpand]
    nlinarith
  have hsquare : shellMean ^ 2 ≤
      (W * R * Real.sqrt (H * C) *
        (N + Q * Real.sqrt (N * D))) ^ 2 := by
    calc
      shellMean ^ 2 ≤ H * E * B := hsq
      _ = H * (E * B) := by ring
      _ ≤ H * (W ^ 2 * R ^ 2 *
          (N ^ 2 + C * Q ^ 2 * N * D)) :=
        mul_le_mul_of_nonneg_left hcancel hH
      _ ≤ H * (W ^ 2 * R ^ 2 *
          (C * (N + Q * Real.sqrt (N * D)) ^ 2)) := by gcongr
      _ = (W * R * Real.sqrt (H * C) *
          (N + Q * Real.sqrt (N * D))) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hHC]
        ring
  have htarget : 0 ≤ W * R * Real.sqrt (H * C) *
      (N + Q * Real.sqrt (N * D)) := by positivity
  exact (sq_le_sq₀ hmean htarget).mp hsquare

/-- Finite shell aggregation.  This is the final wiring theorem used after the
first lane (`d` shells) and middle lane (`(d,e)` shells) have separately been
expanded.  It records the explicit constant `K = #first shells + #middle
shells`; the common `logPay` contains the RM, coefficient, harmonic, and
large-sieve logarithmic payments supplied by the shell estimates. -/
theorem vaughanDirectAPNormalizedTypeIInput_of_shells
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (firstShells : Finset α) (middleShells : Finset β)
    (firstMean : α → ℝ) (middleMean : β → ℝ)
    (N Q u v : ℕ) (logPay : ℝ)
    (hlog : 0 ≤ logPay)
    (hdecomp : apNormalizedVaughanTypeIMean N Q u v ≤
      (∑ s ∈ firstShells, firstMean s) +
        ∑ s ∈ middleShells, middleMean s)
    (hfirst : ∀ s ∈ firstShells,
      firstMean s ≤ logPay *
        ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N))
    (hmiddle : ∀ s ∈ middleShells,
      middleMean s ≤ logPay *
        ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N)) :
    VaughanDirectAPNormalizedTypeIInput N Q u v
      ((firstShells.card + middleShells.card : ℕ) : ℝ) logPay := by
  unfold VaughanDirectAPNormalizedTypeIInput
  let X : ℝ := (N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N
  calc
    apNormalizedVaughanTypeIMean N Q u v ≤
        (∑ s ∈ firstShells, firstMean s) +
          ∑ s ∈ middleShells, middleMean s := hdecomp
    _ ≤ (∑ _s ∈ firstShells, logPay * X) +
          ∑ _s ∈ middleShells, logPay * X := by
        exact add_le_add (Finset.sum_le_sum hfirst) (Finset.sum_le_sum hmiddle)
    _ = ((firstShells.card + middleShells.card : ℕ) : ℝ) * logPay * X := by
        simp [X]
        ring

end

end AnalyticNumberTheory.LargeSieve
