

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.BilinearTensorPrefixMaximalExplicit

/-!
 # AP-normalized direct Type-II bilinear shells

The direct mean is formed before squaring.  Cauchy is first taken over primitive
characters and then over moduli with the outer weight `q⁻¹/²`; hence the square
side has exactly the `q / φ(q)` weight accepted by the bilinear tensor large
sieve.  The canonical `(d,t)` tensor prefix remains intact throughout.

The resulting square scale on a `d`-shell is

`H * RM² * D * (M + c(Q)Q²) * E(D,M)`.

For the actual tensor energy `E(D,M) ≪ D M log⁵`, taking the square root gives
`D M + sqrt(c(Q)) Q sqrt(D * D M)`, rather than another unsquared factor `D M`.
Thus the existing second moment is sufficient for the direct shell.  The final
theorem below only aggregates already-physical shell bounds; it does not freeze
a Type-II conclusion as a new analytic premise.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The unsquared AP-normalized mean of one actual canonical `(d,t)` tensor
prefix.  The maximum in `t` is inside each primitive-character summand. -/
def apNormalizedVaughanCanonicalBilinearShellMean
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalBilinearPrefixMaxSquare
        b y N u v k l q χ)


/-- The correct double Cauchy inequality for a direct bilinear shell.  Character
Cauchy is local to each modulus; modulus Cauchy uses `q⁻¹/²`.  Consequently no
cardinality factor for the modulus interval and no second tensor energy appear. -/
theorem apNormalizedVaughanCanonicalBilinearShellMean_sq_le
    (b : ℕ → ℂ) (y N u v k l Q : ℕ)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanCanonicalBilinearShellMean b y N u v k l Q ^ 2 ≤
      conductorHarmonicFactor Q *
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalBilinearPrefixMaxSquare
              b y N u v k l q χ) := by
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ
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
              exact_mod_cast hcard q hq
        _ = (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, F q χ := by
              congr 1
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [Real.sq_sqrt]
              exact bilinearTensorCharacterPrefixMaxSquare_nonneg _ _ _ _ _
    dsimp [T, Bq]
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedVaughanCanonicalBilinearShellMean
      b y N u v k l Q =
      ∑ q ∈ Finset.Icc 1 Q,
        (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt (q : ℝ) * T q) := by
    unfold apNormalizedVaughanCanonicalBilinearShellMean
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
      _ = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ := by
            rfl
  · exact conductorHarmonicFactor_nonneg Q




/-- Honest final wiring: once the exact canonical shell decomposition and its
physical bounds have been proved, their finite sum inhabits the existing
AP-normalized Type-II input.  No Type-II estimate is assumed under another name. -/
theorem vaughanDirectAPNormalizedTypeIIInput_of_bilinear_shells
    {ι : Type*} [DecidableEq ι]
    (shells : Finset ι) (shellMean : ι → ℝ)
    (N Q u v : ℕ) (logPay : ℝ)
    (hdecomp : apNormalizedVaughanTypeIIMean N Q u v ≤
      ∑ s ∈ shells, shellMean s)
    (hshell : ∀ s ∈ shells, shellMean s ≤ logPay *
      ((N : ℝ) + (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))) :
    VaughanDirectAPNormalizedTypeIIInput N Q u v
      (shells.card : ℝ) logPay := by
  unfold VaughanDirectAPNormalizedTypeIIInput
  let X : ℝ := (N : ℝ) + (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ)
  calc
    apNormalizedVaughanTypeIIMean N Q u v ≤ ∑ s ∈ shells, shellMean s := hdecomp
    _ ≤ ∑ _s ∈ shells, logPay * X := by
      apply Finset.sum_le_sum
      intro s hs
      exact hshell s hs
    _ = (shells.card : ℝ) * logPay * X := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end

end AnalyticNumberTheory.LargeSieve
