

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIPhysicalInput

/-!
 # Actual dyadic partition for the AP-normalized Vaughan Type-I mean
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Dyadic first-lane shell: positive `d ≤ u` with `log₂ d = k`. -/
def vaughanTypeIFirstDyadicShell (u k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 u).filter fun d => Nat.log2 d = k

/-- Dyadic product shell in the middle lane.  It partitions by the actual short
product `d*e`, rather than by an ambient rectangle. -/
def vaughanTypeIMiddleProductDyadicShell (u v k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 u) ×ˢ (Finset.Icc 1 v)).filter fun de =>
    Nat.log2 (de.1 * de.2) = k

@[simp] theorem mem_vaughanTypeIFirstDyadicShell {u k d : ℕ} :
    d ∈ vaughanTypeIFirstDyadicShell u k ↔
      0 < d ∧ d ≤ u ∧ Nat.log2 d = k := by
  simp only [vaughanTypeIFirstDyadicShell, Finset.mem_filter, Finset.mem_Icc,
    Nat.succ_le_iff]
  tauto

@[simp] theorem mem_vaughanTypeIMiddleProductDyadicShell {u v k d e : ℕ} :
    (d, e) ∈ vaughanTypeIMiddleProductDyadicShell u v k ↔
      0 < d ∧ d ≤ u ∧ 0 < e ∧ e ≤ v ∧ Nat.log2 (d * e) = k := by
  simp only [vaughanTypeIMiddleProductDyadicShell, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc, Nat.succ_le_iff]
  tauto

/-- A first shell really is contained in `[2^k,2^(k+1))`. -/
theorem vaughanTypeIFirstDyadicShell_bounds {u k d : ℕ}
    (hd : d ∈ vaughanTypeIFirstDyadicShell u k) :
    2 ^ k ≤ d ∧ d < 2 ^ (k + 1) := by
  have h := mem_vaughanTypeIFirstDyadicShell.mp hd
  rw [← h.2.2]
  exact ⟨(Nat.le_log2 (Nat.ne_of_gt h.1)).mp le_rfl, Nat.lt_log2_self⟩

/-- A middle shell has the corresponding bounds on the actual product. -/
theorem vaughanTypeIMiddleProductDyadicShell_bounds {u v k d e : ℕ}
    (hde : (d, e) ∈ vaughanTypeIMiddleProductDyadicShell u v k) :
    2 ^ k ≤ d * e ∧ d * e < 2 ^ (k + 1) := by
  have h := mem_vaughanTypeIMiddleProductDyadicShell.mp hde
  rw [← h.2.2.2.2]
  have hp : 0 < d * e := Nat.mul_pos h.1 h.2.2.1
  exact ⟨(Nat.le_log2 (Nat.ne_of_gt hp)).mp le_rfl, Nat.lt_log2_self⟩

/-- Every positive `d ≤ u` occurs in its actual dyadic shell. -/
theorem mem_own_vaughanTypeIFirstDyadicShell {u d : ℕ}
    (hd : 0 < d) (hdu : d ≤ u) :
    d ∈ vaughanTypeIFirstDyadicShell u (Nat.log2 d) := by
  exact mem_vaughanTypeIFirstDyadicShell.mpr ⟨hd, hdu, rfl⟩

/-- Every positive pair in the Vaughan rectangle occurs in its product shell. -/
theorem mem_own_vaughanTypeIMiddleProductDyadicShell {u v d e : ℕ}
    (hd : 0 < d) (hdu : d ≤ u) (he : 0 < e) (hev : e ≤ v) :
    (d, e) ∈ vaughanTypeIMiddleProductDyadicShell u v (Nat.log2 (d * e)) := by
  exact mem_vaughanTypeIMiddleProductDyadicShell.mpr ⟨hd, hdu, he, hev, rfl⟩

/-- The shell index of a nonempty first shell lies in the advertised range. -/
theorem firstDyadicShell_index_lt {u k d : ℕ}
    (hd : d ∈ vaughanTypeIFirstDyadicShell u k) : k < Nat.log2 u + 1 := by
  have h := mem_vaughanTypeIFirstDyadicShell.mp hd
  have hu : u ≠ 0 := Nat.ne_of_gt (h.1.trans_le h.2.1)
  have hpow : 2 ^ k ≤ u := (vaughanTypeIFirstDyadicShell_bounds hd).1.trans h.2.1
  exact Nat.lt_succ_iff.mpr ((Nat.le_log2 hu).mpr hpow)

/-- The shell index of a nonempty product shell lies in the advertised range. -/
theorem middleProductDyadicShell_index_lt {u v k d e : ℕ}
    (hde : (d, e) ∈ vaughanTypeIMiddleProductDyadicShell u v k) :
    k < Nat.log2 (u * v) + 1 := by
  have h := mem_vaughanTypeIMiddleProductDyadicShell.mp hde
  have hp : 0 < d * e := Nat.mul_pos h.1 h.2.2.1
  have huv : u * v ≠ 0 := Nat.ne_of_gt
    (Nat.mul_pos (h.1.trans_le h.2.1) (h.2.2.1.trans_le h.2.2.2.1))
  have hprod : d * e ≤ u * v := Nat.mul_le_mul h.2.1 h.2.2.2.1
  have hpow : 2 ^ k ≤ u * v :=
    (vaughanTypeIMiddleProductDyadicShell_bounds hde).1.trans hprod
  exact Nat.lt_succ_iff.mpr ((Nat.le_log2 huv).mpr hpow)

/-- Literal AP-normalized mean of one middle product shell. -/
def apNormalizedVaughanTypeIMiddleProductShellMean
    (S : Finset (ℕ × ℕ)) (N Q : ℕ) : ℝ :=
  apNormalizedWeightedRowShellMean S
    (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))
    (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
    (vaughanTypeIMiddlePairRowLength N) Q

/-- The exact physical payment attached to a first shell.  This deliberately
spells out the two literal ledgers; no global length-`N` moment is substituted. -/
def vaughanTypeIFirstDyadicLogPay (u k N Q : ℕ) : ℝ :=
  let S := vaughanTypeIFirstDyadicShell u k
  Real.sqrt (rowShellShortEnergy S
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))) *
    Real.sqrt (((2 ^ k : ℕ) : ℝ) *
      variableLengthPrimitivePrefixBudget S
        (vaughanTypeIFirstRowCoeff fun _ => 1)
        (vaughanTypeIFirstRowLength N) Q) *
    Real.sqrt (conductorHarmonicFactor Q)

/-- The analogous honest product-shell payment. -/
def vaughanTypeIMiddleProductDyadicLogPay (u v k N Q : ℕ) : ℝ :=
  let S := vaughanTypeIMiddleProductDyadicShell u v k
  Real.sqrt (rowShellShortEnergy S
      (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
        (ArithmeticFunction.vonMangoldt de.2 : ℂ))) *
    Real.sqrt (((2 ^ k : ℕ) : ℝ) *
      variableLengthPrimitivePrefixBudget S
        (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
        (vaughanTypeIMiddlePairRowLength N) Q) *
    Real.sqrt (conductorHarmonicFactor Q)

private theorem shell_physical_with_literal_ledgers
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℂ)
    (c : ι → ℤ → ℂ) (L : ι → ℕ) (D N Q : ℕ)
    (hN : 0 < N) (hD : 0 < D)
    (hmean : apNormalizedWeightedRowShellMean S w c L Q ^ 2 ≤
      conductorHarmonicFactor Q * rowShellShortEnergy S w *
        variableLengthPrimitivePrefixBudget S c L Q) :
    apNormalizedWeightedRowShellMean S w c L Q ≤
      Real.sqrt (rowShellShortEnergy S w) *
        Real.sqrt ((D : ℝ) * variableLengthPrimitivePrefixBudget S c L Q) *
        Real.sqrt (conductorHarmonicFactor Q) *
        ((N : ℝ) + (Q : ℝ) * Real.sqrt ((N : ℝ) * D)) := by
  let E := rowShellShortEnergy S w
  let B := variableLengthPrimitivePrefixBudget S c L Q
  have hE : 0 ≤ E := rowShellShortEnergy_nonneg S w
  have hB : 0 ≤ B := by
    unfold B variableLengthPrimitivePrefixBudget
    apply Finset.sum_nonneg
    intro r hr
    unfold primitiveLargeSieveConstant
    positivity
  have hDB : 0 ≤ (D : ℝ) * B := mul_nonneg (by positivity) hB
  have henergy : E ≤ (D : ℝ) * (Real.sqrt E) ^ 2 := by
    rw [Real.sq_sqrt hE]
    nlinarith [show (1 : ℝ) ≤ D by exact_mod_cast hD]
  have hrow : (D : ℝ) * B ≤ (Real.sqrt ((D : ℝ) * B)) ^ 2 *
      ((N : ℝ) ^ 2 + 1 * (Q : ℝ) ^ 2 * N * D) := by
    rw [Real.sq_sqrt hDB]
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : 1 ≤ (N : ℝ) ^ 2 + 1 * (Q : ℝ) ^ 2 * N * D := by
      nlinarith [sq_nonneg (N : ℝ), mul_nonneg
        (mul_nonneg (sq_nonneg (Q : ℝ)) (by positivity : (0 : ℝ) ≤ N))
        (by positivity : (0 : ℝ) ≤ D)]
    exact le_mul_of_one_le_right hDB hx
  simpa [E, B, mul_assoc] using
    apNormalized_typeI_shell_physical
      (apNormalizedWeightedRowShellMean S w c L Q)
      (conductorHarmonicFactor Q) E B D (Real.sqrt E)
      (Real.sqrt ((D : ℝ) * B)) 1 N Q
      (apNormalizedWeightedRowShellMean_nonneg S w c L Q)
      (conductorHarmonicFactor_nonneg Q) hE hB (by exact_mod_cast hD)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by norm_num)
      (by positivity) (by positivity) hmean henergy hrow

/-- Every first shell meets the existing physical lemma with its literal energy
and variable-length budget. -/
theorem apNormalizedVaughanTypeIFirstDyadicShell_physical
    (u k N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanTypeIFirstShellMean
        (vaughanTypeIFirstDyadicShell u k) N Q ≤
      vaughanTypeIFirstDyadicLogPay u k N Q *
        ((N : ℝ) + (Q : ℝ) *
          Real.sqrt ((N : ℝ) * (2 ^ k : ℕ))) := by
  apply shell_physical_with_literal_ledgers
    (vaughanTypeIFirstDyadicShell u k)
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (vaughanTypeIFirstRowCoeff fun _ => 1)
    (vaughanTypeIFirstRowLength N) (2 ^ k) N Q hN (by positivity)
  simpa [apNormalizedVaughanTypeIFirstShellMean,
    rowShellShortEnergy, vaughanTypeIFirstShortEnergy, mul_assoc] using
    apNormalizedVaughanTypeIFirstShellMean_sq_le_budget
      (vaughanTypeIFirstDyadicShell u k) N Q hQ hcard

/-- Every middle product shell meets the same physical lemma. -/
theorem apNormalizedVaughanTypeIMiddleProductDyadicShell_physical
    (u v k N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanTypeIMiddleProductShellMean
        (vaughanTypeIMiddleProductDyadicShell u v k) N Q ≤
      vaughanTypeIMiddleProductDyadicLogPay u v k N Q *
        ((N : ℝ) + (Q : ℝ) *
          Real.sqrt ((N : ℝ) * (2 ^ k : ℕ))) := by
  let S := vaughanTypeIMiddleProductDyadicShell u v k
  apply shell_physical_with_literal_ledgers S
    (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))
    (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
    (vaughanTypeIMiddlePairRowLength N) (2 ^ k) N Q hN (by positivity)
  simpa [apNormalizedVaughanTypeIMiddleProductShellMean, S] using
    apNormalizedWeightedRowShellMean_sq_le_budget S
      (fun de => ((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
        (ArithmeticFunction.vonMangoldt de.2 : ℂ))
      (vaughanTypeIMiddlePairRowCoeff fun _ => 1)
      (vaughanTypeIMiddlePairRowLength N) Q hQ hcard

/-- Explicit common payment used by the finite shell assembler. -/
def vaughanTypeIActualDyadicLogPay (N Q u v : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (Nat.log2 u + 1),
      vaughanTypeIFirstDyadicLogPay u k N Q) +
    ∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
      vaughanTypeIMiddleProductDyadicLogPay u v k N Q

lemma vaughanTypeIFirstDyadicLogPay_nonneg (u k N Q : ℕ) :
    0 ≤ vaughanTypeIFirstDyadicLogPay u k N Q := by
  unfold vaughanTypeIFirstDyadicLogPay
  positivity

lemma vaughanTypeIMiddleProductDyadicLogPay_nonneg (u v k N Q : ℕ) :
    0 ≤ vaughanTypeIMiddleProductDyadicLogPay u v k N Q := by
  unfold vaughanTypeIMiddleProductDyadicLogPay
  positivity

lemma vaughanTypeIActualDyadicLogPay_nonneg (N Q u v : ℕ) :
    0 ≤ vaughanTypeIActualDyadicLogPay N Q u v := by
  unfold vaughanTypeIActualDyadicLogPay
  exact add_nonneg
    (Finset.sum_nonneg fun k _ => vaughanTypeIFirstDyadicLogPay_nonneg u k N Q)
    (Finset.sum_nonneg fun k _ =>
      vaughanTypeIMiddleProductDyadicLogPay_nonneg u v k N Q)


end

end AnalyticNumberTheory.LargeSieve
