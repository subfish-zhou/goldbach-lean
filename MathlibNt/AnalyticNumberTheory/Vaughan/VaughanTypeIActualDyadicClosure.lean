

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicDecomposition

/-!
 # Unconditional closure of the actual dyadic Vaughan Type-I input
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Summing the per-character long-row inequality with the AP weight gives the
complete first- and middle-row means. -/
private theorem apNormalizedVaughanTypeIMean_le_complete_rows
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIMean N Q u v ≤
      apNormalizedVaughanTypeIFirstShellMean (Finset.Icc 1 u) N Q +
      apNormalizedVaughanTypeIMiddleProductShellMean
        (Finset.Icc 1 u ×ˢ Finset.Icc 1 v) N Q := by
  unfold apNormalizedVaughanTypeIMean apNormalizedPrimitiveMean
  unfold apNormalizedVaughanTypeIFirstShellMean
    apNormalizedVaughanTypeIMiddleProductShellMean
    apNormalizedWeightedRowShellMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ χ : PrimitiveCharacter q,
          primitivePrefixAmplitude
            (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ) ≤
          ∑ χ : PrimitiveCharacter q,
            ((∑ d ∈ Finset.Icc 1 u,
                ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
                  Real.sqrt (primitiveCharacterPrefixMaxSquare
                    (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ)) +
              ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v,
                ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
                  (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
                  Real.sqrt (primitiveCharacterPrefixMaxSquare
                    (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
                      (N / (de.1 * de.2)) q χ)) := by
            apply Finset.sum_le_sum
            intro χ hχ
            exact primitivePrefixAmplitude_vaughanTypeI_le_rows N u v q χ
      _ =
          (∑ χ : PrimitiveCharacter q, ∑ d ∈ Finset.Icc 1 u,
            ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
              Real.sqrt (primitiveCharacterPrefixMaxSquare
                (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ)) +
          ∑ χ : PrimitiveCharacter q,
            ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v,
              ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
                (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
                Real.sqrt (primitiveCharacterPrefixMaxSquare
                  (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
                    (N / (de.1 * de.2)) q χ) := Finset.sum_add_distrib
  · positivity

/-- The first shell means sum exactly to the complete first-row mean. -/
private theorem sum_apNormalizedVaughanTypeIFirstDyadicShellMean
    (N Q u : ℕ) :
    (∑ k ∈ Finset.range (Nat.log2 u + 1),
      apNormalizedVaughanTypeIFirstShellMean
        (vaughanTypeIFirstDyadicShell u k) N Q) =
      apNormalizedVaughanTypeIFirstShellMean (Finset.Icc 1 u) N Q := by
  unfold apNormalizedVaughanTypeIFirstShellMean
    apNormalizedWeightedRowShellMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact sum_vaughanTypeIFirstDyadicShell u (fun d =>
    ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0
          (vaughanTypeIFirstRowLength N d) q χ))

/-- The product-dyadic middle shell means sum exactly to the complete middle-row mean. -/
private theorem sum_apNormalizedVaughanTypeIMiddleProductDyadicShellMean
    (N Q u v : ℕ) :
    (∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
      apNormalizedVaughanTypeIMiddleProductShellMean
        (vaughanTypeIMiddleProductDyadicShell u v k) N Q) =
      apNormalizedVaughanTypeIMiddleProductShellMean
        (Finset.Icc 1 u ×ˢ Finset.Icc 1 v) N Q := by
  unfold apNormalizedVaughanTypeIMiddleProductShellMean
    apNormalizedWeightedRowShellMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact sum_vaughanTypeIMiddleProductDyadicShell u v (fun de =>
    ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
          (vaughanTypeIMiddlePairRowLength N de) q χ))

/-- Exact unconditional decomposition of the AP-normalized Vaughan Type-I mean
into the actual first and product-dyadic middle shells. -/
theorem apNormalizedVaughanTypeIMean_le_actual_dyadic_shells
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIMean N Q u v ≤
      (∑ k ∈ Finset.range (Nat.log2 u + 1),
        apNormalizedVaughanTypeIFirstShellMean
          (vaughanTypeIFirstDyadicShell u k) N Q) +
      ∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
        apNormalizedVaughanTypeIMiddleProductShellMean
          (vaughanTypeIMiddleProductDyadicShell u v k) N Q := by
  rw [sum_apNormalizedVaughanTypeIFirstDyadicShellMean,
    sum_apNormalizedVaughanTypeIMiddleProductDyadicShellMean]
  exact apNormalizedVaughanTypeIMean_le_complete_rows N Q u v

/-- Primitive characters form a subtype of all Dirichlet characters, so their
cardinality is bounded by Euler's totient without any additional hypothesis. -/
theorem card_primitiveCharacter_le_totient (q : ℕ) :
    0 < q → Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  intro hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) :=
      @Fintype.card_subtype_le (DirichletCharacter ℂ q) _
        (fun χ => χ.IsPrimitive) _
    _ = q.totient := by
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
        (a := (1 : ZMod q)) isUnit_one (1 : ZMod q)
      simpa using h

/-- Unconditional direct AP-normalized Type-I input.  The physical shell
bounds are assembled against the proved exact first/middle long-variable shell
decomposition, so no decomposition hypothesis is exposed or carried. -/
theorem vaughanDirectAPNormalizedTypeIInput_actual_dyadic
    (N Q u v : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (hu : u ≤ Q ^ 2) (huv : u * v ≤ Q ^ 2) :
    VaughanDirectAPNormalizedTypeIInput N Q u v
      (((Nat.log2 u + 1) + (Nat.log2 (u * v) + 1) : ℕ) : ℝ)
      (vaughanTypeIActualDyadicLogPay N Q u v) := by
  have hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient := fun q hq =>
    card_primitiveCharacter_le_totient q (Finset.mem_Icc.mp hq).1
  have hshort : vaughanTypeIShortScale u v ≤ Q ^ 2 := by
    exact max_le hu huv
  have hsqrtScale : Real.sqrt ((N : ℝ) * vaughanTypeIShortScale u v) ≤
      (Q : ℝ) * Real.sqrt N := by
    have hprod : (N : ℝ) * vaughanTypeIShortScale u v ≤
        (Q : ℝ) ^ 2 * N := by
      simpa [mul_comm] using (by
        exact_mod_cast Nat.mul_le_mul_left N hshort :
          (N : ℝ) * vaughanTypeIShortScale u v ≤ (N : ℝ) * Q ^ 2)
    have harg0 : 0 ≤ (N : ℝ) * vaughanTypeIShortScale u v := by positivity
    have hx : Real.sqrt ((N : ℝ) * vaughanTypeIShortScale u v) ^ 2 =
        (N : ℝ) * vaughanTypeIShortScale u v := Real.sq_sqrt harg0
    have hy : ((Q : ℝ) * Real.sqrt N) ^ 2 = (Q : ℝ) ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hright : 0 ≤ (Q : ℝ) * Real.sqrt N := by positivity
    nlinarith [Real.sqrt_nonneg ((N : ℝ) * vaughanTypeIShortScale u v),
      Real.sqrt_nonneg (N : ℝ)]
  have hphysicalScale : (N : ℝ) + (Q : ℝ) *
        Real.sqrt ((N : ℝ) * vaughanTypeIShortScale u v) ≤
      (N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N := by
    have := mul_le_mul_of_nonneg_left hsqrtScale (by positivity : (0 : ℝ) ≤ Q)
    nlinarith
  have hfirst : ∀ k ∈ Finset.range (Nat.log2 u + 1),
      apNormalizedVaughanTypeIFirstShellMean
          (vaughanTypeIFirstDyadicShell u k) N Q ≤
        vaughanTypeIActualDyadicLogPay N Q u v *
          ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N) := by
    intro k hk
    by_cases hS : vaughanTypeIFirstDyadicShell u k = ∅
    · simp [apNormalizedVaughanTypeIFirstShellMean,
        apNormalizedWeightedRowShellMean, hS]
      exact mul_nonneg (vaughanTypeIActualDyadicLogPay_nonneg N Q u v) (by positivity)
    · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hD : 2 ^ k ≤ vaughanTypeIShortScale u v :=
        (vaughanTypeIFirstDyadicShell_bounds hd).1.trans
          ((mem_vaughanTypeIFirstDyadicShell.mp hd).2.1.trans
            (Nat.le_max_left _ _))
      refine (apNormalizedVaughanTypeIFirstDyadicShell_physical
        u k N Q hN hQ hcard).trans ?_
      have hpay : vaughanTypeIFirstDyadicLogPay u k N Q ≤
          vaughanTypeIActualDyadicLogPay N Q u v := by
        unfold vaughanTypeIActualDyadicLogPay
        exact (Finset.single_le_sum
          (fun j _ => vaughanTypeIFirstDyadicLogPay_nonneg u j N Q) hk).trans
            (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
              vaughanTypeIMiddleProductDyadicLogPay_nonneg u v j N Q))
      have hscale : (N : ℝ) + (Q : ℝ) *
            Real.sqrt ((N : ℝ) * (2 ^ k : ℕ)) ≤
          (N : ℝ) + (Q : ℝ) *
            Real.sqrt ((N : ℝ) * vaughanTypeIShortScale u v) := by
        gcongr
      exact (mul_le_mul hpay hscale
        (by positivity)
        (vaughanTypeIActualDyadicLogPay_nonneg N Q u v)).trans
          (mul_le_mul_of_nonneg_left hphysicalScale
            (vaughanTypeIActualDyadicLogPay_nonneg N Q u v))
  have hmiddle : ∀ k ∈ Finset.range (Nat.log2 (u * v) + 1),
      apNormalizedVaughanTypeIMiddleProductShellMean
          (vaughanTypeIMiddleProductDyadicShell u v k) N Q ≤
        vaughanTypeIActualDyadicLogPay N Q u v *
          ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N) := by
    intro k hk
    by_cases hS : vaughanTypeIMiddleProductDyadicShell u v k = ∅
    · simp [apNormalizedVaughanTypeIMiddleProductShellMean,
        apNormalizedWeightedRowShellMean, hS]
      exact mul_nonneg (vaughanTypeIActualDyadicLogPay_nonneg N Q u v) (by positivity)
    · obtain ⟨de, hde⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hD : 2 ^ k ≤ vaughanTypeIShortScale u v :=
        (vaughanTypeIMiddleProductDyadicShell_bounds hde).1.trans
          ((Nat.mul_le_mul
            (mem_vaughanTypeIMiddleProductDyadicShell.mp hde).2.1
            (mem_vaughanTypeIMiddleProductDyadicShell.mp hde).2.2.2.1).trans
              (Nat.le_max_right _ _))
      refine (apNormalizedVaughanTypeIMiddleProductDyadicShell_physical
        u v k N Q hN hQ hcard).trans ?_
      have hpay : vaughanTypeIMiddleProductDyadicLogPay u v k N Q ≤
          vaughanTypeIActualDyadicLogPay N Q u v := by
        unfold vaughanTypeIActualDyadicLogPay
        exact (Finset.single_le_sum
          (fun j _ => vaughanTypeIMiddleProductDyadicLogPay_nonneg u v j N Q) hk).trans
            (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ =>
              vaughanTypeIFirstDyadicLogPay_nonneg u j N Q))
      have hscale : (N : ℝ) + (Q : ℝ) *
            Real.sqrt ((N : ℝ) * (2 ^ k : ℕ)) ≤
          (N : ℝ) + (Q : ℝ) *
            Real.sqrt ((N : ℝ) * vaughanTypeIShortScale u v) := by
        gcongr
      exact (mul_le_mul hpay hscale
        (by positivity)
        (vaughanTypeIActualDyadicLogPay_nonneg N Q u v)).trans
          (mul_le_mul_of_nonneg_left hphysicalScale
            (vaughanTypeIActualDyadicLogPay_nonneg N Q u v))
  simpa only [Finset.card_range] using
    vaughanDirectAPNormalizedTypeIInput_of_shells
      (Finset.range (Nat.log2 u + 1))
      (Finset.range (Nat.log2 (u * v) + 1))
      (fun k => apNormalizedVaughanTypeIFirstShellMean
        (vaughanTypeIFirstDyadicShell u k) N Q)
      (fun k => apNormalizedVaughanTypeIMiddleProductShellMean
        (vaughanTypeIMiddleProductDyadicShell u v k) N Q)
      N Q u v (vaughanTypeIActualDyadicLogPay N Q u v)
      (vaughanTypeIActualDyadicLogPay_nonneg N Q u v)
      (apNormalizedVaughanTypeIMean_le_actual_dyadic_shells N Q u v)
      hfirst hmiddle

end

end AnalyticNumberTheory.LargeSieve
