import MathlibNt.Wu2008DoubleSieve.FourModulusTransport

/-!
# The product-truncated positive sixth term

This is a variant of the eleven expression. Only its positive sixth
term is truncated; the original expression and moving fourth-prime
cutoff are not redefined.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def truncatedSixthPairs (N : ℕ) (z w u : ℝ) : Finset (ℕ × ℕ) :=
  primeWindow N z w ×ˢ primeWindow N w u

noncomputable def truncatedSixthKept (N : ℕ) (z w u V : ℝ) : Finset (ℕ × ℕ) :=
  (truncatedSixthPairs N z w u).filter (fun t => (t.1 : ℝ) * t.2 < V)

noncomputable def truncatedSixthOmitted (N : ℕ) (z w u V : ℝ) : Finset (ℕ × ℕ) :=
  (truncatedSixthPairs N z w u).filter (fun t => V ≤ (t.1 : ℝ) * t.2)

noncomputable def truncatedSixthFullMass (N : ℕ) (z w u : ℝ) : ℤ :=
  ∑ t ∈ truncatedSixthPairs N z w u, sieveCount N (t.1 * t.2) N z

noncomputable def truncatedSixthMass (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ truncatedSixthKept N z w u V, sieveCount N (t.1 * t.2) N z

noncomputable def truncatedSixthOmittedMass (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ truncatedSixthOmitted N z w u V, sieveCount N (t.1 * t.2) N z

noncomputable def truncatedSixthExpression (N : ℕ) (z w u v V : ℝ) : ℤ :=
  fourModulusQuotientEleven N z w u v V -
    (truncatedSixthFullMass N z w u - truncatedSixthMass N z w u V)

noncomputable def truncatedSixthExcessMass (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Excess N z w u V, fourModulusQuotientTerm N t

noncomputable def truncatedSixthExcessAtoms (N : ℕ) (z w u V : ℝ) :
    Finset ((_t : ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  (s3Upsilon11Excess N z w u V).sigma
    (fun t => sieveCarrier N (fourModulusProduct t) N (t.2.1 : ℝ))

noncomputable def truncatedSixthOmittedAtoms (N : ℕ) (z w u V : ℝ) :
    Finset ((_t : ℕ × ℕ) × ℕ) :=
  (truncatedSixthOmitted N z w u V).sigma
    (fun t => sieveCarrier N (t.1 * t.2) N z)

theorem truncatedSixth_full_eq_original (N : ℕ) (z w u : ℝ) :
    truncatedSixthFullMass N z w u =
      ∑ d ∈ primeWindow N w u, ∑ c ∈ primeWindow N z w,
        sieveCount N (c * d) N z := by
  unfold truncatedSixthFullMass truncatedSixthPairs
  rw [sum_product, sum_comm]

theorem truncatedSixth_full_sub_kept (N : ℕ) (z w u V : ℝ) :
    truncatedSixthFullMass N z w u - truncatedSixthMass N z w u V =
      truncatedSixthOmittedMass N z w u V := by
  have h := sum_filter_add_sum_filter_not (truncatedSixthPairs N z w u)
    (fun t : ℕ × ℕ => (t.1 : ℝ) * t.2 < V)
    (fun t => sieveCount N (t.1 * t.2) N z)
  simp only [not_lt] at h
  change truncatedSixthMass N z w u V + truncatedSixthOmittedMass N z w u V =
    truncatedSixthFullMass N z w u at h
  omega

theorem truncatedSixthExcessAtoms_card (N : ℕ) (z w u V : ℝ) :
    ((truncatedSixthExcessAtoms N z w u V).card : ℤ) =
      truncatedSixthExcessMass N z w u V := by
  simp only [truncatedSixthExcessAtoms, card_sigma, Nat.cast_sum,
    truncatedSixthExcessMass, fourModulusQuotientTerm, sieveCount]

theorem truncatedSixthOmittedAtoms_card (N : ℕ) (z w u V : ℝ) :
    ((truncatedSixthOmittedAtoms N z w u V).card : ℤ) =
      truncatedSixthOmittedMass N z w u V := by
  simp only [truncatedSixthOmittedAtoms, card_sigma, Nat.cast_sum,
    truncatedSixthOmittedMass, sieveCount]

theorem truncatedSixth_moving_subset_rectangle {N : ℕ} {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    s3Upsilon11Range N z w V ⊆ s3DistinctQuadruples N (s3SecondRange N z w u) := by
  rintro ⟨a, b, c, d⟩ ht
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcw, hwd, hdV⟩ :=
    mem_s3Upsilon11Range.mp ht
  have hcd : c < d := by exact_mod_cast hcw.trans_le hwd
  have hzc : z ≤ (c : ℝ) :=
    hza.trans (by exact_mod_cast (hab.trans hbc).le)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hdu : (d : ℝ) < u := by
    have hprod := (lt_div_iff₀ hc0).mp hdV
    have hzu := mul_le_mul_of_nonneg_right hzc hu
    nlinarith
  exact mem_s3_second_quadruples.mpr
    ⟨ha, haN, hza, hb, hbN, hc, hcN, hd, hdN, hdu, hab, hbc, hcd, hcw, hwd⟩

theorem truncatedSixth_rectangle_split {N : ℕ} {z w u V : ℝ}
    (hu : 0 ≤ u) (hV : V ≤ z * u) :
    (∑ t ∈ s3DistinctQuadruples N (s3SecondRange N z w u),
      fourModulusQuotientTerm N t) =
      (∑ t ∈ s3Upsilon11Range N z w V, fourModulusQuotientTerm N t) +
        truncatedSixthExcessMass N z w u V := by
  have h := sum_sdiff (f := fourModulusQuotientTerm N)
    (truncatedSixth_moving_subset_rectangle (N := N) (w := w) hu hV)
  unfold truncatedSixthExcessMass
  rw [s3Upsilon11Excess_eq_sdiff]
  omega

end Wu2008DoubleSieve
