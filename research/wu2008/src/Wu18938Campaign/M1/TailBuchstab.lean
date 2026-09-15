import WR2MotherMovingRange
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthCarriers

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

noncomputable def tailTriples (N : ℕ) (z w u V : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (s3SecondRange N z w u).filter (fun t => V ≤ (t.2.1 : ℝ) * t.2.2)

noncomputable def tailPairRaised (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ truncatedSixthOmitted N z w u V,
    sieveCount N (t.1 * t.2) N (t.1 : ℝ)

noncomputable def tailTripleRaised (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ tailTriples N z w u V,
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ)

private theorem tail_triples_sum (N : ℕ) (z w u V : ℝ)
    (f : ℕ × ℕ × ℕ → ℤ) :
    (∑ t ∈ tailTriples N z w u V, f t) =
      ∑ t ∈ truncatedSixthOmitted N z w u V,
        ∑ a ∈ primeWindow N z (t.1 : ℝ), f (a, t.1, t.2) := by
  rw [sum_sigma']
  apply sum_bij (fun t _ => ⟨(t.2.1, t.2.2), t.1⟩)
  · rintro ⟨a, c, d⟩ ht
    obtain ⟨ht, hV⟩ := mem_filter.mp ht
    obtain ⟨ht, hcw, hwd⟩ := mem_filter.mp ht
    obtain ⟨ha, haN, hza, hc, hcN, hd, hdN, hdu, hac, _⟩ :=
      mem_s3_ordered_triples.mp ht
    have hac' : (a : ℝ) < c := by exact_mod_cast hac
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_primeWindow.mpr ⟨hc, hcN, hza.trans hac'.le, hcw⟩,
        mem_primeWindow.mpr ⟨hd, hdN, hwd, hdu⟩⟩, hV⟩,
      mem_primeWindow.mpr ⟨ha, haN, hza, hac'⟩⟩
  · rintro ⟨a, c, d⟩ _ ⟨a', c', d'⟩ _ h
    have hcd := congrArg Sigma.fst h
    have ha := congrArg (fun t : (_ : ℕ × ℕ) × ℕ => t.2) h
    have hc := congrArg Prod.fst hcd
    have hd := congrArg Prod.snd hcd
    dsimp only at ha hc hd
    subst a'; subst c'; subst d'
    rfl
  · rintro ⟨⟨c, d⟩, a⟩ ht
    obtain ⟨hcd, ha⟩ := mem_sigma.mp ht
    obtain ⟨hcd, hV⟩ := mem_filter.mp hcd
    obtain ⟨hc, hd⟩ := mem_product.mp hcd
    obtain ⟨ha, haN, hza, hac⟩ := mem_primeWindow.mp ha
    obtain ⟨hc, hcN, _, hcw⟩ := mem_primeWindow.mp hc
    obtain ⟨hd, hdN, hwd, hdu⟩ := mem_primeWindow.mp hd
    refine ⟨(a, c, d), mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_s3_ordered_triples.mpr
        ⟨ha, haN, hza, hc, hcN, hd, hdN, hdu,
          by exact_mod_cast hac, by exact_mod_cast hcw.trans_le hwd⟩,
        hcw, hwd⟩, hV⟩, rfl⟩
  · intro t _
    rfl

private theorem tail_distinct_quadruples (N : ℕ) (z w u V : ℝ) :
    s3DistinctQuadruples N (tailTriples N z w u V) =
      s3Upsilon11Excess N z w u V := by
  ext ⟨a, b, c, d⟩
  simp only [mem_s3DistinctQuadruples, tailTriples, s3Upsilon11Excess, mem_filter]
  tauto

theorem tail_buchstab_exact (N : ℕ) (z w u V : ℝ) :
    truncatedSixthOmittedMass N z w u V =
      quotientExcess N z w u V + tailPairRaised N z w u V +
        tailTripleRaised N z w u V +
        s3RepeatedFirstPrimeMass N (tailTriples N z w u V) := by
  have hfirst :
      truncatedSixthOmittedMass N z w u V =
        tailPairRaised N z w u V +
          ∑ t ∈ tailTriples N z w u V,
            sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ) := by
    unfold truncatedSixthOmittedMass tailPairRaised
    rw [tail_triples_sum, ← sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨c, d⟩ ht
    have hzc := (mem_primeWindow.mp (mem_product.mp (mem_filter.mp ht).1).1).2.2.1
    have h := goldbach_buchstab N (c * d) N hzc
    dsimp only
    simp only [mul_comm, mul_left_comm] at h ⊢
    omega
  have hsecond :
      (∑ t ∈ tailTriples N z w u V,
        sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)) =
      tailTripleRaised N z w u V +
        ∑ t ∈ tailTriples N z w u V, s3FourPrimeRemainder N t := by
    unfold tailTripleRaised
    rw [← sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨a, c, d⟩ ht
    obtain ⟨_, _, _, _, _, _, _, _, hac, _⟩ := mem_s3_ordered_triples.mp
      (mem_filter.mp (mem_filter.mp ht).1).1
    have h := s3_triple_cutoff_difference N a c d hac.le
    dsimp only
    omega
  have hsplit := s3_fourprime_sum_split N (tailTriples N z w u V) (by
    rintro ⟨a, c, d⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hac, _⟩ := mem_s3_ordered_triples.mp
      (mem_filter.mp (mem_filter.mp ht).1).1
    exact ⟨ha, haN, hac⟩)
  rw [tail_distinct_quadruples] at hsplit
  change _ = quotientExcess N z w u V +
    s3RepeatedFirstPrimeMass N (tailTriples N z w u V) at hsplit
  omega

theorem tail_repeated_partition (N : ℕ) (z w u V : ℝ) :
    s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) =
      s3RepeatedFirstPrimeMass N (tailTriples N z w u V) +
        s3RepeatedFirstPrimeMass N
          ((s3SecondRange N z w u).filter (fun t => (t.2.1 : ℝ) * t.2.2 < V)) := by
  have h := sum_filter_add_sum_filter_not (s3SecondRange N z w u)
    (fun t : ℕ × ℕ × ℕ => V ≤ (t.2.1 : ℝ) * t.2.2)
    (fun t => sieveCount N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ))
  simpa only [s3RepeatedFirstPrimeMass, tailTriples, not_le] using h.symm

end Wu18938Campaign.M1
