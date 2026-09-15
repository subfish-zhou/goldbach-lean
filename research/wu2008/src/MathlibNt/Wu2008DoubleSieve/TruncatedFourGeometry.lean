import MathlibNt.Wu2008DoubleSieve.TruncatedFourExceptions

/-! The original strict domains, with their literal fixed cutoff geometry. -/
namespace Wu2008DoubleSieve.TruncatedFourPhysical
open Finset Real
open scoped Classical

noncomputable def T10 (N : ℕ) : Finset Quad :=
  s3DistinctQuadruples N (orderedTriples (primeWindow N
    ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^truncatedSixthLowerBeta)))
noncomputable def T11 (N : ℕ) : Finset Quad :=
  s3Upsilon11Range N ((N : ℝ)^truncatedSixthLowerAlpha)
    ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerLambda)

noncomputable def Physical10 (N : ℕ) : Finset Label := physical N (T10 N)
noncomputable def Physical11 (N : ℕ) : Finset Label := physical N (T11 N)
noncomputable def Q10 (N : ℕ) : ℤ :=
  ∑ t ∈ T10 N, sieveCount N (fourModulusProduct t) N (t.2.1 : ℝ)
noncomputable def Q11 (N : ℕ) : ℤ :=
  ∑ t ∈ T11 N, sieveCount N (fourModulusProduct t) N (t.2.1 : ℝ)

theorem physical_mem {N n : ℕ} {S : Finset Quad} {t : Quad}
    (hD : 0 < fourModulusProduct t) :
    (⟨t,n⟩ : Label) ∈ physical N S ↔ t ∈ S ∧ 1 < n ∧
      LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) n ∧
      fourModulusProduct t*n < N ∧ (N-fourModulusProduct t*n).Prime := by
  simp only [physical, mem_sigma, mem_filter, mem_range]
  constructor
  · rintro ⟨ht,_,hn,hr,hlt,hp⟩
    exact ⟨ht,hn,hr,hlt,hp⟩
  · rintro ⟨ht,hn,hr,hlt,hp⟩
    exact ⟨ht, Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left n hD).trans hlt.le),hn,hr,hlt,hp⟩

theorem T10_sub (N : ℕ) : T10 N ⊆ fourModulusDomain N
    ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^truncatedSixthLowerBeta)
    ((N : ℝ)^truncatedSixthLowerLambda) := subset_union_left

theorem T11_sub (N : ℕ) : T11 N ⊆ fourModulusDomain N
    ((N : ℝ)^truncatedSixthLowerAlpha) ((N : ℝ)^truncatedSixthLowerBeta)
    ((N : ℝ)^truncatedSixthLowerLambda) := subset_union_right

theorem tenth_strict_cap {N : ℕ} {z w : ℝ} {t : Quad}
    (ht : t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w))) :
    (fourModulusProduct t : ℝ) < w^4 := by
  rcases t with ⟨a,b,c,d⟩
  obtain ⟨ha,_,_,hb,_,hc,_,hd,_,hdw,hab,hbc,hcd⟩ := mem_s3_first_quadruples.mp ht
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have hcd' : (c : ℝ) < d := by exact_mod_cast hcd
  have haw := hab'.trans (hbc'.trans (hcd'.trans hdw))
  have hbw := hbc'.trans (hcd'.trans hdw)
  have hcw := hcd'.trans hdw
  calc
    _ = (a : ℝ)*b*c*d := by simp only [fourModulusProduct, Nat.cast_mul]
    _ < w*w*w*w := by gcongr
    _ = w^4 := by ring

theorem eleventh_strict_cap {N : ℕ} {z w V : ℝ} {t : Quad}
    (ht : t ∈ s3Upsilon11Range N z w V) :
    (fourModulusProduct t : ℝ) < w^2*V := by
  rcases t with ⟨a,b,c,d⟩
  obtain ⟨ha,_,_,hb,_,hc,_,hd,_,hab,hbc,hcw,_,_⟩ := mem_s3Upsilon11Range.mp ht
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have haw := hab'.trans (hbc'.trans hcw)
  have hbw := hbc'.trans hcw
  have hcd := fourModulus_moving_bound ht
  calc
    _ = (a : ℝ)*b*((c : ℝ)*d) := by simp only [fourModulusProduct, Nat.cast_mul]; ring
    _ < w*w*V := by gcongr
    _ = w^2*V := by ring

theorem fixed_exponents :
    0 < truncatedSixthLowerAlpha ∧
    4*truncatedSixthLowerBeta ≤ 1-truncatedSixthLowerAlpha ∧
    2*truncatedSixthLowerBeta+truncatedSixthLowerLambda ≤ 1-truncatedSixthLowerAlpha ∧
    (1/2 : ℝ) ≤ 1-truncatedSixthLowerAlpha := by
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerBeta, truncatedSixthLowerLambda]

theorem T10_cap {N : ℕ} (hN : 1 ≤ N) {t : Quad} (ht : t ∈ T10 N) :
    (fourModulusProduct t : ℝ) ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) := by
  apply (tenth_strict_cap ht).le.trans
  calc
    _ = (N : ℝ)^(4*truncatedSixthLowerBeta) := by
      rw [mul_comm (4 : ℝ), rpow_mul (Nat.cast_nonneg N)]
      norm_num
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) fixed_exponents.2.1

theorem T11_cap {N : ℕ} (hN : 1 ≤ N) {t : Quad} (ht : t ∈ T11 N) :
    (fourModulusProduct t : ℝ) ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (eleventh_strict_cap ht).le.trans
  calc
    _ = (N : ℝ)^(2*truncatedSixthLowerBeta+truncatedSixthLowerLambda) := by
      rw [rpow_add hN0, mul_comm (2 : ℝ), rpow_mul hN0.le]
      norm_num
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) fixed_exponents.2.2.1

/-- Exact physical membership on the unmodified original tenth domain. -/
theorem Physical10_mem (N : ℕ) (t : Quad) (n : ℕ) :
    (⟨t,n⟩ : Label) ∈ Physical10 N ↔ t ∈ T10 N ∧ 1 < n ∧
      LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) n ∧
      fourModulusProduct t*n < N ∧ (N-fourModulusProduct t*n).Prime := by
  by_cases ht : t ∈ T10 N
  · exact physical_mem (domain_product_pos (T10_sub N ht))
  · simp [Physical10, physical, ht]

theorem Physical11_mem (N : ℕ) (t : Quad) (n : ℕ) :
    (⟨t,n⟩ : Label) ∈ Physical11 N ↔ t ∈ T11 N ∧ 1 < n ∧
      LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) n ∧
      fourModulusProduct t*n < N ∧ (N-fourModulusProduct t*n).Prime := by
  by_cases ht : t ∈ T11 N
  · exact physical_mem (domain_product_pos (T11_sub N ht))
  · simp [Physical11, physical, ht]

end Wu2008DoubleSieve.TruncatedFourPhysical
