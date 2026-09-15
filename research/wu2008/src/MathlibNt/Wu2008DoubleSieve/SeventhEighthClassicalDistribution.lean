import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedGeometry
import MathlibNt.Wu2008DoubleSieve.NinthProductProfileDistribution

/-!
# Full convolution distribution for the original seventh and eighth pairs

Only output-independent geometry is packaged. The lower prime endpoint is
b-1, so the physical r=b atom is retained. The full pair aggregate remains
inside the absolute value, at the original common N scale.
-/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real
open scoped Classical

/-- No count, distribution or payment field occurs in this predicate. -/
def ClassicalPairGeometry (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 < p.2 ∧
    (N : ℝ) ^ alpha ≤ p.1 ∧ p.1 * p.2 ^ 2 < N ∧ 3 ≤ p.2

noncomputable def classicalPairRepresentative (S : Finset (ℕ × ℕ)) (m : ℕ) : ℕ × ℕ :=
  if h : ∃ p ∈ S, ninthPairProduct p = m then h.choose else (0, 0)

noncomputable def classicalPairLower (S : Finset (ℕ × ℕ)) (m : ℕ) : ℝ :=
  ((classicalPairRepresentative S m).2 : ℝ) - 1

noncomputable def classicalPairR1 (N : ℕ) (S : Finset (ℕ × ℕ)) (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
    |∑ p ∈ S.filter (fun p => (ninthPairProduct p).Coprime q),
      omega3ProfileError N q (ninthPairProduct p) ((p.2 : ℝ) - 1)
        (ninthProfileUpper N (ninthPairProduct p))|

theorem classicalPair_injective {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) : Set.InjOn ninthPairProduct S := by
  intro p hp p' hp' he
  obtain ⟨ha, hb, hab, _⟩ := hS p hp
  obtain ⟨ha', hb', hab', _⟩ := hS p' hp'
  exact ninth_ordered_prime_product_injective ha hb ha' hb' hab hab' he

theorem classicalPairRepresentative_eq {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    classicalPairRepresentative S (ninthPairProduct p) = p := by
  have h : ∃ p' ∈ S, ninthPairProduct p' = ninthPairProduct p := ⟨p, hp, rfl⟩
  rw [classicalPairRepresentative, dif_pos h]
  exact classicalPair_injective hS h.choose_spec.1 hp h.choose_spec.2

theorem classicalPair_balanced {N : ℕ} (hN : 1 < N) {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    (N : ℝ) ^ alpha ≤ ninthPairProduct p ∧
      (ninthPairProduct p : ℝ) ≤ (N : ℝ) ^ (1 - alpha) := by
  obtain ⟨ha, hb, hab, hlow, hsize, _⟩ := hS p hp
  have ha0 : (0 : ℝ) < p.1 := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < p.2 := by exact_mod_cast hb.pos
  have hb1 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hb.one_lt.le
  have habR : (p.1 : ℝ) ≤ p.2 := by exact_mod_cast hab.le
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) ≤ ninthPairProduct p := by positivity
  have hs : (ninthPairProduct p : ℝ) * p.2 < N := by
    have : ninthPairProduct p * p.2 < N := by
      simpa only [ninthPairProduct, pow_two, mul_assoc] using hsize
    exact_mod_cast this
  constructor
  · exact hlow.trans (by simpa only [ninthPairProduct, Nat.cast_mul] using
      le_mul_of_one_le_right ha0.le hb1)
  · have hmul : (ninthPairProduct p : ℝ) * (N : ℝ) ^ alpha ≤ N :=
      (mul_le_mul_of_nonneg_left (hlow.trans habR) hm0).trans hs.le
    rw [rpow_sub hNR, rpow_one]
    exact (le_div_iff₀ (rpow_pos_of_pos hNR alpha)).mpr hmul

theorem classicalPair_interval {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    2 ≤ (p.2 : ℝ) - 1 ∧
      (p.2 : ℝ) - 1 ≤ ninthProfileUpper N (ninthPairProduct p) ∧
      (ninthPairProduct p : ℝ) * ninthProfileUpper N (ninthPairProduct p) ≤ N := by
  obtain ⟨ha, hb, _, _, hsize, hb3⟩ := hS p hp
  have hm : 0 < ninthPairProduct p := Nat.mul_pos ha.pos hb.pos
  have hN : 0 < N := by omega
  have hs : ninthPairProduct p * p.2 < N := by
    simpa only [ninthPairProduct, pow_two, mul_assoc] using hsize
  have hu := (ninthProfileUpper_nat_iff hN hm).mpr hs
  have hbR : (3 : ℝ) ≤ p.2 := by exact_mod_cast hb3
  refine ⟨by linarith, by linarith, ?_⟩
  have hmR : (ninthPairProduct p : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [ninthProfileUpper, mul_div_cancel₀ _ hmR]
  linarith

theorem classicalPair_error_sum {N q : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) :
    (∑ m ∈ (S.image ninthPairProduct).filter (fun m => m.Coprime q),
      omega3ProfileError N q m (classicalPairLower S m) (ninthProfileUpper N m)) =
    ∑ p ∈ S.filter (fun p => (ninthPairProduct p).Coprime q),
      omega3ProfileError N q (ninthPairProduct p) ((p.2 : ℝ) - 1)
        (ninthProfileUpper N (ninthPairProduct p)) := by
  rw [sum_filter, sum_image (classicalPair_injective hS), sum_filter]
  apply sum_congr rfl
  intro p hp
  simp only [classicalPairLower, classicalPairRepresentative_eq hS hp]

/-- Genuine consumption of the accepted full-convolution distribution theorem.
The threshold precedes every geometric family, not merely its output fibres. -/
theorem classicalPair_balanced_distribution (A : ℝ) {δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S → ∀ Z : ℝ,
        classicalPairR1 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
          C * N / log (N : ℝ) ^ A := by
  obtain ⟨C, hC, T, hT, hdist⟩ := omega3_balanced_interval_distribution A alpha 1
    hA (by norm_num [alpha]) (by norm_num) hδ
  refine ⟨C, hC, T, hT, ?_⟩
  intro N hN S hS Z
  have hN1 : 1 < N := by omega
  have h := hdist N hN (S.image ninthPairProduct) (fun _ => 1)
    (classicalPairLower S) (ninthProfileUpper N)
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      exact classicalPair_balanced hN1 hS hp)
    (by intro m _; norm_num)
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      simpa only [classicalPairLower, classicalPairRepresentative_eq hS hp] using
        classicalPair_interval hS hp) Z
  simpa only [one_mul, classicalPair_error_sum hS, classicalPairR1] using h

theorem seventh_classicalPairGeometry {N : ℕ} (hN : 512 ≤ N) :
    ClassicalPairGeometry N (seventhPairs N) := by
  intro p hp
  obtain ⟨hm, _⟩ := mem_filter.mp hp
  obtain ⟨ha, hb, _, _, hwa, hub, hab, hsize⟩ := lowerPairs_data hm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlow : (N : ℝ) ^ alpha ≤ p.1 :=
    (rpow_le_rpow_of_exponent_le hN1 (by norm_num [alpha, beta] : alpha ≤ beta)).trans hwa
  have hu : 4 ≤ u N := (ninth_fixed_cutoffs_ge hN).2
  have hb3 : (3 : ℝ) ≤ p.2 := by linarith
  exact ⟨ha, hb, hab, hlow, hsize, by exact_mod_cast hb3⟩

theorem eighth_classicalPairGeometry {N : ℕ} (hN : 512 ≤ N) :
    ClassicalPairGeometry N (eighthPairs N) := by
  intro p hp
  obtain ⟨hm, _⟩ := mem_filter.mp hp
  obtain ⟨ha, hb, _, _, hza, hvb, hab, hsize⟩ := lowerPairs_data hm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hu : 4 ≤ u N := (ninth_fixed_cutoffs_ge hN).2
  have huv : u N ≤ v N := rpow_le_rpow_of_exponent_le hN1
    (by norm_num [sigma, alpha] : sigma ≤ (1 / 3 : ℝ))
  have hb3 : (3 : ℝ) ≤ p.2 := by linarith
  exact ⟨ha, hb, hab, hza, hsize, by exact_mod_cast hb3⟩

/-- One common C and T for both literal original pair families. -/
theorem seventh_eighth_full_convolution_distribution (A : ℝ) {δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      classicalPairR1 N (seventhPairs N) (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
          C * N / log (N : ℝ) ^ A ∧
      classicalPairR1 N (eighthPairs N) (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
          C * N / log (N : ℝ) ^ A := by
  obtain ⟨C, hC, T, _, hd⟩ := classicalPair_balanced_distribution A hA hδ
  refine ⟨C, hC, max T 512, le_max_right _ _, ?_⟩
  intro N hN Z
  have hNT := (le_max_left T 512).trans hN
  have h512 := (le_max_right T 512).trans hN
  exact ⟨hd N hNT _ (seventh_classicalPairGeometry h512) Z,
    hd N hNT _ (eighth_classicalPairGeometry h512) Z⟩

/-- Closed lower prime atoms are not discarded by the profile translation. -/
theorem classicalPair_lower_nat_iff (b r : ℕ) :
    (b : ℝ) - 1 < (r : ℝ) ↔ b ≤ r := by
  have h : (b : ℤ) - 1 < (r : ℤ) ↔ b ≤ r := by omega
  exact_mod_cast h

/-- Exact physical fibre identity: no new coprimality condition on r or output. -/
theorem classicalPair_physical_fibre {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    ((range (N + 1)).filter (fun r : ℕ => r.Prime ∧ p.2 ≤ r ∧
      p.1 * p.2 * r < N ∧ (N - p.1 * p.2 * r).Prime)) =
    (omega3ProfilePrimes N ((p.2 : ℝ) - 1) (ninthProfileUpper N (ninthPairProduct p))).filter
      (fun r => (N - ninthPairProduct p * r).Prime) := by
  obtain ⟨ha, hb, _, _, hs, _⟩ := hS p hp
  have hN : 0 < N := by omega
  have hm : 0 < ninthPairProduct p := Nat.mul_pos ha.pos hb.pos
  ext r
  simp only [omega3ProfilePrimes, mem_filter, classicalPair_lower_nat_iff,
    ninthPairProduct, ninthProfileUpper_nat_iff hN (show 0 < p.1 * p.2 from hm)]
  tauto

theorem classicalPair_physical_card {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) :
    (physical N S).card = ∑ p ∈ S,
      ((omega3ProfilePrimes N ((p.2 : ℝ) - 1)
        (ninthProfileUpper N (ninthPairProduct p))).filter
          (fun r => (N - ninthPairProduct p * r).Prime)).card := by
  rw [physical, card_sigma]
  apply sum_congr rfl
  intro p hp
  rw [classicalPair_physical_fibre hS hp]

end Wu2008DoubleSieve.SeventhEighth
