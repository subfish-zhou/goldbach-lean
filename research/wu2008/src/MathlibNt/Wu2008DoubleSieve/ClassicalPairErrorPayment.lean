import MathlibNt.Wu2008DoubleSieve.ClassicalPairSmallOutput
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeEuler
import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentAsymptotic

/-! Uniform R2 payment on the actual pair support. The image transfer is
injective, the roughness exponent is original alpha, and the complete
squarefree Euler mass pays 3^omega/phi rather than the number of moduli. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real Filter
open scoped Classical Topology

theorem classicalPair_product_rough {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S)
    {l : ℕ} (hl : l.Prime) (hd : l ∣ ninthPairProduct p) : (N : ℝ) ^ alpha ≤ l := by
  obtain ⟨ha, hb, hab, hwa, _⟩ := hS p hp
  rcases hl.dvd_mul.mp hd with hla | hlb
  · have h : l = p.1 := ((Nat.dvd_prime ha).mp hla).resolve_left hl.ne_one
    simpa only [h] using hwa
  · have h : l = p.2 := ((Nat.dvd_prime hb).mp hlb).resolve_left hl.ne_one
    rw [h]
    exact hwa.trans (by exact_mod_cast hab.le)

theorem classicalPair_product_range {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    0 < ninthPairProduct p ∧ ninthPairProduct p ≤ N := by
  obtain ⟨ha, hb, _, _, hs, _⟩ := hS p hp
  refine ⟨Nat.mul_pos ha.pos hb.pos, ?_⟩
  have hb1 := hb.one_lt
  change p.1 * p.2 ≤ N
  nlinarith

theorem classicalProfile_card_le_div {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    ((classicalProfile N p).card : ℝ) ≤ (N : ℝ) / ninthPairProduct p := by
  have hmR : (0 : ℝ) < ninthPairProduct p := by
    exact_mod_cast (classicalPair_product_range hS hp).1
  have hsub : classicalProfile N p ⊆ Icc 1 ⌊(N : ℝ) / ninthPairProduct p⌋₊ := by
    intro r hr
    have hs : (ninthPairProduct p : ℝ) * r ≤ N := by
      exact_mod_cast (classicalProfile_size hS hp hr).le
    have hrN : (r : ℝ) ≤ (N : ℝ) / ninthPairProduct p :=
      (le_div_iff₀ hmR).mpr (by simpa only [mul_comm] using hs)
    exact mem_Icc.mpr ⟨(mem_filter.mp hr).2.1.one_lt.le, Nat.le_floor hrN⟩
  calc
    _ ≤ ((Icc 1 ⌊(N : ℝ) / ninthPairProduct p⌋₊).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ _ := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
        Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hmR.le)

theorem classicalMissingMass_bound {N q : ℕ} (hN : 0 < N) {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (hq : 0 < q) (hqN : q ≤ N) :
    classicalMissingMass N S q ≤
      (N : ℝ) * ((1 + log N) * log N / ((N : ℝ) ^ alpha * log 2)) := by
  have hw : 0 < (N : ℝ) ^ alpha := rpow_pos_of_pos (by exact_mod_cast hN) _
  have hr := omega3_rough_non_coprime_reciprocal_le N q (S.image ninthPairProduct)
    hw hq hqN
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      exact classicalPair_product_range hS hp)
    (by
      intro m hm l hl hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      exact classicalPair_product_rough hS hp hl hd)
  have heq :
      (∑ m ∈ (S.image ninthPairProduct).filter (fun m => ¬m.Coprime q), 1 / (m : ℝ)) =
      ∑ p ∈ S.filter (fun p => ¬(ninthPairProduct p).Coprime q),
        1 / (ninthPairProduct p : ℝ) := by
    rw [sum_filter, sum_image (classicalPair_injective hS), sum_filter]
  rw [heq] at hr
  calc
    _ ≤ ∑ p ∈ S.filter (fun p => ¬(ninthPairProduct p).Coprime q),
        (N : ℝ) / ninthPairProduct p := by
      apply sum_le_sum
      intro p hp
      exact classicalProfile_card_le_div hS (mem_filter.mp hp).1
    _ = (N : ℝ) * ∑ p ∈ S.filter (fun p => ¬(ninthPairProduct p).Coprime q),
        1 / (ninthPairProduct p : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N)

theorem classicalR2_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ S : Finset (ℕ × ℕ),
      ClassicalPairGeometry N S → ∀ D : ℕ, ∀ Z : ℝ,
      Z ≤ N → (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      classicalR2 N S D Z ≤
        C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN S hS D Z hZ hqN
  have hnonneg : 0 ≤ (N : ℝ) *
      ((1 + log N) * log N / ((N : ℝ) ^ alpha * log 2)) := by
    have := log_natCast_nonneg N
    positivity
  calc
    _ ≤ ∑ q ∈ omega3SieveModuli N D Z,
        ((3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
          ((N : ℝ) * ((1 + log N) * log N / ((N : ℝ) ^ alpha * log 2))) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (classicalMissingMass_bound (by omega) hS
          (omega3SieveModuli_properties hq).1 (hqN q hq)) (by positivity)
    _ = (∑ q ∈ omega3SieveModuli N D Z,
        (3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
          ((N : ℝ) * ((1 + log N) * log N / ((N : ℝ) ^ alpha * log 2))) :=
      (sum_mul ..).symm
    _ ≤ (C * log N ^ 3) *
        ((N : ℝ) * ((1 + log N) * log N / ((N : ℝ) ^ alpha * log 2))) := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun q _ _ => by positivity)).trans (hmass N (by omega) Z hZ)
    _ = _ := by ring

theorem classicalR2_source_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ S : Finset (ℕ × ℕ),
      ClassicalPairGeometry N S → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      classicalR2 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
  obtain ⟨C, hC, hb⟩ := classicalR2_finite_bound
  refine ⟨C, hC, ?_⟩
  intro N hN S hS δ hδ hδhi
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  apply hb N hN S hS _ _ hg.2.2.2.1
  intro q hq
  have hqD := (omega3SieveModuli_properties hq).2.2.2
  have hDN := hg.2.2.2.2.2.2.1
  omega

theorem classicalR2_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ S : Finset (ℕ × ℕ),
      ClassicalPairGeometry N S → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      classicalR2 N S (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤ ε * N / log N ^ 2 := by
  obtain ⟨C, hC, hf⟩ := classicalR2_source_bound
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 5
    (show 0 < 2 * C / log 2 by positivity) (by norm_num [alpha] : 0 < alpha) hε
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN S hS δ hδ hδhi
  have hN1 := (le_max_left T1 T2).trans hN
  have hlog1 := hlogT N ((le_max_right _ _).trans hN)
  calc
    _ ≤ C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) :=
      hf N (hT1.trans hN1) S hS δ hδ hδhi
    _ ≤ C * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
      gcongr
      linarith
    _ = (2 * C / log 2) * N * log N ^ 5 / (N : ℝ) ^ alpha := by ring
    _ ≤ _ := hpay N hN1

theorem classicalSmallBudget_source_bound {N : ℕ} (hN : 512 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    classicalSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      (2 / alpha ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hZ : sqrt ((N : ℝ) ^ (1 / 2 - δ)) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_mul (Nat.cast_nonneg N)]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [rpow_zero] using
      rpow_le_rpow_of_exponent_le hN1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hfloor := Nat.floor_le (sqrt_nonneg ((N : ℝ) ^ (1 / 2 - δ)))
  unfold classicalSmallBudget
  rw [max_eq_left (sqrt_nonneg _), Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (1 / alpha ^ 2) * (2 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

theorem classicalSmall_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ : ℝ, 0 < δ →
      classicalSmallBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤ ε * N / log N ^ 2 := by
  have hk : 0 < alpha := by norm_num [alpha]
  obtain ⟨T, hT, hp⟩ := ninth_power_log_error_budget 0
    (show 0 < 2 / alpha ^ 2 by positivity) (show (0 : ℝ) < 3 / 4 by norm_num) hε
  refine ⟨T, hT, ?_⟩
  intro N hN δ hδ
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (2 / alpha ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) :=
      classicalSmallBudget_source_bound (hT.trans hN) hδ
    _ = (2 / alpha ^ 2) * N * log N ^ (0 : ℕ) / (N : ℝ) ^ (3 / 4 : ℝ) := by
      rw [show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num, rpow_sub hNR, rpow_one, pow_zero]
      ring
    _ ≤ _ := hp N hN
end Wu2008DoubleSieve.SeventhEighth
