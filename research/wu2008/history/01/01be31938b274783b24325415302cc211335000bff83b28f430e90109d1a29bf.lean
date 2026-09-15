import MathlibNt.Wu2008DoubleSieve.ClosedLowerWeight
import MathlibNt.Wu2008DoubleSieve.Buchstab

/-!
# A quotient-sequence variable-cutoff S3 comparison

Buchstab at the moving cutoff `sqrt(N/(a*b))` produces the third triple
range. The excluded repeated factor `c=b` is retained and then paid by the
proved pair endpoint budget, rather than asserted negligible.
This is inspired by Wu (2008), Lemma 2.2, not a literal unscaled-carrier
identity. If the moving cutoff crosses a selected prime, division changes
the sifting condition; the source-carrier transport is a separate obligation.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- The finite bounding windows introduce no restriction beyond the source
prime ranges and the strict square-root size condition. -/
theorem mem_lowerPairs_source {N M a b : ℕ} {z w : ℝ} :
    (a, b) ∈ lowerPairs N M z w ↔
      a.Prime ∧ b.Prime ∧ (a * b).Coprime M ∧
        z ≤ (a : ℝ) ∧ w ≤ (b : ℝ) ∧ a < b ∧
        (b : ℝ) < Real.sqrt ((N : ℝ) / a) := by
  constructor
  · intro ht
    obtain ⟨hwin, hab, hsize⟩ := mem_filter.mp ht
    obtain ⟨hwa, hwb⟩ := mem_product.mp hwin
    obtain ⟨ha, haM, hza, _⟩ := mem_primeWindow.mp hwa
    obtain ⟨hb, hbM, hwb, _⟩ := mem_primeWindow.mp hwb
    exact ⟨ha, hb, Nat.coprime_mul_iff_left.mpr ⟨haM, hbM⟩,
      hza, hwb, hab, (lower_pair_size_iff ha.pos).mp hsize⟩
  · rintro ⟨ha, hb, hcop, hza, hwb, hab, hsize⟩
    have hs := (lower_pair_size_iff ha.pos).mpr hsize
    have hb1 : 1 ≤ b ^ 2 := by have := hb.two_le; nlinarith
    have ha1 : 1 ≤ a := ha.one_lt.le
    have habsq : a ≤ a * b ^ 2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left a hb1
    have hbsq : b ≤ b ^ 2 := by have := hb.two_le; nlinarith
    have hbsqa : b ^ 2 ≤ a * b ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (b ^ 2) ha1
    have haN : a < N + 1 := by omega
    have hbN : b < N + 1 := by omega
    obtain ⟨haM, hbM⟩ := Nat.coprime_mul_iff_left.mp hcop
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_primeWindow.mpr ⟨ha, haM, hza, by exact_mod_cast haN⟩,
        mem_primeWindow.mpr ⟨hb, hbM, hwb, by exact_mod_cast hbN⟩⟩, hab, hs⟩

theorem sieveCount_nonneg (N d M : ℕ) (z : ℝ) :
    0 ≤ sieveCount N d M z := Int.natCast_nonneg _

theorem sieveCount_antitone (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    sieveCount N d M w ≤ sieveCount N d M z := by
  apply Int.ofNat_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, hprime, hd,
    fun q hq hqM hqz => hs q hq hqM (hqz.trans_le hzw)⟩

/-- No assumption about whether the moving cutoff lies above `b` is needed. -/
theorem variable_cutoff_pair_bound (N a b : ℕ) (T : ℝ) :
    sieveCount N (a * b) (N * a) (b : ℝ) ≤
      sieveCount N (a * b) (N * a) T +
        (∑ c ∈ (primeWindow N (b : ℝ) T).filter (fun c => b < c),
          sieveCount N (a * b * c) (N * a) (c : ℝ)) +
        sieveCount N (a * b * b) (N * a) (b : ℝ) := by
  have hr := sieveCount_nonneg N (a * b * b) (N * a) (b : ℝ)
  have ht : 0 ≤ ∑ c ∈ (primeWindow N (b : ℝ) T).filter (fun c => b < c),
      sieveCount N (a * b * c) (N * a) (c : ℝ) :=
    sum_nonneg (fun c _ => sieveCount_nonneg N (a * b * c) (N * a) c)
  by_cases hbT : (b : ℝ) ≤ T
  · have he := goldbach_buchstab N (a * b) (N * a) hbT
    have hsub : primeWindow (N * a) (b : ℝ) T ⊆
        insert b ((primeWindow N (b : ℝ) T).filter (fun c => b < c)) := by
      intro c hc
      obtain ⟨hcp, hcop, hbc, hcT⟩ := mem_primeWindow.mp hc
      by_cases hcb : c = b
      · simp [hcb]
      · apply mem_insert_of_mem
        exact mem_filter.mpr
          ⟨mem_primeWindow.mpr
            ⟨hcp, (Nat.coprime_mul_iff_right.mp hcop).1, hbc, hcT⟩,
            by
              have : b ≤ c := by exact_mod_cast hbc
              omega⟩
    have hsum := sum_le_sum_of_subset_of_nonneg hsub
      (fun c _ _ => sieveCount_nonneg N (a * b * c) (N * a) c)
    have hnot : b ∉ (primeWindow N (b : ℝ) T).filter (fun c => b < c) := by simp
    rw [sum_insert hnot] at hsum
    omega
  · have hm := sieveCount_antitone N (a * b) (N * a) (le_of_not_ge hbT)
    omega

theorem repeated_pair_eq_endpoint_loss {N a b : ℕ} {z w : ℝ}
    (ht : (a, b) ∈ lowerPairs N N z w) :
    sieveCount N (a * b * b) (N * a) (b : ℝ) =
      ((sieveEndpointLoss N (a * b) (N * a) (b : ℝ)).card : ℤ) := by
  obtain ⟨hwin, hab, _⟩ := mem_filter.mp ht
  obtain ⟨hwa, hwb⟩ := mem_product.mp hwin
  obtain ⟨ha, _, _, _⟩ := mem_primeWindow.mp hwa
  obtain ⟨hb, hbN, _, _⟩ := mem_primeWindow.mp hwb
  have hbNa : b.Coprime (N * a) := Nat.coprime_mul_iff_right.mpr
    ⟨hbN, (Nat.coprime_primes hb ha).mpr (by omega)⟩
  have he := sieveCount_prime_endpoint N (a * b) (N * a) hb hbNa
  have he' := sieveCount_eq_closed_add_loss N (a * b) (N * a) (b : ℝ)
  change sieveCount N (a * b) (N * a) (b : ℝ) =
    sieveCountLE N (a * b) (N * a) (b : ℝ) +
      sieveCount N (a * b * b) (N * a) (b : ℝ) at he
  omega

noncomputable def variableS3Main (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    sieveCount N (t.1 * t.2) (N * t.1)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))

noncomputable def variableS3Triples (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    ∑ c ∈ (primeWindow N (t.2 : ℝ)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter (fun c => t.2 < c),
      sieveCount N (t.1 * t.2 * c) (N * t.1) (c : ℝ)

/-- Exact finite error carrier for the repeated second prime. -/
theorem lowerS3_le_variable_add_square_error (N : ℕ) (z w : ℝ) :
    lowerS3 N z w ≤ variableS3Main N z w + variableS3Triples N z w +
      ∑ t ∈ lowerPairs N N z w,
        ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ) := by
  have h := sum_le_sum (s := (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w))
    (fun t _ => variable_cutoff_pair_bound N t.1 t.2
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2))))
  simp only [sum_add_distrib] at h
  have hr :
      (∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
        sieveCount N (t.1 * t.2 * t.2) (N * t.1) (t.2 : ℝ)) ≤
      ∑ t ∈ lowerPairs N N z w,
        ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ) := by
    calc
      _ = ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
          ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℤ) :=
        sum_congr rfl (fun t ht => repeated_pair_eq_endpoint_loss (mem_filter.mp ht).1)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => Int.natCast_nonneg _)
  change lowerS3 N z w ≤ variableS3Main N z w + variableS3Triples N z w + _ at h
  omega

/-- The quotient S3 comparison, with its repeated-prime term paid
uniformly over the full pair range. All sieve counts here are strict. -/
theorem lowerS3_le_variable_add_paid_error {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    {κ w : ℝ} (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (hzw : (N : ℝ) ^ κ ≤ w) :
    (lowerS3 N ((N : ℝ) ^ κ) w : ℝ) ≤
      (variableS3Main N ((N : ℝ) ^ κ) w : ℝ) +
        (variableS3Triples N ((N : ℝ) ^ κ) w : ℝ) +
        2 * (1 / κ) ^ 2 * (N : ℝ) ^ (1 - κ) := by
  have h := lowerS3_le_variable_add_square_error N ((N : ℝ) ^ κ) w
  have hc :
      (lowerS3 N ((N : ℝ) ^ κ) w : ℝ) ≤
        (variableS3Main N ((N : ℝ) ^ κ) w : ℝ) +
          (variableS3Triples N ((N : ℝ) ^ κ) w : ℝ) +
          ∑ t ∈ lowerPairs N N ((N : ℝ) ^ κ) w,
            ((sieveEndpointLoss N (t.1 * t.2) (N * t.1) (t.2 : ℝ)).card : ℝ) := by
    exact_mod_cast h
  have hb := pair_endpoint_sum_le hN he hκ hz hzw
  have hpow : (N : ℝ) / (N : ℝ) ^ κ = (N : ℝ) ^ (1 - κ) := by
    rw [Real.rpow_sub (by positivity : (0 : ℝ) < N), Real.rpow_one]
  rw [hpow] at hb
  linarith

theorem variableS3_eventually {κ σ : ℝ} (hκ : 0 < κ) (hκσ : κ < σ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      (lowerS3 N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) ≤
        (variableS3Main N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) +
          (variableS3Triples N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) +
          2 * (1 / κ) ^ 2 * (N : ℝ) ^ (1 - κ) := by
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ :=
    ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz, Filter.eventually_ge_atTop (4 : ℕ)] with N hzN hN
  intro he
  exact lowerS3_le_variable_add_paid_error hN he hκ hzN
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) hκσ.le)

end Wu2008DoubleSieve
