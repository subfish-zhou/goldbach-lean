import MathlibNt.Wu2008DoubleSieve.NinthUpperSieveSource
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeEuler

/-!
# Finite payment bounds for the actual ninth missing mass

The full product support is rough at N^(25/206). The reciprocal bound and
complete squarefree Euler mass are generic accepted inputs; no specialized
Omega3 coefficient or source-box hypothesis is introduced.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem ninthProductSupport_rough {N m : ℕ} (hm : m ∈ ninthProductSupport N)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    ninthProfileW N ≤ (p : ℝ) := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  obtain ⟨ha, hb, _, hwa, _, hab, _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  rcases hp.dvd_mul.mp hpm with hpa | hpb
  · have h : p = t.1 := ((Nat.dvd_prime ha).mp hpa).resolve_left hp.ne_one
    simpa only [h] using hwa
  · have h : p = t.2 := ((Nat.dvd_prime hb).mp hpb).resolve_left hp.ne_one
    rw [h]
    exact hwa.trans (by exact_mod_cast hab.le)

theorem ninthProductSupport_le_N {N m : ℕ} (hN : 512 ≤ N)
    (hm : m ∈ ninthProductSupport N) : m ≤ N := by
  have h := (ninthProductSupport_balanced hN hm).2
  have hp : (N : ℝ) ^ (1 - ninthProfileK2) ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
      (show 1 - ninthProfileK2 ≤ 1 by norm_num [ninthProfileK2])
  exact_mod_cast h.trans hp

/-- Count positive varying primes by positive integers, with no extra
one per product label. -/
theorem P9_card_le_div {N m : ℕ} (hm : m ∈ ninthProductSupport N) :
    ((P9 N m).card : ℝ) ≤ (N : ℝ) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast ninthProductSupport_pos hm
  have hsub : P9 N m ⊆ Icc 1 ⌊(N : ℝ) / m⌋₊ := by
    intro c hc
    have hs : (m : ℝ) * c ≤ N := by exact_mod_cast (P9_size hm hc).le
    have hcN : (c : ℝ) ≤ (N : ℝ) / m :=
      (le_div_iff₀ hmR).mpr (by simpa only [mul_comm] using hs)
    exact mem_Icc.mpr ⟨(P9_prime hc).one_lt.le, Nat.le_floor hcN⟩
  calc
    ((P9 N m).card : ℝ) ≤ ((Icc 1 ⌊(N : ℝ) / m⌋₊).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ (N : ℝ) / m := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
        Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hmR.le)

theorem ninthSieveMissingMass_le {N q : ℕ} (hN : 512 ≤ N)
    (hq : 0 < q) (hqN : q ≤ N) :
    ninthSieveMissingMass N q ≤
      (N : ℝ) * ((1 + log N) * log N / (ninthProfileW N * log 2)) := by
  have hw : 0 < ninthProfileW N := rpow_pos_of_pos (by positivity) _
  have hr := omega3_rough_non_coprime_reciprocal_le N q (ninthProductSupport N)
    hw hq hqN
    (fun m hm => ⟨ninthProductSupport_pos hm, ninthProductSupport_le_N hN hm⟩)
    (fun m hm p hp hd => ninthProductSupport_rough hm hp hd)
  calc
    ninthSieveMissingMass N q ≤
        ∑ m ∈ (ninthProductSupport N).filter (fun m => ¬m.Coprime q), (N : ℝ) / m := by
      apply sum_le_sum
      intro m hm
      exact P9_card_le_div (mem_filter.mp hm).1
    _ = (N : ℝ) *
        ∑ m ∈ (ninthProductSupport N).filter (fun m => ¬m.Coprime q), 1 / (m : ℝ) := by
      rw [mul_sum]
      simp only [mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N)

/-- The complete divisor Euler mass, not a global count of moduli, pays
the outer 3^omega/phi weight. Its constant precedes N and all cutoffs. -/
theorem ninthSieveR2_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ D : ℕ, ∀ Z : ℝ,
      Z ≤ N → (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      ninthSieveR2 N D Z ≤
        C * N * ((1 + log N) * log N ^ 4 / (ninthProfileW N * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN D Z hZ hqN
  have hnonneg : 0 ≤ (N : ℝ) *
      ((1 + log N) * log N / (ninthProfileW N * log 2)) := by
    have := log_natCast_nonneg N
    have hw : 0 < ninthProfileW N := rpow_pos_of_pos (by positivity) _
    positivity
  calc
    ninthSieveR2 N D Z ≤ ∑ q ∈ omega3SieveModuli N D Z,
        ((3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
          ((N : ℝ) * ((1 + log N) * log N / (ninthProfileW N * log 2))) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (ninthSieveMissingMass_le hN (omega3SieveModuli_properties hq).1 (hqN q hq))
        (by positivity)
    _ = (∑ q ∈ omega3SieveModuli N D Z,
        (3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
          ((N : ℝ) * ((1 + log N) * log N / (ninthProfileW N * log 2))) :=
      (sum_mul ..).symm
    _ ≤ (C * log N ^ 3) *
        ((N : ℝ) * ((1 + log N) * log N / (ninthProfileW N * log 2))) := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun q _ _ => by positivity)).trans (hmass N (by omega) Z hZ)
    _ = _ := by ring

/-- q < floor(Q)+1 permits q=Q when Q is integral; no source-level
endpoint is removed when applying the finite bound. -/
theorem ninthSieveR2_source_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ δ : ℝ,
      0 < δ → δ < 1 / 2 →
      ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      C * N * ((1 + log N) * log N ^ 4 / (ninthProfileW N * log 2)) := by
  obtain ⟨C, hC, hbound⟩ := ninthSieveR2_finite_bound
  refine ⟨C, hC, ?_⟩
  intro N hN δ hδ hδhi
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  apply hbound N hN _ _ hg.2.2.2.1
  intro q hq
  have hqD := (omega3SieveModuli_properties hq).2.2.2
  have hDN := hg.2.2.2.2.2.2.1
  omega

theorem ninthSmallOutputBudget_le {Z : ℝ} (hZ : 0 ≤ Z) :
    ninthSmallOutputBudget Z ≤ (1 / ninthProfileK2 ^ 2) * (Z + 1) := by
  unfold ninthSmallOutputBudget
  rw [max_eq_left hZ, Nat.cast_add, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [Nat.floor_le hZ]

theorem ninthSmallOutputBudget_source_le {N : ℕ} (hN : 512 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) :
    ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      (2 / ninthProfileK2 ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hZ : sqrt ((N : ℝ) ^ (1 / 2 - δ)) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_mul (Nat.cast_nonneg N)]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [rpow_zero] using
      rpow_le_rpow_of_exponent_le hN1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  calc
    _ ≤ (1 / ninthProfileK2 ^ 2) *
        (sqrt ((N : ℝ) ^ (1 / 2 - δ)) + 1) :=
      ninthSmallOutputBudget_le (sqrt_nonneg _)
    _ ≤ (1 / ninthProfileK2 ^ 2) * (2 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

end Wu2008DoubleSieve
