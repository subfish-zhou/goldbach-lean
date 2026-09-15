import MathlibNt.Wu2008DoubleSieve.Gamma5MassKernel
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureTriple

/-!
# Finite prime sections, exact endpoint masks, and divisor deletion

The diagonal and the strict upper source endpoint are removed explicitly.
Deleting primes dividing N costs their bounded large-prime divisor mass,
not an assumption that the enlarged product is a source box.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def gamma5MassPrimes (R A B : ℝ) : Finset ℕ :=
  primesIcc (R ^ A) (R ^ B)

noncomputable def gamma5MassRowPrimes (N : ℕ) (R C D : ℝ) (p : ℕ) : Finset ℕ :=
  (gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D).filter
    (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB ∧ q.Coprime N)

noncomputable def gamma5MassPrimePairs (N : ℕ) (R A B C D : ℝ) : Finset (ℕ × ℕ) :=
  (gamma5MassPrimes R A B ×ˢ gamma5MassPrimes R C D).filter
    (fun x => x.1 < x.2 ∧ (x.2 : ℝ) < R ^ gamma5ClassicalB ∧
      x.1.Coprime N ∧ x.2.Coprime N)

noncomputable def gamma5MassReciprocalPairs (N : ℕ) (R A B C D : ℝ) : ℝ :=
  ∑ x ∈ gamma5MassPrimePairs N R A B C D,
    gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
      ((x.1 : ℝ) * x.2)

theorem gamma5Mass_coordinate_mem_iff {R A B : ℝ} (hR : 1 < R) (p : ℕ) :
    p ∈ gamma5MassPrimes R A B ↔
      p.Prime ∧ A ≤ gamma5MassCoordinate R p ∧ gamma5MassCoordinate R p ≤ B := by
  have hR0 : 0 < R := by linarith
  rw [gamma5MassPrimes, mem_primesIcc (rpow_nonneg hR0.le _)]
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hl := log_le_log (rpow_pos_of_pos hR0 _) hlo
    have hu := log_le_log hp0 hhi
    rw [log_rpow hR0] at hl hu
    exact ⟨hp, (le_div_iff₀ (log_pos hR)).mpr hl, (div_le_iff₀ (log_pos hR)).mpr hu⟩
  · rintro ⟨hp, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    refine ⟨hp, ?_, ?_⟩
    · apply (log_le_log_iff (rpow_pos_of_pos hR0 _) hp0).mp
      rw [log_rpow hR0]
      exact (le_div_iff₀ (log_pos hR)).mp hlo
    · apply (log_le_log_iff hp0 (rpow_pos_of_pos hR0 _)).mp
      rw [log_rpow hR0]
      exact (div_le_iff₀ (log_pos hR)).mp hhi

theorem gamma5Mass_coordinate_le_iff {R : ℝ} {p q : ℕ}
    (hR : 1 < R) (hp : p.Prime) (hq : q.Prime) :
    gamma5MassCoordinate R p ≤ gamma5MassCoordinate R q ↔ p ≤ q := by
  unfold gamma5MassCoordinate
  rw [div_le_div_iff_of_pos_right (log_pos hR),
    log_le_log_iff (by exact_mod_cast hp.pos) (by exact_mod_cast hq.pos)]
  exact_mod_cast Iff.rfl

theorem gamma5Mass_row_mem_iff {N p q : ℕ} {R C D : ℝ}
    (hR : 1 < R) (hCD : C ≤ D) (hp : p.Prime) :
    q ∈ gamma5MassRowPrimes N R C D p ↔
      q ∈ gamma5MassPrimes R C D ∧ p < q ∧
        (q : ℝ) < R ^ gamma5ClassicalB ∧ q.Coprime N := by
  simp only [gamma5MassRowPrimes, mem_filter, gamma5Mass_coordinate_mem_iff hR]
  constructor
  · rintro ⟨⟨hq, hlo, hhi⟩, hpq, hqb, hc⟩
    exact ⟨⟨hq, (gamma5Mass_start_bounds hCD _).1.trans hlo, hhi⟩, hpq, hqb, hc⟩
  · rintro ⟨⟨hq, hlo, hhi⟩, hpq, hqb, hc⟩
    have ht := (gamma5Mass_coordinate_le_iff hR hp hq).mpr hpq.le
    refine ⟨⟨hq, ?_, hhi⟩, hpq, hqb, hc⟩
    exact (min_le_right _ _).trans (max_le hlo ht)

theorem gamma5Mass_pairs_eq_rows {N : ℕ} {R A B C D : ℝ}
    (hR : 1 < R) (hCD : C ≤ D) :
    gamma5MassReciprocalPairs N R A B C D =
      ∑ p ∈ (gamma5MassPrimes R A B).filter (fun p => p.Coprime N),
        (∑ q ∈ gamma5MassRowPrimes N R C D p,
          gamma5MassH (gamma5MassCoordinate R p) (gamma5MassCoordinate R q) / q) / p := by
  unfold gamma5MassReciprocalPairs gamma5MassPrimePairs
  rw [sum_filter, sum_product, sum_filter]
  apply sum_congr rfl
  intro p hp
  have hpp := ((gamma5Mass_coordinate_mem_iff hR p).mp hp).1
  by_cases hpN : p.Coprime N
  · simp only [hpN, if_true, true_and, and_true]
    rw [sum_div]
    have he : gamma5MassRowPrimes N R C D p =
        (gamma5MassPrimes R C D).filter
          (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB ∧ q.Coprime N) := by
      ext q
      exact (gamma5Mass_row_mem_iff hR hCD hpp).trans (mem_filter.symm)
    rw [he, sum_filter]
    apply sum_congr rfl
    intro q _
    split_ifs <;> ring
  · simp [hpN]

/-- Arbitrary finite prime sets, with no upper-window hypothesis. -/
theorem gamma5Mass_divisor_deletion {N : ℕ} {α M : ℝ}
    (hN : 1 < N) (hα : 0 < α) (hM : 0 ≤ M) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ))
    (g : ℕ → ℝ) (hg : ∀ p ∈ P, |g p| ≤ M / p) :
    |(∑ p ∈ P, g p) - ∑ p ∈ P.filter (fun p => p.Coprime N), g p| ≤
      M / (α * (N : ℝ) ^ α) := by
  let E := P.filter (fun p => ¬p.Coprime N)
  have he : (∑ p ∈ P, g p) - ∑ p ∈ P.filter (fun p => p.Coprime N), g p =
      ∑ p ∈ E, g p := by
    have h := sum_filter_add_sum_filter_not P (fun p => p.Coprime N) g
    dsimp [E]
    linarith
  have hsub : E ⊆ largePrimeDivisors N ((N : ℝ) ^ α) := by
    intro p hp
    obtain ⟨hp, hc⟩ := mem_filter.mp hp
    obtain ⟨hpp, hlo⟩ := hP p hp
    exact mem_largePrimeDivisors.mpr
      ⟨hpp, by simpa only [hpp.coprime_iff_not_dvd, not_not] using hc, by omega, hlo⟩
  have hcard : (E.card : ℝ) ≤ 1 / α :=
    (show (E.card : ℝ) ≤ (largePrimeDivisors N ((N : ℝ) ^ α)).card by
      exact_mod_cast card_le_card hsub).trans
        (largePrimeDivisors_card_le_inv hN (by omega) le_rfl hα)
  have hpow : 0 < (N : ℝ) ^ α := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  rw [he]
  calc
    _ ≤ ∑ p ∈ E, |g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ E, M / (N : ℝ) ^ α := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).1
      exact (hg p hp').trans
        (div_le_div_of_nonneg_left hM hpow (hP p hp').2)
    _ = (E.card : ℝ) * (M / (N : ℝ) ^ α) := by simp
    _ ≤ (1 / α) * (M / (N : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem gamma5Mass_row_boundary {p : ℕ} {R C D Z M : ℝ}
    (hR : 1 < R) (hp : p.Prime) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB)
    (hZ : 0 < Z) (hZC : Z ≤ R ^ C) (hM : 0 ≤ M)
    (g : ℕ → ℝ)
    (hg : ∀ q ∈ gamma5MassPrimes R
        (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D, |g q| ≤ M / q) :
    |(∑ q ∈ gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D,
        g q) -
      ∑ q ∈ (gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D).filter
        (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB), g q| ≤ 3 * M / Z := by
  let P := gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D
  let E := P.filter (fun q => ¬(p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB))
  have hsub : E ⊆ {p, ⌊R ^ gamma5ClassicalB⌋₊, ⌊R ^ D⌋₊} := by
    intro q hq
    obtain ⟨hq, hn⟩ := mem_filter.mp hq
    obtain ⟨hqq, hlo, hhi⟩ := (gamma5Mass_coordinate_mem_iff hR q).mp hq
    have ht := gamma5Mass_start_bounds hCD (gamma5MassCoordinate R p)
    by_cases htD : gamma5MassCoordinate R p ≤ D
    · have hpcoord : gamma5MassCoordinate R p ≤ gamma5MassCoordinate R q :=
        (le_min htD (le_max_right _ _)).trans hlo
      have hpq := (gamma5Mass_coordinate_le_iff hR hp hqq).mp hpcoord
      by_cases he : q = p
      · simp [he]
      · have hqb : (q : ℝ) ≤ R ^ gamma5ClassicalB := by
          have hm := (gamma5Mass_coordinate_mem_iff hR q).mpr
            ⟨hqq, le_rfl, hhi.trans hD⟩
          exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hm).2.2
        have heqb : (q : ℝ) = R ^ gamma5ClassicalB := by
          by_contra hnq
          exact hn ⟨lt_of_le_of_ne hpq (Ne.symm he), hqb.lt_of_ne hnq⟩
        have hfloor : q = ⌊R ^ gamma5ClassicalB⌋₊ := by rw [← heqb, Nat.floor_natCast]
        simp [hfloor]
    · have hs : gamma5MassSectionStart C D (gamma5MassCoordinate R p) = D :=
        min_eq_left ((le_of_lt (lt_of_not_ge htD)).trans (le_max_right _ _))
      rw [hs] at hlo
      have heq : gamma5MassCoordinate R q = D := le_antisymm hhi hlo
      have hpow := primeOrdered_coordinate_rpow hR hqq
      change R ^ gamma5MassCoordinate R q = (q : ℝ) at hpow
      rw [heq] at hpow
      have hfloor : q = ⌊R ^ D⌋₊ := by rw [hpow, Nat.floor_natCast]
      simp [hfloor]
  have hcard : E.card ≤ 3 :=
    (card_le_card hsub).trans (by
      calc
        _ ≤ 1 + ({⌊R ^ gamma5ClassicalB⌋₊, ⌊R ^ D⌋₊} : Finset ℕ).card := card_insert_le _ _
        _ ≤ 3 := by have := card_insert_le ⌊R ^ gamma5ClassicalB⌋₊ {⌊R ^ D⌋₊}; simp at this; omega)
  have he := sum_filter_add_sum_filter_not P
    (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB) g
  have heq : (∑ q ∈ P, g q) - ∑ q ∈ P.filter
      (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB), g q = ∑ q ∈ E, g q := by
    dsimp [E]
    linarith
  change |(∑ q ∈ P, g q) - _| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ q ∈ E, |g q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ E, M / Z := by
      apply sum_le_sum
      intro q hq
      have hqm := (mem_filter.mp hq).1
      have hqc := (gamma5Mass_coordinate_mem_iff hR q).mp hqm
      have hqC := (gamma5Mass_coordinate_mem_iff hR q).mpr
        ⟨hqc.1, (gamma5Mass_start_bounds hCD _).1.trans hqc.2.1, hqc.2.2⟩
      have hlow := ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hqC).2.1
      exact (hg q hqm).trans (div_le_div_of_nonneg_left hM hZ (hZC.trans hlow))
    _ = (E.card : ℝ) * (M / Z) := by simp
    _ ≤ 3 * (M / Z) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

end Wu2008DoubleSieve
