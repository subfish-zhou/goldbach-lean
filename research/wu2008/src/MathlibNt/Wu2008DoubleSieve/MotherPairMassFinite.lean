import MathlibNt.Wu2008DoubleSieve.MotherPairMassKernel
namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval
noncomputable def rowPrimes (N : ℕ) (R C D : ℝ) (p : ℕ) : Finset ℕ :=
  (gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D).filter
    (fun q => p < q ∧ (q:ℝ) < R^D ∧ q.Coprime N)
noncomputable def primePairs (N : ℕ) (R A B C D : ℝ) : Finset (ℕ × ℕ) :=
  (gamma5MassPrimes R A B ×ˢ gamma5MassPrimes R C D).filter
    (fun x => x.1 < x.2 ∧ (x.2:ℝ) < R^D ∧ x.1.Coprime N ∧ x.2.Coprime N ∧ (x.1:ℝ) < R^B)
noncomputable def reciprocalPairs (U : ℝ) (N : ℕ) (R A B C D : ℝ) : ℝ :=
  ∑ x ∈ primePairs N R A B C D,
    clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) / ((x.1:ℝ)*x.2)
theorem row_mem_iff {N p q : ℕ} {R C D : ℝ}
    (hR : 1 < R) (hCD : C ≤ D) (hp : p.Prime) :
    q ∈ rowPrimes N R C D p ↔
      q ∈ gamma5MassPrimes R C D ∧ p < q ∧
        (q : ℝ) < R ^ D ∧ q.Coprime N := by
  simp only [rowPrimes, mem_filter, gamma5Mass_coordinate_mem_iff hR]
  constructor
  · rintro ⟨⟨hq, hlo, hhi⟩, hpq, hqb, hc⟩
    exact ⟨⟨hq, (gamma5Mass_start_bounds hCD _).1.trans hlo, hhi⟩, hpq, hqb, hc⟩
  · rintro ⟨⟨hq, hlo, hhi⟩, hpq, hqb, hc⟩
    have ht := (gamma5Mass_coordinate_le_iff hR hp hq).mpr hpq.le
    refine ⟨⟨hq, ?_, hhi⟩, hpq, hqb, hc⟩
    exact (min_le_right _ _).trans (max_le hlo ht)

theorem pairs_eq_rows (U : ℝ) {N : ℕ} {R A B C D : ℝ}
    (hR : 1 < R) (hCD : C ≤ D) :
    reciprocalPairs U N R A B C D =
      ∑ p ∈ (gamma5MassPrimes R A B).filter (fun p : ℕ => p.Coprime N ∧ (p:ℝ) < R^B),
        (∑ q ∈ rowPrimes N R C D p,
          clipH U (gamma5MassCoordinate R p) (gamma5MassCoordinate R q) / q) / p := by
  unfold reciprocalPairs primePairs
  rw [sum_filter, sum_product, sum_filter]
  apply sum_congr rfl
  intro p hp
  dsimp only
  have hpp := ((gamma5Mass_coordinate_mem_iff hR p).mp hp).1
  by_cases hpN : p.Coprime N ∧ (p:ℝ) < R^B
  · rw [if_pos hpN]
    rw [sum_div]
    have he : rowPrimes N R C D p =
        (gamma5MassPrimes R C D).filter
          (fun q => p < q ∧ (q : ℝ) < R ^ D ∧ q.Coprime N) := by
      ext q
      rw [Finset.mem_filter]
      exact row_mem_iff hR hCD hpp
    rw [he, sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hq : p < q ∧ (q : ℝ) < R ^ D ∧ q.Coprime N
    · rw [if_pos ⟨hq.1, hq.2.1, hpN.1, hq.2.2, hpN.2⟩, if_pos hq]
      ring
    · rw [if_neg (by tauto), if_neg hq]
  · rw [if_neg hpN]
    apply sum_eq_zero
    intro q _
    rw [if_neg (by tauto)]

theorem row_boundary {p : ℕ} {R C D Z M : ℝ}
    (hR : 1 < R) (hp : p.Prime) (hCD : C ≤ D)
    (hZ : 0 < Z) (hZC : Z ≤ R ^ C) (hM : 0 ≤ M)
    (g : ℕ → ℝ)
    (hg : ∀ q ∈ gamma5MassPrimes R
        (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D, |g q| ≤ M / q) :
    |(∑ q ∈ gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D,
        g q) -
      ∑ q ∈ (gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D).filter
        (fun q => p < q ∧ (q : ℝ) < R ^ D), g q| ≤ 3 * M / Z := by
  let P := gamma5MassPrimes R (gamma5MassSectionStart C D (gamma5MassCoordinate R p)) D
  let E := P.filter (fun q => ¬(p < q ∧ (q : ℝ) < R ^ D))
  have hsub : E ⊆ {p, ⌊R ^ D⌋₊, ⌊R ^ D⌋₊} := by
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
      · have hqb : (q : ℝ) ≤ R ^ D := by
          have hm := (gamma5Mass_coordinate_mem_iff hR q).mpr
            ⟨hqq, le_rfl, hhi⟩
          exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hm).2.2
        have heqb : (q : ℝ) = R ^ D := by
          by_contra hnq
          exact hn ⟨lt_of_le_of_ne hpq (Ne.symm he), hqb.lt_of_ne hnq⟩
        have hfloor : q = ⌊R ^ D⌋₊ := by rw [← heqb, Nat.floor_natCast]
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
    (Finset.card_le_card hsub).trans (by
      calc
        _ ≤ ({⌊R ^ D⌋₊, ⌊R ^ D⌋₊} : Finset ℕ).card + 1 := card_insert_le _ _
        _ ≤ 3 := by simp)
  have he := sum_filter_add_sum_filter_not P
    (fun q => p < q ∧ (q : ℝ) < R ^ D) g
  have heq : (∑ q ∈ P, g q) - ∑ q ∈ P.filter
      (fun q => p < q ∧ (q : ℝ) < R ^ D), g q = ∑ q ∈ E, g q := by
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


theorem upper_deletion {Z M H : ℝ} (hZ : 0 < Z) (hM : 0 ≤ M)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Z ≤ (p:ℝ) ∧ (p:ℝ) ≤ H)
    (f : ℕ → ℝ) (hf : ∀ p ∈ P, |f p| ≤ M/p) :
    |(∑ p ∈ P, f p) - ∑ p ∈ P.filter (fun p : ℕ => (p:ℝ)<H), f p| ≤ M/Z := by
  let E := P.filter (fun p : ℕ => ¬(p:ℝ)<H)
  have hsub : E ⊆ {⌊H⌋₊} := by
    intro p hp
    obtain ⟨hp,hn⟩ := mem_filter.mp hp
    have he : (p:ℝ)=H := le_antisymm (hP p hp).2 (le_of_not_gt hn)
    have he' : p=⌊H⌋₊ := by rw [← he, Nat.floor_natCast]
    simp [he']
  have hc : E.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
  have he := sum_filter_add_sum_filter_not P (fun p : ℕ => (p:ℝ)<H) f
  have heq : (∑ p ∈ P, f p) - ∑ p ∈ P.filter (fun p : ℕ => (p:ℝ)<H), f p = ∑ p ∈ E, f p := by
    dsimp [E]
    linarith
  rw [heq]
  calc
    _ ≤ ∑ p ∈ E, |f p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ E, M/Z := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).1
      exact (hf p hp').trans (div_le_div_of_nonneg_left hM hZ (hP p hp').1)
    _ = (E.card:ℝ)*(M/Z) := by simp
    _ ≤ 1*(M/Z) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := one_mul _

theorem prime_lower {N : ℕ} {a R A B α : ℝ}
    (hR : 1<R) (hA : a ≤ A) (hZ : (N:ℝ)^α ≤ R^a) :
    ∀ p ∈ gamma5MassPrimes R A B, p.Prime ∧ (N:ℝ)^α ≤ (p:ℝ) := by
  intro p hp
  obtain ⟨hpp,hlo,_⟩ := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) B)).mp hp
  exact ⟨hpp,hZ.trans ((rpow_le_rpow_of_exponent_le hR.le hA).trans hlo)⟩

end Wu2008DoubleSieve.MotherPair

