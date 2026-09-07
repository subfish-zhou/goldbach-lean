import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughQuotient

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

-- Coordinates are t, s, q, k; equal prime coordinates remain separate labels.
abbrev GoldbachG11SwitchedBody := Σ _t : ℕ, Σ _s : ℕ, Σ _q : ℕ, ℕ

def goldbachG11SwitchedBodyProd (u : GoldbachG11SwitchedBody) : ℕ :=
  u.2.2.1 * u.2.1 * u.1 * u.2.2.2

noncomputable def goldbachG11SwitchedBodies (N : ℕ) (z b : ℝ) :
    Finset GoldbachG11SwitchedBody := by
  classical
  exact ((goldbachClosedPrimes N z b).sigma fun t =>
    (goldbachClosedPrimes N z t).sigma fun s =>
      (goldbachClosedPrimes N z s).sigma fun _q => Icc 1 N).filter fun u =>
        SurvivesSieve 1 u.2.2.1 u.2.2.2 ∧ goldbachG11SwitchedBodyProd u < N

theorem mem_goldbachG11SwitchedBodies_iff {N t s q k : ℕ} {z b : ℝ} :
    (⟨t, s, q, k⟩ : GoldbachG11SwitchedBody) ∈ goldbachG11SwitchedBodies N z b ↔
      q.Prime ∧ s.Prime ∧ t.Prime ∧ Nat.Coprime (q * s * t) N ∧
        z ≤ (q : ℝ) ∧ q ≤ s ∧ s ≤ t ∧ (t : ℝ) ≤ b ∧
        1 ≤ k ∧ k ≤ N ∧ SurvivesSieve 1 q k ∧ q * s * t * k < N := by
  classical
  rw [goldbachG11SwitchedBodies, Finset.mem_filter]
  simp only [Finset.mem_sigma,
    mem_goldbachClosedPrimes_iff, Finset.mem_Icc, goldbachG11SwitchedBodyProd]
  constructor
  · rintro ⟨⟨⟨ht, htN, _, htb⟩, ⟨hs, hsN, _, hst⟩,
      ⟨hq, hqN, hzq, hqs⟩, hk1, hkN⟩, hrough, hB⟩
    exact ⟨hq, hs, ht,
      ((hq.coprime_iff_not_dvd.mpr hqN).mul_left
        (hs.coprime_iff_not_dvd.mpr hsN)).mul_left
        (ht.coprime_iff_not_dvd.mpr htN),
      hzq, by exact_mod_cast hqs, by exact_mod_cast hst, htb, hk1, hkN, hrough, hB⟩
  · rintro ⟨hq, hs, ht, hcop, hzq, hqs, hst, htb, hk1, hkN, hrough, hB⟩
    obtain ⟨hqsN, htN⟩ := Nat.coprime_mul_iff_left.mp hcop
    obtain ⟨hqN, hsN⟩ := Nat.coprime_mul_iff_left.mp hqsN
    have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
    have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
    exact ⟨⟨⟨ht, ht.coprime_iff_not_dvd.mp htN, (hzq.trans hqsR).trans hstR, htb⟩,
      ⟨hs, hs.coprime_iff_not_dvd.mp hsN, hzq.trans hqsR, hstR⟩,
      ⟨hq, hq.coprime_iff_not_dvd.mp hqN, hzq, hqsR⟩, hk1, hkN⟩, hrough, hB⟩

theorem goldbachG11SwitchedBodyProd_pos {N : ℕ} {z b : ℝ}
    {u : GoldbachG11SwitchedBody} (hu : u ∈ goldbachG11SwitchedBodies N z b) :
    0 < goldbachG11SwitchedBodyProd u := by
  rcases u with ⟨t, s, q, k⟩
  obtain ⟨hq, hs, ht, _, _, _, _, _, hk, _⟩ :=
    mem_goldbachG11SwitchedBodies_iff.mp hu
  exact mul_pos (mul_pos (mul_pos hq.pos hs.pos) ht.pos) hk

noncomputable def goldbachG11FirstPrimeFiber (N : ℕ) (eps z : ℝ)
    (u : GoldbachG11SwitchedBody) : Finset ℕ := by
  classical
  exact (goldbachClosedPrimes N z u.2.2.1).filter fun r =>
    eps * N < (r * goldbachG11SwitchedBodyProd u : ℕ) ∧
      r * goldbachG11SwitchedBodyProd u < N ∧
        (N - r * goldbachG11SwitchedBodyProd u).Prime

theorem mem_goldbachG11FirstPrimeFiber_iff {N r : ℕ} {eps z : ℝ}
    {u : GoldbachG11SwitchedBody} :
    r ∈ goldbachG11FirstPrimeFiber N eps z u ↔
      r.Prime ∧ ¬r ∣ N ∧ z ≤ (r : ℝ) ∧ r ≤ u.2.2.1 ∧
        eps * N < (r * goldbachG11SwitchedBodyProd u : ℕ) ∧
          r * goldbachG11SwitchedBodyProd u < N ∧
            (N - r * goldbachG11SwitchedBodyProd u).Prime := by
  classical
  simp only [goldbachG11FirstPrimeFiber, Finset.mem_filter,
    mem_goldbachClosedPrimes_iff, Nat.cast_le]
  tauto

theorem goldbachG11FirstPrimeFiber_interval_iff {N r : ℕ} {eps z : ℝ}
    {u : GoldbachG11SwitchedBody} (hB : 0 < goldbachG11SwitchedBodyProd u) :
    r ∈ goldbachG11FirstPrimeFiber N eps z u ↔
      r ∈ goldbachClosedPrimes N z u.2.2.1 ∧
        eps * N / goldbachG11SwitchedBodyProd u < (r : ℝ) ∧
          (r : ℝ) < (N : ℝ) / goldbachG11SwitchedBodyProd u ∧
            (N - r * goldbachG11SwitchedBodyProd u).Prime := by
  classical
  have hBR : (0 : ℝ) < goldbachG11SwitchedBodyProd u := by exact_mod_cast hB
  simp only [goldbachG11FirstPrimeFiber, Finset.mem_filter,
    div_lt_iff₀ hBR, lt_div_iff₀ hBR, Nat.cast_mul]
  have hcast : r * goldbachG11SwitchedBodyProd u < N ↔
      (r : ℝ) * goldbachG11SwitchedBodyProd u < N := by
    exact_mod_cast (Iff.rfl : r * goldbachG11SwitchedBodyProd u < N ↔
      r * goldbachG11SwitchedBodyProd u < N)
  rw [hcast]

theorem goldbachG11FirstPrimeFiber_coprime_iff {N r : ℕ} {eps z : ℝ}
    {u : GoldbachG11SwitchedBody} (hr : r ∈ goldbachG11FirstPrimeFiber N eps z u) :
    Nat.Coprime (r * goldbachG11SwitchedBodyProd u) N ↔
      Nat.Coprime (goldbachG11SwitchedBodyProd u) N := by
  obtain ⟨hp, hNd, _⟩ := mem_goldbachG11FirstPrimeFiber_iff.mp hr
  rw [Nat.coprime_mul_iff_left]
  exact and_iff_right (hp.coprime_iff_not_dvd.mpr hNd)

noncomputable def goldbachG11GoodSwitchedBodies (N : ℕ) (z b : ℝ) :
    Finset GoldbachG11SwitchedBody := by
  classical
  exact (goldbachG11SwitchedBodies N z b).filter fun u =>
    Nat.Coprime (goldbachG11SwitchedBodyProd u) N

theorem mem_goldbachG11GoodSwitchedBodies_iff {N : ℕ} {z b : ℝ}
    {u : GoldbachG11SwitchedBody} :
    u ∈ goldbachG11GoodSwitchedBodies N z b ↔
      u ∈ goldbachG11SwitchedBodies N z b ∧
        Nat.Coprime (goldbachG11SwitchedBodyProd u) N := by
  classical
  exact Finset.mem_filter

noncomputable def goldbachG11SwitchedTotal (N : ℕ) (eps z b : ℝ) : ℤ :=
  ∑ u ∈ goldbachG11SwitchedBodies N z b,
    ((goldbachG11FirstPrimeFiber N eps z u).card : ℤ)

noncomputable def goldbachG11GoodSwitchedTotal (N : ℕ) (eps z b : ℝ) : ℤ :=
  ∑ u ∈ goldbachG11GoodSwitchedBodies N z b,
    ((goldbachG11FirstPrimeFiber N eps z u).card : ℤ)

noncomputable def goldbachG11BadSwitchedTotal (N : ℕ) (eps z b : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (goldbachG11SwitchedBodies N z b).filter
      (fun u => ¬Nat.Coprime (goldbachG11SwitchedBodyProd u) N),
    ((goldbachG11FirstPrimeFiber N eps z u).card : ℤ)

theorem goldbachG11SwitchedTotal_eq_good_add_bad (N : ℕ) (eps z b : ℝ) :
    goldbachG11SwitchedTotal N eps z b =
      goldbachG11GoodSwitchedTotal N eps z b + goldbachG11BadSwitchedTotal N eps z b := by
  classical
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem goldbachG11SwitchedTotal_sub_good_nonneg (N : ℕ) (eps z b : ℝ) :
    0 ≤ goldbachG11SwitchedTotal N eps z b - goldbachG11GoodSwitchedTotal N eps z b := by
  rw [goldbachG11SwitchedTotal_eq_good_add_bad, add_sub_cancel_left]
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig