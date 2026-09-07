import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruple

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

-- The sigma coordinates follow the production summation order: t, s, r, q.
abbrev GoldbachG11Label := Σ _t : ℕ, Σ _s : ℕ, Σ _r : ℕ, ℕ

noncomputable def goldbachG11Labels (N : ℕ) (z b : ℝ) : Finset GoldbachG11Label :=
  (goldbachClosedPrimes N z b).sigma fun t =>
    (goldbachClosedPrimes N z t).sigma fun s =>
      (goldbachClosedPrimes N z s).sigma fun r =>
        goldbachClosedPrimes N r s

def goldbachG11LabelProd (v : GoldbachG11Label) : ℕ :=
  v.2.2.1 * v.2.2.2 * v.2.1 * v.1

theorem goldbachG11Labels_sum (N : ℕ) (z b : ℝ) (f : GoldbachG11Label → ℤ) :
    ∑ v ∈ goldbachG11Labels N z b, f v =
      ∑ t ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z t,
          ∑ r ∈ goldbachClosedPrimes N z s,
            ∑ q ∈ goldbachClosedPrimes N r s, f ⟨t, s, r, q⟩ := by
  simp [goldbachG11Labels, Finset.sum_sigma']

theorem goldbachWeightG11_eq_label_sum (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachWeightG11 A N z b =
      ∑ v ∈ goldbachG11Labels N z b,
        literalH A (N * v.2.2.1) (goldbachG11LabelProd v) v.2.2.2 := by
  rw [goldbachG11Labels_sum]
  rfl

theorem mem_goldbachG11Labels_iff {N r q s t : ℕ} {z b : ℝ} :
    (⟨t, s, r, q⟩ : GoldbachG11Label) ∈ goldbachG11Labels N z b ↔
      r.Prime ∧ q.Prime ∧ s.Prime ∧ t.Prime ∧
        Nat.Coprime (r * q * s * t) N ∧
        z ≤ (r : ℝ) ∧ r ≤ q ∧ q ≤ s ∧ s ≤ t ∧ (t : ℝ) ≤ b := by
  simp only [goldbachG11Labels, Finset.mem_sigma, mem_goldbachClosedPrimes_iff]
  constructor
  · rintro ⟨⟨ht, htN, _, htb⟩, ⟨hs, hsN, _, hst⟩,
      ⟨hr, hrN, hzr, _⟩, hq, hqN, hrq, hqs⟩
    refine ⟨hr, hq, hs, ht, ?_, hzr, ?_, ?_, ?_, htb⟩
    · exact (((hr.coprime_iff_not_dvd.mpr hrN).mul_left
        (hq.coprime_iff_not_dvd.mpr hqN)).mul_left
        (hs.coprime_iff_not_dvd.mpr hsN)).mul_left
        (ht.coprime_iff_not_dvd.mpr htN)
    · exact_mod_cast hrq
    · exact_mod_cast hqs
    · exact_mod_cast hst
  · rintro ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, hst, htb⟩
    rcases (Nat.coprime_mul_iff_left.mp hcop) with ⟨hrqs, htN⟩
    rcases (Nat.coprime_mul_iff_left.mp hrqs) with ⟨hrqN, hsN⟩
    rcases (Nat.coprime_mul_iff_left.mp hrqN) with ⟨hrN, hqN⟩
    have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
    have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
    have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
    exact ⟨⟨ht, ht.coprime_iff_not_dvd.mp htN,
        ((hzr.trans hrqR).trans hqsR).trans hstR, htb⟩,
      ⟨hs, hs.coprime_iff_not_dvd.mp hsN, (hzr.trans hrqR).trans hqsR, hstR⟩,
      ⟨hr, hr.coprime_iff_not_dvd.mp hrN, hzr, hrqR.trans hqsR⟩,
      hq, hq.coprime_iff_not_dvd.mp hqN, hrqR, hqsR⟩

theorem goldbachG11LabelProd_pos {N : ℕ} {z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b) : 0 < goldbachG11LabelProd v := by
  rcases v with ⟨t, s, r, q⟩
  rcases mem_goldbachG11Labels_iff.mp hv with ⟨hr, hq, hs, ht, _⟩
  exact mul_pos (mul_pos (mul_pos hr.pos hq.pos) hs.pos) ht.pos

theorem goldbachG11_survives_one_iff (x : ℝ) (m : ℕ) :
    SurvivesSieve 1 x m ↔ ∀ ell : ℕ, ell.Prime → ell ∣ m → x ≤ (ell : ℝ) := by
  constructor
  · intro h ell hp hm
    exact h ell hp hm hp.not_dvd_one
  · intro h ell hp hm _
    exact h ell hp hm

theorem goldbachG11_survives_one (x : ℝ) : SurvivesSieve 1 x 1 := by
  intro ell hp hm
  exact (hp.not_dvd_one hm).elim

noncomputable def goldbachG11QuotientPairs (N : ℕ) (ε : ℝ) (d : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((range (N + 1)).product (Icc 1 N)).filter fun pm =>
    pm.1.Prime ∧ (pm.1 : ℝ) < (1 - ε) * N ∧ pm.1 + d * pm.2 = N

noncomputable def goldbachG11RoughPairs (N : ℕ) (ε : ℝ) (v : GoldbachG11Label) :
    Finset (ℕ × ℕ) := by
  classical
  exact (goldbachG11QuotientPairs N ε (goldbachG11LabelProd v)).filter fun pm =>
    SurvivesSieve 1 v.2.2.2 pm.2

noncomputable def goldbachG11RoughCount (N : ℕ) (ε : ℝ) (v : GoldbachG11Label) : ℤ :=
  ((goldbachG11RoughPairs N ε v).card : ℤ)

theorem mem_goldbachG11QuotientPairs_iff {N d p m : ℕ} {ε : ℝ} :
    (p, m) ∈ goldbachG11QuotientPairs N ε d ↔
      p ≤ N ∧ 1 ≤ m ∧ m ≤ N ∧ p.Prime ∧
        (p : ℝ) < (1 - ε) * N ∧ p + d * m = N := by
  classical
  rw [goldbachG11QuotientPairs, Finset.mem_filter]
  constructor
  · rintro ⟨hpm, hp, hcut, heq⟩
    rcases Finset.mem_product.mp hpm with ⟨hpN, hm⟩
    exact ⟨by simpa using hpN, (Finset.mem_Icc.mp hm).1,
      (Finset.mem_Icc.mp hm).2, hp, hcut, heq⟩
  · rintro ⟨hpN, hm1, hmN, hp, hcut, heq⟩
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_Icc.mpr ⟨hm1, hmN⟩⟩, hp, hcut, heq⟩

theorem mem_goldbachG11RoughPairs_iff {N p m : ℕ} {ε : ℝ} {v : GoldbachG11Label} :
    (p, m) ∈ goldbachG11RoughPairs N ε v ↔
      p ≤ N ∧ 1 ≤ m ∧ m ≤ N ∧ p.Prime ∧
        (p : ℝ) < (1 - ε) * N ∧ p + goldbachG11LabelProd v * m = N ∧
        ∀ ell : ℕ, ell.Prime → ell ∣ m → (v.2.2.2 : ℝ) ≤ ell := by
  classical
  simp only [goldbachG11RoughPairs, Finset.mem_filter,
    mem_goldbachG11QuotientPairs_iff, goldbachG11_survives_one_iff]
  tauto

theorem goldbachG11_difference_data {N n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hn : n ∈ goldbachDifferenceCarrier N ε) :
    1 ≤ n ∧ n ≤ N ∧ (N - n).Prime ∧ ((N - n : ℕ) : ℝ) < (1 - ε) * N := by
  rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
  rcases (mem_goldbachPrimeCarrier_iff hε).mp hp with ⟨hp, hcut⟩
  have hpN : p < N := by
    have : (p : ℝ) < N := by
      nlinarith [mul_nonneg hε (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast this
  have hsub : N - (N - p) = p := by omega
  rw [hsub]
  exact ⟨by omega, Nat.sub_le N p, hp, hcut⟩

theorem goldbachG11_quotient_forward {N n d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hd : 0 < d) (hn : n ∈ goldbachDifferenceCarrier N ε) (hdn : d ∣ n) :
    (N - n, n / d) ∈ goldbachG11QuotientPairs N ε d := by
  rcases goldbachG11_difference_data hε hn with ⟨hn1, hnN, hp, hcut⟩
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
  have hm1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd
  exact mem_goldbachG11QuotientPairs_iff.mpr
    ⟨Nat.sub_le N n, hm1, (Nat.div_le_self n d).trans hnN, hp, hcut, by omega⟩

theorem goldbachG11_quotient_backward {N d p m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hpm : (p, m) ∈ goldbachG11QuotientPairs N ε d) :
    d * m ∈ goldbachDifferenceCarrier N ε ∧
      d ∣ d * m ∧ N - d * m = p := by
  rcases mem_goldbachG11QuotientPairs_iff.mp hpm with ⟨_, _, _, hp, hcut, heq⟩
  refine ⟨?_, dvd_mul_right d m, by omega⟩
  exact Finset.mem_image.mpr
    ⟨p, (mem_goldbachPrimeCarrier_iff hε).mpr ⟨hp, hcut⟩, by omega⟩

theorem goldbachG11_quotient_cast {N n d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hd : 0 < d) (hn : n ∈ goldbachDifferenceCarrier N ε) (hdn : d ∣ n) :
    ((n / d : ℕ) : ℝ) = (n : ℝ) / d ∧
      ((N - n : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = N := by
  have hpair := goldbachG11_quotient_forward hε hd hn hdn
  constructor
  · apply (eq_div_iff (show (d : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd)).mpr
    exact_mod_cast Nat.div_mul_cancel hdn
  · exact_mod_cast (mem_goldbachG11QuotientPairs_iff.mp hpair).2.2.2.2.2

noncomputable def goldbachG11QuotientEquiv (N : ℕ) (ε : ℝ) (d : ℕ)
    (hε : 0 ≤ ε) (hd : 0 < d) :
    {n // n ∈ goldbachDifferenceCarrier N ε ∧ d ∣ n} ≃
      {pm // pm ∈ goldbachG11QuotientPairs N ε d} where
  toFun n := ⟨(N - n.1, n.1 / d), goldbachG11_quotient_forward hε hd n.2.1 n.2.2⟩
  invFun pm := ⟨d * pm.1.2, (goldbachG11_quotient_backward hε pm.2).1,
    (goldbachG11_quotient_backward hε pm.2).2.1⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.mul_div_cancel' n.2.2
  right_inv pm := by
    apply Subtype.ext
    apply Prod.ext
    · exact (goldbachG11_quotient_backward hε pm.2).2.2
    · exact Nat.mul_div_right _ hd

open Classical in
theorem goldbachG11RoughCount_eq_filter (N : ℕ) (ε : ℝ) (v : GoldbachG11Label)
    (hε : 0 ≤ ε) (hv : 0 < goldbachG11LabelProd v) :
    goldbachG11RoughCount N ε v =
      (((goldbachDifferenceCarrier N ε).filter fun n =>
        goldbachG11LabelProd v ∣ n ∧
          SurvivesSieve 1 v.2.2.2 (n / goldbachG11LabelProd v)).card : ℤ) := by
  classical
  unfold goldbachG11RoughCount
  congr 1
  symm
  apply Finset.card_bij (fun n _ => (N - n, n / goldbachG11LabelProd v))
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hd, hrough⟩
    exact Finset.mem_filter.mpr
      ⟨goldbachG11_quotient_forward hε hv hnA hd, hrough⟩
  · intro a ha b hb hab
    have haD := (Finset.mem_filter.mp ha).2.1
    have hbD := (Finset.mem_filter.mp hb).2.1
    have hm := congrArg Prod.snd hab
    dsimp at hm
    calc
      a = goldbachG11LabelProd v * (a / goldbachG11LabelProd v) :=
        (Nat.mul_div_cancel' haD).symm
      _ = goldbachG11LabelProd v * (b / goldbachG11LabelProd v) := by rw [hm]
      _ = b := Nat.mul_div_cancel' hbD
  · rintro ⟨p, m⟩ hpm
    rcases Finset.mem_filter.mp hpm with ⟨hpm, hrough⟩
    rcases goldbachG11_quotient_backward hε hpm with ⟨hnA, hd, hp⟩
    have hm : goldbachG11LabelProd v * m / goldbachG11LabelProd v = m :=
      Nat.mul_div_right _ hv
    refine ⟨goldbachG11LabelProd v * m, Finset.mem_filter.mpr ⟨hnA, hd, ?_⟩, ?_⟩
    · simpa only [hm] using hrough
    · exact Prod.ext hp hm

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig