import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughQuotient

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachG11RSquareException (A : Finset ℕ) (v : GoldbachG11Label) :
    Finset ℕ := by
  classical
  exact A.filter fun n =>
    goldbachG11LabelProd v ∣ n ∧ v.2.2.1 < v.2.2.2 ∧ v.2.2.1 ^ 2 ∣ n

noncomputable def goldbachG11NException (A : Finset ℕ) (N : ℕ) (v : GoldbachG11Label) :
    Finset ℕ := by
  classical
  exact A.filter fun n => goldbachG11LabelProd v ∣ n ∧ ¬Nat.Coprime n N

noncomputable def goldbachG11RSquareCount (A : Finset ℕ) (v : GoldbachG11Label) : ℤ :=
  ((goldbachG11RSquareException A v).card : ℤ)

noncomputable def goldbachG11NCount (A : Finset ℕ) (N : ℕ) (v : GoldbachG11Label) : ℤ :=
  ((goldbachG11NException A N v).card : ℤ)

theorem goldbachG11_rough_mul_survives {N r q s t m : ℕ}
    (hq : q.Prime) (hs : s.Prime) (ht : t.Prime) (hqs : q ≤ s) (hst : s ≤ t)
    (hm : SurvivesSieve 1 q m) :
    SurvivesSieve (N * r) q (r * q * s * t * m) := by
  intro ell hp hn hNr
  rcases hp.dvd_mul.mp hn with hprod | hdm
  · rcases hp.dvd_mul.mp hprod with hrqs | hdt
    · rcases hp.dvd_mul.mp hrqs with hrq | hds
      · rcases hp.dvd_mul.mp hrq with hdr | hdq
        · exact (hNr (dvd_mul_of_dvd_right hdr N)).elim
        · have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdq
          subst ell
          exact le_rfl
      · have heq := (Nat.prime_dvd_prime_iff_eq hp hs).mp hds
        subst ell
        exact_mod_cast hqs
    · have heq := (Nat.prime_dvd_prime_iff_eq hp ht).mp hdt
      subst ell
      exact_mod_cast hqs.trans hst
  · exact (goldbachG11_survives_one_iff q m).mp hm ell hp hdm

theorem goldbachG11_survives_or_exceptions {N r q s t n : ℕ}
    (hr : r.Prime) (hd : r * q * s * t ∣ n)
    (hH : SurvivesSieve (N * r) q n) :
    SurvivesSieve 1 q (n / (r * q * s * t)) ∨
      (r < q ∧ r ^ 2 ∣ n) ∨ ¬Nat.Coprime n N := by
  classical
  by_cases hrough : SurvivesSieve 1 q (n / (r * q * s * t))
  · exact Or.inl hrough
  rw [goldbachG11_survives_one_iff] at hrough
  push Not at hrough
  obtain ⟨ell, hp, hdm, hlt⟩ := hrough
  have hmul : (r * q * s * t) * (n / (r * q * s * t)) = n :=
    Nat.mul_div_cancel' hd
  have helln : ell ∣ n := by
    rw [← hmul]
    exact dvd_mul_of_dvd_right hdm _
  have hellNr : ell ∣ N * r := by
    by_contra h
    exact (not_le.mpr hlt) (hH ell hp helln h)
  by_cases hellN : ell ∣ N
  · exact Or.inr (Or.inr fun hc =>
      hp.ne_one (Nat.eq_one_of_dvd_coprimes hc helln hellN))
  · have hellr : ell ∣ r := (hp.dvd_mul.mp hellNr).resolve_left hellN
    have heq : ell = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hellr
    subst ell
    refine Or.inr (Or.inl ⟨by exact_mod_cast hlt, ?_⟩)
    have hrprod : r ∣ r * q * s * t :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right r q) s) t
    rw [pow_two, ← hmul]
    exact Nat.mul_dvd_mul hrprod hdm

theorem goldbachG11_cell_sandwich (N : ℕ) (ε : ℝ) (v : GoldbachG11Label)
    {z b : ℝ} (hε : 0 ≤ ε) (hv : v ∈ goldbachG11Labels N z b) :
    goldbachG11RoughCount N ε v ≤
        literalH (goldbachDifferenceCarrier N ε) (N * v.2.2.1)
          (goldbachG11LabelProd v) v.2.2.2 ∧
      literalH (goldbachDifferenceCarrier N ε) (N * v.2.2.1)
          (goldbachG11LabelProd v) v.2.2.2 ≤
        goldbachG11RoughCount N ε v +
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v +
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v := by
  classical
  have hpos := goldbachG11LabelProd_pos hv
  rcases v with ⟨t, s, r, q⟩
  rcases mem_goldbachG11Labels_iff.mp hv with ⟨hr, hq, hs, ht, _, _, _, hqs, hst, _⟩
  let A := goldbachDifferenceCarrier N ε
  let R := A.filter fun n => r * q * s * t ∣ n ∧ SurvivesSieve 1 q (n / (r * q * s * t))
  let H := A.filter (literalHPoint (N * r) (r * q * s * t) q)
  let Er := goldbachG11RSquareException A ⟨t, s, r, q⟩
  let EN := goldbachG11NException A N ⟨t, s, r, q⟩
  have hR : goldbachG11RoughCount N ε ⟨t, s, r, q⟩ = (R.card : ℤ) :=
    goldbachG11RoughCount_eq_filter N ε ⟨t, s, r, q⟩ hε hpos
  have hRH : R ⊆ H := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hd, hm⟩
    refine Finset.mem_filter.mpr ⟨hnA, hd, ?_⟩
    have heq : r * q * s * t * (n / (r * q * s * t)) = n :=
      Nat.mul_div_cancel' hd
    simpa only [heq] using
      goldbachG11_rough_mul_survives (N := N) (r := r) hq hs ht hqs hst hm
  have hcover : H ⊆ (R ∪ Er) ∪ EN := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hd, hH⟩
    rcases goldbachG11_survives_or_exceptions hr hd hH with hm | he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hnA, hd, hm⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hnA, hd, he⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnA, hd, he⟩)
  have hupper : H.card ≤ R.card + Er.card + EN.card := by
    calc
      H.card ≤ ((R ∪ Er) ∪ EN).card := Finset.card_le_card hcover
      _ ≤ (R ∪ Er).card + EN.card := Finset.card_union_le _ _
      _ ≤ R.card + Er.card + EN.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  rw [hR]
  change (R.card : ℤ) ≤ (H.card : ℤ) ∧
    (H.card : ℤ) ≤ (R.card : ℤ) + (Er.card : ℤ) + (EN.card : ℤ)
  constructor
  · exact_mod_cast Finset.card_le_card hRH
  · exact_mod_cast hupper

theorem goldbachWeightG11_roughQuotient_sandwich
    (N : ℕ) (ε z b : ℝ) (hε : 0 ≤ ε) :
    (∑ v ∈ goldbachG11Labels N z b, goldbachG11RoughCount N ε v) ≤
        goldbachWeightG11 (goldbachDifferenceCarrier N ε) N z b ∧
      goldbachWeightG11 (goldbachDifferenceCarrier N ε) N z b ≤
        (∑ v ∈ goldbachG11Labels N z b, goldbachG11RoughCount N ε v) +
          (∑ v ∈ goldbachG11Labels N z b,
            goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
          (∑ v ∈ goldbachG11Labels N z b,
            goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) := by
  rw [goldbachWeightG11_eq_label_sum]
  constructor
  · exact Finset.sum_le_sum fun v hv => (goldbachG11_cell_sandwich N ε v hε hv).1
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v hv => (goldbachG11_cell_sandwich N ε v hε hv).2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig