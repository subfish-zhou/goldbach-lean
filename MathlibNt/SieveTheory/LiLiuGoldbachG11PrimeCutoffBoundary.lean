import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGrouping
import Mathlib.Data.Nat.Factorization.Basic

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The canonical lower cutoff cannot itself be prime: its fourth-power numerator
is incompatible with the prime valuation of a fifty-third power. -/
theorem goldbachG11_prime_ne_lower_cutoff (N p : ℕ) (hp : p.Prime) :
    (p : ℝ) ≠ (N : ℝ)^(4 / 53 : ℝ) := by
  intro heq
  have hpow : (p : ℝ)^53 = (N : ℝ)^4 := by
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hnat : p^53 = N^4 := by exact_mod_cast hpow
  have hv := congrArg (fun n : ℕ => n.factorization p) hnat
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self] at hv
  omega

/-- Changing the lower prime cutoff from closed to strict costs no boundary prime. -/
theorem goldbachG11_prime_lower_cutoff_iff (N p : ℕ) (hp : p.Prime) :
    (N : ℝ)^(4 / 53 : ℝ) ≤ (p : ℝ) ↔ (N : ℝ)^(4 / 53 : ℝ) < (p : ℝ) := by
  constructor
  · intro h
    exact lt_of_le_of_ne h (goldbachG11_prime_ne_lower_cutoff N p hp).symm
  · exact le_of_lt

theorem goldbachG11ProductSupport_one_lt {N m : ℕ} {z b : ℝ}
    (hm : m ∈ goldbachG11ProductSupport N z b) : 1 < m := by
  have hpos := (goldbachG11ProductSupport_data hm).1
  obtain ⟨⟨t, s, q, k⟩, hu, heq⟩ := mem_goldbachG11ProductSupport_iff.mp hm
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  have hq := (mem_goldbachG11SwitchedBodies_iff.mp huB).1
  have hd : q ∣ m := heq ▸
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right q s) t) k
  have hne : m ≠ 1 := fun he => hq.not_dvd_one (he ▸ hd)
  omega

theorem goldbachG11ProductSupport_not_dvd {N m : ℕ} {z b : ℝ}
    (hm : m ∈ goldbachG11ProductSupport N z b) : ¬m ∣ N := by
  intro hd
  have hc := (goldbachG11ProductSupport_data hm).2.2.1
  have he : m = 1 := (Nat.gcd_eq_left hd).symm.trans hc.gcd_eq_one
  have h := goldbachG11ProductSupport_one_lt hm
  omega

/-- The upper product equality is also absent on the actual coprime mother support. -/
theorem goldbachG11_product_upper_cutoff_iff {N m : ℕ} {z b : ℝ}
    (hm : m ∈ goldbachG11ProductSupport N z b) (r : ℕ) :
    r * m < N ↔ r * m ≤ N := by
  constructor
  · exact le_of_lt
  · intro h
    apply lt_of_le_of_ne h
    intro he
    exact goldbachG11ProductSupport_not_dvd hm ⟨r, by rw [← he, Nat.mul_comm]⟩

theorem goldbachG11ProductFirstPrimeFiber_endpoint_iff {N m r : ℕ} {ε b : ℝ}
    (hm : m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) b) :
    r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m ↔
      r.Prime ∧ ¬r ∣ N ∧ (N : ℝ)^(4 / 53 : ℝ) < (r : ℝ) ∧ r ≤ m.minFac ∧
        ε * N < (r * m : ℕ) ∧ r * m ≤ N ∧ (N - r * m).Prime := by
  rw [mem_goldbachG11ProductFirstPrimeFiber_iff]
  constructor
  · rintro ⟨hp, hNd, hz, hq, he, hn, hout⟩
    exact ⟨hp, hNd, (goldbachG11_prime_lower_cutoff_iff N r hp).mp hz,
      hq, he, hn.le, hout⟩
  · rintro ⟨hp, hNd, hz, hq, he, hn, hout⟩
    exact ⟨hp, hNd, hz.le, hq, he,
      (goldbachG11_product_upper_cutoff_iff hm r).mpr hn, hout⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig