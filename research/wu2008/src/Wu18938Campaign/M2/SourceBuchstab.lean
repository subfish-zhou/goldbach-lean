import MathlibNt.Wu2008DoubleSieve.Buchstab
import MathlibNt.Wu2008DoubleSieve.SourceCarriers
import MathlibNt.Wu2008DoubleSieve.S3CarrierMajorant

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

theorem source_first_carrier (N D M : ℕ) {z w : ℝ} {q : ℕ}
    (hq : q ∈ primeWindow M z w) :
    (sourceSieveCarrier N D M z).filter
        (fun ell => FirstDivisor (primeWindow M z w) (N - ell) q) =
      sourceSieveCarrier N (Nat.lcm D q) M q := by
  obtain ⟨_, _, hzq, hqw⟩ := mem_primeWindow.mp hq
  ext ell
  simp only [sourceSieveCarrier, mem_filter, Nat.lcm_dvd_iff]
  constructor
  · rintro ⟨⟨hr, hp, hd, hs⟩, hfirst⟩
    refine ⟨hr, hp, ⟨hd, hfirst.1⟩, ?_⟩
    intro r hr hrM hrq
    by_cases hrz : (r : ℝ) < z
    · exact hs r hr hrM hrz
    · exact hfirst.2 r (mem_primeWindow.mpr
        ⟨hr, hrM, le_of_not_gt hrz, hrq.trans hqw⟩) (by exact_mod_cast hrq)
  · rintro ⟨hr, hp, ⟨hd, hqdiv⟩, hs⟩
    refine ⟨⟨hr, hp, hd, fun r hr hrM hrz => hs r hr hrM (hrz.trans_le hzq)⟩,
      hqdiv, ?_⟩
    intro r hr hrq
    obtain ⟨hrp, hrM, _, _⟩ := mem_primeWindow.mp hr
    exact hs r hrp hrM (by exact_mod_cast hrq)

theorem source_buchstab_lcm (N D M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    sourceSieveCount N D M z - sourceSieveCount N D M w =
      ∑ q ∈ primeWindow M z w, sourceSieveCount N (Nat.lcm D q) M q := by
  have hb := finite_buchstab (sourceSieveCarrier N D M z)
    (fun ell => N - ell) (primeWindow M z w)
  have hc : siftedIndices (sourceSieveCarrier N D M z)
      (fun ell => N - ell) (primeWindow M z w) = sourceSieveCarrier N D M w := by
    ext ell
    simp only [siftedIndices, sourceSieveCarrier, mem_filter, sifted_split hzw]
    tauto
  rw [hc] at hb
  have hm : firstMass (sourceSieveCarrier N D M z) (fun ell => N - ell)
      (primeWindow M z w) =
        ∑ q ∈ primeWindow M z w, sourceSieveCount N (Nat.lcm D q) M q := by
    unfold firstMass sourceSieveCount
    apply sum_congr rfl
    intro q hq
    rw [source_first_carrier N D M hq]
  rw [hm] at hb
  change sourceSieveCount N D M w = sourceSieveCount N D M z - _ at hb
  omega

theorem source_buchstab_product (N D M : ℕ) {z w : ℝ} (hzw : z ≤ w)
    (hcop : ∀ q ∈ primeWindow M z w, D.Coprime q) :
    sourceSieveCount N D M z - sourceSieveCount N D M w =
      ∑ q ∈ primeWindow M z w, sourceSieveCount N (D * q) M q := by
  rw [source_buchstab_lcm N D M hzw]
  apply sum_congr rfl
  intro q hq
  rw [(hcop q hq).lcm_eq_mul]

theorem selected_first_carrier {N D M p : ℕ} {w : ℝ}
    (hp : p.Prime) (hpM : p.Coprime M) (hpD : p ∣ D) (hpw : (p : ℝ) < w) :
    (sourceSieveCarrier N D M p).filter
        (fun ell => FirstDivisor (primeWindow M p w) (N - ell) p) =
      sourceSieveCarrier N D M p := by
  have hlcm : Nat.lcm D p = D := Nat.dvd_antisymm
    (Nat.lcm_dvd_iff.mpr ⟨dvd_rfl, hpD⟩) (Nat.dvd_lcm_left D p)
  rw [source_first_carrier N D M (mem_primeWindow.mpr ⟨hp, hpM, le_rfl, hpw⟩), hlcm]

theorem selected_diagonal_mass {N D M p : ℕ} {w : ℝ}
    (hp : p.Prime) (hpM : p.Coprime M) (hpD : p ∣ D) (hpw : (p : ℝ) < w) :
    (∑ r ∈ primeWindow M p w, sourceSieveCount N (Nat.lcm D r) M r) =
        sourceSieveCount N D M p ∧
      (∑ r ∈ (primeWindow M p w).filter (fun r => p < r),
        sourceSieveCount N (D * r) M r) = 0 := by
  constructor
  · rw [← source_buchstab_lcm N D M hpw.le]
    simp [sourceSieveCount, sourceSieveCarrier_eq_empty_of_selected hp hpM hpD hpw]
  · apply sum_eq_zero
    intro r hr
    have hpr := (mem_filter.mp hr).2
    simp [sourceSieveCount, sourceSieveCarrier_eq_empty_of_selected hp hpM
      (hpD.trans (dvd_mul_right D r)) (by exact_mod_cast hpr : (p : ℝ) < r)]

theorem penultimate_buchstab (N A p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    sourceSieveCount N (A * p * q) (A * N) p -
        sourceSieveCount N (A * p * q) (A * p * N) q =
      ∑ r ∈ primeWindow (A * p * N) p q,
        sourceSieveCount N (A * p * r * q) (A * p * N) r := by
  have he : sourceSieveCount N (A * p * q) (A * N) p =
      sourceSieveCount N (A * p * q) (A * p * N) p := by
    apply congrArg (fun s : Finset ℕ => (s.card : ℤ))
    ext ell
    have hs : Sifted (A * p * N) (N - ell) (p : ℝ) ↔
        Sifted (A * N) (N - ell) (p : ℝ) := by
      rw [show A * p * N = (A * N) * p by ring,
        sifted_mul_modulus_of_le hp le_rfl]
    simp only [sourceSieveCarrier, mem_filter, hs]
  rw [he, source_buchstab_product N (A * p * q) (A * p * N)
    (by exact_mod_cast hpq)]
  · apply sum_congr rfl
    intro r _
    congr 1
    ring
  · intro r hr
    obtain ⟨hrp, hrM, _, hrq⟩ := mem_primeWindow.mp hr
    have hrAp : r.Coprime (A * p) :=
      hrM.of_dvd_right (dvd_mul_right (A * p) N)
    have hrq' : r < q := by exact_mod_cast hrq
    exact (hrAp.mul_right ((Nat.coprime_primes hrp hq).mpr (ne_of_lt hrq'))).symm

theorem penultimate_selected_label_absent {N A p q r : ℕ}
    (hp : p.Prime) (hr : r ∈ primeWindow (A * p * N) p q) : p < r := by
  obtain ⟨hrp, hrM, hpr, _⟩ := mem_primeWindow.mp hr
  have hle : p ≤ r := by exact_mod_cast hpr
  apply lt_of_le_of_ne hle
  intro heq
  subst r
  exact hp.coprime_iff_not_dvd.mp hrM
    ((dvd_mul_left p A).trans (dvd_mul_right (A * p) N))

end Wu18938Campaign.M2
