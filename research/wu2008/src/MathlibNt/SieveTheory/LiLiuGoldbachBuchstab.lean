import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem survivesSieve_iff_coprime_siftingProduct
    (M n : ℕ) (x : ℝ) :
    SurvivesSieve M x n ↔ Nat.Coprime ((siftingPrimes M x).prod id) n := by
  constructor
  · intro h
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    have hp' := mem_siftingPrimes.mp hp
    exact hp'.1.coprime_iff_not_dvd.mpr (fun hpn => by
      exact not_lt_of_ge (h p hp'.1 hpn hp'.2.2) hp'.2.1)
  · intro h p hpPrime hpn hpM
    refine not_lt.mp ?_
    intro hpx
    have hpMem : p ∈ siftingPrimes M x := mem_siftingPrimes.mpr ⟨hpPrime, hpx, hpM⟩
    have hpCop : Nat.Coprime p n := (Nat.coprime_prod_left_iff.mp h) p hpMem
    exact (hpPrime.coprime_iff_not_dvd.mp hpCop) hpn

theorem literalH_real_eq_siftedCount
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    ((literalH A M d x : ℤ) : ℝ) = siftedCount (A.filter fun n => d ∣ n) M x := by
  rw [literalH, siftedCount]
  congr 1
  congr 1
  apply congrArg Finset.card
  ext n
  simp [literalHPoint, survivesSieve_iff_coprime_siftingProduct, and_left_comm, and_assoc]

theorem literalH_filter_one
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH (A.filter fun n => d ∣ n) M 1 x = literalH A M d x := by
  unfold literalH
  congr 1
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, literalHPoint, one_dvd]
  tauto

theorem literalH_filter_trivialCarrier
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH (A.filter fun n => 1 ∣ n) M d x = literalH A M d x := by
  unfold literalH
  congr 1
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, literalHPoint, one_dvd]
  tauto

theorem literalH_filter_mul_of_coprime
    (A : Finset ℕ) (M d e : ℕ) (x : ℝ)
    (hde : Nat.Coprime d e) :
    literalH (A.filter fun n => d ∣ n) M e x = literalH A M (d * e) x := by
  unfold literalH
  congr 1
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, literalHPoint, and_assoc]
  constructor
  · rintro ⟨hnA, hd, he, hs⟩
    exact ⟨hnA, hde.mul_dvd_of_dvd_of_dvd hd he, hs⟩
  · rintro ⟨hnA, hmul, hs⟩
    exact ⟨hnA, dvd_trans (dvd_mul_of_dvd_left (dvd_refl d) e) hmul,
      dvd_trans (dvd_mul_of_dvd_right (dvd_refl e) d) hmul, hs⟩

theorem literalH_buchstab_interval
    (A : Finset ℕ) (M d : ℕ) {u v : ℝ} (huv : u ≤ v) :
    literalH A M d u - literalH A M d v =
      ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
        literalH (A.filter fun n => d ∣ n) M p p := by
  let B : Finset ℕ := A.filter fun n => d ∣ n
  have hbase := siftedCount_eq_siftedCount_sub_interval B M huv
  have hsum :
      ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
          conditionedSiftedCountOn B (siftingPrimes M v) p =
        ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
          siftedCount (B.filter fun n => p ∣ n) M p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p ∈ siftingPrimes M v := (Finset.mem_filter.mp hp).1
    rw [conditionedSiftedCountOn_siftingPrimes_eq B M hp']
  rw [hsum] at hbase
  rw [← literalH_real_eq_siftedCount A M d u,
    ← literalH_real_eq_siftedCount A M d v] at hbase
  have hsum' :
      ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
          siftedCount (B.filter fun n => p ∣ n) M p =
        ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
          (((literalH B M p p : ℤ)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    symm
    exact literalH_real_eq_siftedCount B M p p
  rw [hsum'] at hbase
  have hreal :
      (((literalH A M d u - literalH A M d v : ℤ)) : ℝ) =
        ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
          (((literalH B M p p : ℤ)) : ℝ) := by
    have htmp :
        ((literalH A M d u : ℤ) : ℝ) - ((literalH A M d v : ℤ) : ℝ) =
          ∑ p ∈ (siftingPrimes M v).filter (fun p : ℕ => u ≤ (p : ℝ)),
            (((literalH B M p p : ℤ)) : ℝ) := by
      linarith
    simpa using htmp
  exact_mod_cast hreal

/-- The half-open prime interval `z ≤ p < y`, with `p` prime and `p ∤ N`. -/
noncomputable def goldbachHalfOpenPrimes (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (siftingPrimes N y).filter (fun p : ℕ => z ≤ (p : ℝ))

/-- The literal half-open sum `S3h = Σ_{z≤s<y, s∈P(N)} H(A,N,s;z)`. -/
noncomputable def goldbachS3HalfOpen (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ s ∈ goldbachHalfOpenPrimes N z y, literalH A N s z

/-- The literal strict double sum `U = Σ_{z≤r<s<y, r,s∈P(N)} H(A,N,rs;r)`. -/
noncomputable def goldbachUStrict (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ s ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
      literalH A N (r * s) r

theorem goldbachS1_two_buchstab_exact
    (A : Finset ℕ) (N : ℕ) {z y : ℝ} (hzy : z ≤ y) :
    goldbachS1 A N y =
      goldbachS1 A N z - goldbachS3HalfOpen A N z y + goldbachUStrict A N z y := by
  have houter := literalH_buchstab_interval A N 1 hzy
  have hinner :
      ∀ s ∈ goldbachHalfOpenPrimes N z y,
        literalH A N s s =
          literalH A N s z -
            ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
              literalH A N (r * s) r := by
    intro s hs
    have hs' : s ∈ siftingPrimes N y := (Finset.mem_filter.mp hs).1
    have hzs : z ≤ (s : ℝ) := (Finset.mem_filter.mp hs).2
    have hsPrime : s.Prime := (mem_siftingPrimes.mp hs').1
    have hBs := literalH_buchstab_interval (A.filter fun n => s ∣ n) N 1 hzs
    have hsum0 :
        ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH ((A.filter fun n => s ∣ n).filter fun n => 1 ∣ n) N r r =
          ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH (A.filter fun n => s ∣ n) N r r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact literalH_filter_trivialCarrier (A.filter fun n => s ∣ n) N r r
    rw [literalH_filter_one, literalH_filter_one, hsum0] at hBs
    have hsum1 :
        ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH (A.filter fun n => s ∣ n) N r r =
          ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
            literalH A N (r * s) r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r ∈ siftingPrimes N s := (Finset.mem_filter.mp hr).1
      have hrPrime : r.Prime := (mem_siftingPrimes.mp hr').1
      have hrs : (r : ℝ) < s := (mem_siftingPrimes.mp hr').2.1
      have hne : r ≠ s := by
        exact ne_of_lt (by exact_mod_cast hrs)
      have hcop : Nat.Coprime s r := (Nat.coprime_primes hsPrime hrPrime).mpr hne.symm
      simpa [Nat.mul_comm] using literalH_filter_mul_of_coprime A N s r r hcop
    rw [hsum1] at hBs
    omega
  have hsum :
      ∑ s ∈ goldbachHalfOpenPrimes N z y, literalH A N s s =
        goldbachS3HalfOpen A N z y - goldbachUStrict A N z y := by
    calc
      ∑ s ∈ goldbachHalfOpenPrimes N z y, literalH A N s s =
          ∑ s ∈ goldbachHalfOpenPrimes N z y,
            (literalH A N s z -
              ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
                literalH A N (r * s) r) := by
              apply Finset.sum_congr rfl
              intro s hs
              exact hinner s hs
      _ = (∑ s ∈ goldbachHalfOpenPrimes N z y, literalH A N s z) -
            ∑ s ∈ goldbachHalfOpenPrimes N z y,
              ∑ r ∈ (siftingPrimes N s).filter (fun r : ℕ => z ≤ (r : ℝ)),
                literalH A N (r * s) r := by
                  rw [Finset.sum_sub_distrib]
      _ = goldbachS3HalfOpen A N z y - goldbachUStrict A N z y := by
            simp [goldbachS3HalfOpen, goldbachUStrict]
  have hsum0 :
      ∑ p ∈ (siftingPrimes N y).filter (fun p : ℕ => z ≤ (p : ℝ)),
        literalH ({n ∈ A | 1 ∣ n}) N p p =
      ∑ p ∈ (siftingPrimes N y).filter (fun p : ℕ => z ≤ (p : ℝ)),
        literalH A N p p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact literalH_filter_trivialCarrier A N p p
  rw [hsum0] at houter
  have houter' :
      goldbachS1 A N z - goldbachS1 A N y =
        goldbachS3HalfOpen A N z y - goldbachUStrict A N z y := by
    simpa [goldbachS1, goldbachHalfOpenPrimes] using houter.trans hsum
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig