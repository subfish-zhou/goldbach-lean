import MathlibNt.Wu2008DoubleSieve.FiniteWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wu's weight on actual Goldbach quotient sequences

The convention is strict sifting (`q < z`), with prime windows `[z,w)`.
This is the convention used by the Buchstab expansions in Wu (2008),
Sections 2 and 4. The printed definition of `P(z)` using `q ≤ z` must
not be silently identified with it at prime endpoints.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def Sifted (M n : ℕ) (z : ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → q.Coprime M → (q : ℝ) < z → ¬q ∣ n

noncomputable def primeWindow (M : ℕ) (z w : ℝ) : Finset ℕ :=
  (range ⌈w⌉₊).filter (fun q => q.Prime ∧ q.Coprime M ∧ z ≤ (q : ℝ))

theorem mem_primeWindow {M q : ℕ} {z w : ℝ} :
    q ∈ primeWindow M z w ↔
      q.Prime ∧ q.Coprime M ∧ z ≤ (q : ℝ) ∧ (q : ℝ) < w := by
  simp only [primeWindow, mem_filter, mem_range, Nat.lt_ceil]
  tauto

theorem sifted_split {M n : ℕ} {z w : ℝ} (hzw : z ≤ w) :
    Sifted M n w ↔
      Sifted M n z ∧ divisorsIn (primeWindow M z w) n = ∅ := by
  constructor
  · intro h
    refine ⟨fun q hq hqM hqz => h q hq hqM (hqz.trans_le hzw), ?_⟩
    ext q
    simp only [divisorsIn, mem_filter, notMem_empty, iff_false]
    rintro ⟨hq, hqn⟩
    rcases mem_primeWindow.mp hq with ⟨hp, hM, _, hw⟩
    exact h q hp hM hw hqn
  · rintro ⟨hz, he⟩ q hq hqM hqw hqn
    by_cases hqz : (q : ℝ) < z
    · exact hz q hq hqM hqz hqn
    · have hmem : q ∈ divisorsIn (primeWindow M z w) n :=
        mem_filter.mpr ⟨mem_primeWindow.mpr ⟨hq, hqM, le_of_not_gt hqz, hqw⟩, hqn⟩
      rw [he] at hmem
      exact notMem_empty q hmem

/-- Each prime `p ≤ N` is an index, including the unit and zero endpoints. -/
noncomputable def sieveCarrier (N d M : ℕ) (z : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p =>
    p.Prime ∧ d ∣ N - p ∧ Sifted M ((N - p) / d) z)

noncomputable def sieveCount (N d M : ℕ) (z : ℝ) : ℤ :=
  (sieveCarrier N d M z).card

theorem siftedIndices_sieveCarrier (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    siftedIndices (sieveCarrier N d M z) (fun p => (N - p) / d)
      (primeWindow M z w) = sieveCarrier N d M w := by
  ext p
  simp only [siftedIndices, sieveCarrier, mem_filter, sifted_split hzw]
  tauto

theorem dvd_quotient_iff {q d n : ℕ} (hd : d ∣ n) (hqd : q.Coprime d) :
    q ∣ n / d ↔ q ∣ n := by
  calc
    q ∣ n / d ↔ q ∣ d * (n / d) := hqd.dvd_mul_left.symm
    _ ↔ q ∣ n := by rw [Nat.mul_div_cancel' hd]

theorem sifted_quotient_iff {M n d : ℕ} {z : ℝ} (hd : d ∣ n)
    (hcop : ∀ q : ℕ, q.Prime → q.Coprime M → (q : ℝ) < z → q.Coprime d) :
    Sifted M (n / d) z ↔ Sifted M n z := by
  constructor <;> intro h q hq hqM hqz
  · exact fun hqn => h q hq hqM hqz ((dvd_quotient_iff hd (hcop q hq hqM hqz)).mpr hqn)
  · exact fun hqn => h q hq hqM hqz ((dvd_quotient_iff hd (hcop q hq hqM hqz)).mp hqn)

theorem singleCarrier_eq (N d M : ℕ) {q : ℕ} {z : ℝ}
    (hq : q.Prime) (hzq : z ≤ (q : ℝ)) :
    (sieveCarrier N d M z).filter (fun p => q ∣ (N - p) / d) =
      sieveCarrier N (d * q) M z := by
  have hcop : ∀ r : ℕ, r.Prime → r.Coprime M → (r : ℝ) < z → r.Coprime q := by
    intro r hr _ hrz
    apply (Nat.coprime_primes hr hq).mpr
    intro he
    subst r
    exact (not_lt_of_ge hzq) hrz
  ext p
  simp only [sieveCarrier, mem_filter]
  constructor
  · rintro ⟨⟨hp, hprime, hd, hs⟩, hqd⟩
    refine ⟨hp, hprime, (Nat.dvd_div_iff_mul_dvd hd).mp hqd, ?_⟩
    rw [← Nat.div_div_eq_div_mul]
    exact (sifted_quotient_iff hqd hcop).mpr hs
  · rintro ⟨hp, hprime, hdq, hs⟩
    have hd : d ∣ N - p := dvd_trans (dvd_mul_right d q) hdq
    have hqd := (Nat.dvd_div_iff_mul_dvd hd).mpr hdq
    refine ⟨⟨hp, hprime, hd, ?_⟩, hqd⟩
    rw [← Nat.div_div_eq_div_mul] at hs
    exact (sifted_quotient_iff hqd hcop).mp hs

theorem singleMass_sieveCarrier (N d M : ℕ) (z w : ℝ) :
    singleMass (sieveCarrier N d M z) (fun p => (N - p) / d) (primeWindow M z w) =
      ∑ q ∈ primeWindow M z w, sieveCount N (d * q) M z := by
  unfold singleMass sieveCount
  apply sum_congr rfl
  intro q hq
  rcases mem_primeWindow.mp hq with ⟨hqprime, _, hzq, _⟩
  rw [singleCarrier_eq N d M hqprime hzq]

theorem triple_dvd_iff {a b c n : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (hab : a < b) (hbc : b < c) :
    a * b * c ∣ n ↔ a ∣ n ∧ b ∣ n ∧ c ∣ n := by
  have habcop := (Nat.coprime_primes ha hb).mpr (ne_of_lt hab)
  have haccop := (Nat.coprime_primes ha hc).mpr (ne_of_lt (hab.trans hbc))
  have hbccop := (Nat.coprime_primes hb hc).mpr (ne_of_lt hbc)
  have habccop : (a * b).Coprime c :=
    Nat.coprime_mul_iff_left.mpr ⟨haccop, hbccop⟩
  constructor
  · intro h
    exact ⟨dvd_trans (dvd_mul_of_dvd_left (dvd_mul_right a b) c) h,
      dvd_trans (dvd_mul_of_dvd_left (dvd_mul_left b a) c) h,
      dvd_trans (dvd_mul_left c (a * b)) h⟩
  · rintro ⟨han, hbn, hcn⟩
    exact habccop.mul_dvd_of_dvd_of_dvd
      (habcop.mul_dvd_of_dvd_of_dvd han hbn) hcn

theorem sifted_remove_first_iff {M n a b : ℕ} {z w : ℝ}
    (ha : a.Prime) (hza : z ≤ (a : ℝ)) (hab : a < b) (hbw : (b : ℝ) < w) :
    Sifted (M * a) n (b : ℝ) ↔
      Sifted M n z ∧
        ∀ q ∈ primeWindow M z w, q < b → q ≠ a → ¬q ∣ n := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  constructor
  · intro h
    constructor
    · intro q hq hqM hqz
      have hqa : q ≠ a := by
        intro he
        subst q
        exact (not_lt_of_ge hza) hqz
      exact h q hq (Nat.coprime_mul_iff_right.mpr
        ⟨hqM, (Nat.coprime_primes hq ha).mpr hqa⟩)
        (hqz.trans (hza.trans_lt hab'))
    · intro q hq hqb hqa
      rcases mem_primeWindow.mp hq with ⟨hp, hM, _, _⟩
      exact h q hp (Nat.coprime_mul_iff_right.mpr
        ⟨hM, (Nat.coprime_primes hp ha).mpr hqa⟩) (by exact_mod_cast hqb)
  · rintro ⟨hz, hm⟩ q hq hqMa hqb
    rcases Nat.coprime_mul_iff_right.mp hqMa with ⟨hqM, hqa⟩
    by_cases hqz : (q : ℝ) < z
    · exact hz q hq hqM hqz
    · exact hm q (mem_primeWindow.mpr
        ⟨hq, hqM, le_of_not_gt hqz, hqb.trans hbw⟩)
        (by exact_mod_cast hqb) ((Nat.coprime_primes hq ha).mp hqa)

theorem sifted_triple_quotient_iff {M n a b c : ℕ}
    (hb : b.Prime) (hc : c.Prime) (hbc : b < c)
    (hd : a * b * c ∣ n) :
    Sifted (M * a) (n / (a * b * c)) (b : ℝ) ↔
      Sifted (M * a) n (b : ℝ) := by
  apply sifted_quotient_iff hd
  intro q hq hqMa hqb
  have hqb' : q < b := by exact_mod_cast hqb
  have hqa := (Nat.coprime_mul_iff_right.mp hqMa).2
  have hqbcop := (Nat.coprime_primes hq hb).mpr (ne_of_lt hqb')
  have hqccop := (Nat.coprime_primes hq hc).mpr (ne_of_lt (hqb'.trans hbc))
  exact Nat.coprime_mul_iff_right.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨hqa, hqbcop⟩, hqccop⟩

theorem tripleCarrier_eq (N d M : ℕ) {z w : ℝ} {a b c : ℕ}
    (ht : (a, b, c) ∈ orderedTriples (primeWindow M z w)) :
    (sieveCarrier N d M z).filter
        (fun p => tripleSurvives (primeWindow M z w) ((N - p) / d) (a, b, c)) =
      sieveCarrier N (d * (a * b * c)) (M * a) (b : ℝ) := by
  rcases mem_filter.mp ht with ⟨ht, hab, hbc⟩
  rcases mem_product.mp ht with ⟨ha, hbc'⟩
  rcases mem_product.mp hbc' with ⟨hb, hc⟩
  rcases mem_primeWindow.mp ha with ⟨ha, _, hza, _⟩
  rcases mem_primeWindow.mp hb with ⟨hb, _, _, hbw⟩
  rcases mem_primeWindow.mp hc with ⟨hc, _, _, _⟩
  ext p
  simp only [sieveCarrier, mem_filter]
  constructor
  · rintro ⟨⟨hp, hprime, hd, hz⟩, han, hbn, hcn, hm⟩
    have hprod := (triple_dvd_iff ha hb hc hab hbc).mpr ⟨han, hbn, hcn⟩
    refine ⟨hp, hprime, (Nat.dvd_div_iff_mul_dvd hd).mp hprod, ?_⟩
    rw [← Nat.div_div_eq_div_mul]
    apply (sifted_triple_quotient_iff hb hc hbc hprod).mpr
    exact (sifted_remove_first_iff ha hza hab hbw).mpr ⟨hz, hm⟩
  · rintro ⟨hp, hprime, hdprod, hs⟩
    have hd : d ∣ N - p := dvd_trans (dvd_mul_right d (a * b * c)) hdprod
    have hprod := (Nat.dvd_div_iff_mul_dvd hd).mpr hdprod
    rcases (triple_dvd_iff ha hb hc hab hbc).mp hprod with ⟨han, hbn, hcn⟩
    rw [← Nat.div_div_eq_div_mul] at hs
    have hs' := (sifted_triple_quotient_iff hb hc hbc hprod).mp hs
    rcases (sifted_remove_first_iff ha hza hab hbw).mp hs' with ⟨hz, hm⟩
    exact ⟨⟨hp, hprime, hd, hz⟩, han, hbn, hcn, hm⟩

theorem tripleMass_sieveCarrier (N d M : ℕ) (z w : ℝ) :
    tripleMass (sieveCarrier N d M z) (fun p => (N - p) / d) (primeWindow M z w) =
      ∑ t ∈ orderedTriples (primeWindow M z w),
        sieveCount N (d * (t.1 * t.2.1 * t.2.2)) (M * t.1) (t.2.1 : ℝ) := by
  unfold tripleMass sieveCount
  apply sum_congr rfl
  rintro ⟨a, b, c⟩ ht
  rw [tripleCarrier_eq N d M ht]

/-- The actual quotient-sieve version of the weight in Wu (2008), (4.4).
All cutoffs are real, and the assertion holds for every natural `N,d,M`. -/
theorem goldbach_three_prime_upper_weight (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    2 * sieveCount N d M w ≤
      2 * sieveCount N d M z -
        (∑ q ∈ primeWindow M z w, sieveCount N (d * q) M z) +
        ∑ t ∈ orderedTriples (primeWindow M z w),
          sieveCount N (d * (t.1 * t.2.1 * t.2.2)) (M * t.1) (t.2.1 : ℝ) := by
  have h := finite_three_prime_upper_weight (sieveCarrier N d M z)
    (fun p => (N - p) / d) (primeWindow M z w)
  rw [siftedIndices_sieveCarrier N d M hzw, singleMass_sieveCarrier,
    tripleMass_sieveCarrier] at h
  exact h

theorem sieveCount_le_mul_modulus (N d M e : ℕ) (z : ℝ) :
    sieveCount N d M z ≤ sieveCount N d (e * M) z := by
  apply Int.ofNat_le.mpr
  apply Finset.card_le_card
  intro p hp
  rcases mem_filter.mp hp with ⟨hrange, hprime, hd, hs⟩
  refine mem_filter.mpr ⟨hrange, hprime, hd, ?_⟩
  intro q hq hqM hqz
  exact hs q hq (Nat.coprime_mul_iff_right.mp hqM).2 hqz

/-- The left-hand sieve may retain Wu's original prime set `P(N)`.
No error term is needed for this one-sided comparison. -/
theorem wu_proposition44_finite_weight (N d : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    2 * sieveCount N d N w ≤
      2 * sieveCount N d (d * N) z -
        (∑ q ∈ primeWindow (d * N) z w, sieveCount N (d * q) (d * N) z) +
        ∑ t ∈ orderedTriples (primeWindow (d * N) z w),
          sieveCount N (d * (t.1 * t.2.1 * t.2.2)) (d * N * t.1) (t.2.1 : ℝ) := by
  have hm := sieveCount_le_mul_modulus N d N d w
  have hw := goldbach_three_prime_upper_weight N d (d * N) hzw
  omega

/-- A large prime `d` cannot be a prime in the half-open sifting window. -/
theorem primeWindow_mul_of_prime_above (N : ℕ) {d : ℕ} {z w : ℝ}
    (hd : d.Prime) (hwd : w ≤ (d : ℝ)) :
    primeWindow (d * N) z w = primeWindow N z w := by
  ext q
  simp only [mem_primeWindow, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hq, ⟨_, hqN⟩, hzq, hqw⟩
    exact ⟨hq, hqN, hzq, hqw⟩
  · rintro ⟨hq, hqN, hzq, hqw⟩
    have hqd : q ≠ d := by
      intro he
      subst q
      exact (not_lt_of_ge hwd) hqw
    exact ⟨hq, ⟨(Nat.coprime_primes hq hd).mpr hqd, hqN⟩, hzq, hqw⟩

/-- The finite source weight with the printed `P(N)` prime summation ranges.
The hypothesis `w ≤ d` is retained explicitly instead of silently assuming
the later analytic parameter specialization. -/
theorem wu_proposition44_prime_weight (N : ℕ) {d : ℕ} {z w : ℝ}
    (hd : d.Prime) (hzw : z ≤ w) (hwd : w ≤ (d : ℝ)) :
    2 * sieveCount N d N w ≤
      2 * sieveCount N d (d * N) z -
        (∑ q ∈ primeWindow N z w, sieveCount N (d * q) (d * N) z) +
        ∑ t ∈ orderedTriples (primeWindow N z w),
          sieveCount N (d * (t.1 * t.2.1 * t.2.2)) (d * N * t.1) (t.2.1 : ℝ) := by
  simpa only [primeWindow_mul_of_prime_above N hd hwd] using
    wu_proposition44_finite_weight N d hzw

def SiftedLE (M n : ℕ) (z : ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → q.Coprime M → (q : ℝ) ≤ z → ¬q ∣ n

noncomputable def sieveCarrierLE (N d M : ℕ) (z : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p =>
    p.Prime ∧ d ∣ N - p ∧ SiftedLE M ((N - p) / d) z)

theorem siftedLE_iff_strict_and_endpoint (M n : ℕ) (z : ℝ) :
    SiftedLE M n z ↔ Sifted M n z ∧
      ∀ q : ℕ, q.Prime → q.Coprime M → (q : ℝ) = z → ¬q ∣ n := by
  constructor
  · intro h
    exact ⟨fun q hq hqM hqz => h q hq hqM hqz.le,
      fun q hq hqM hqz => h q hq hqM hqz.le⟩
  · rintro ⟨hs, he⟩ q hq hqM hqz
    rcases lt_or_eq_of_le hqz with hlt | heq
    · exact hs q hq hqM hlt
    · exact he q hq hqM heq

/-- Exact, non-asymptotic conversion of the printed closed sifting convention
at an allowed prime endpoint. The lost term is not assumed negligible. -/
theorem sieveCount_prime_endpoint (N d M : ℕ) {q : ℕ}
    (hq : q.Prime) (hqM : q.Coprime M) :
    sieveCount N d M (q : ℝ) =
      ((sieveCarrierLE N d M (q : ℝ)).card : ℤ) +
        sieveCount N (d * q) M (q : ℝ) := by
  have hle :
      sieveCarrierLE N d M (q : ℝ) =
        (sieveCarrier N d M (q : ℝ)).filter (fun p => ¬q ∣ (N - p) / d) := by
    ext p
    simp only [sieveCarrierLE, sieveCarrier, mem_filter]
    constructor
    · rintro ⟨hp, hprime, hd, hs⟩
      refine ⟨⟨hp, hprime, hd,
        (siftedLE_iff_strict_and_endpoint M ((N - p) / d) (q : ℝ)).mp hs |>.1⟩, ?_⟩
      exact hs q hq hqM le_rfl
    · rintro ⟨⟨hp, hprime, hd, hs⟩, hqn⟩
      refine ⟨hp, hprime, hd,
        (siftedLE_iff_strict_and_endpoint M ((N - p) / d) (q : ℝ)).mpr ⟨hs, ?_⟩⟩
      intro r _ _ hrq
      have he : r = q := by exact_mod_cast hrq
      simpa only [he] using hqn
  have hcard := Finset.card_filter_add_card_filter_not
    (s := sieveCarrier N d M (q : ℝ)) (fun p => q ∣ (N - p) / d)
  rw [singleCarrier_eq N d M hq le_rfl, ← hle] at hcard
  unfold sieveCount
  exact_mod_cast hcard.symm.trans (Nat.add_comm _ _)

end Wu2008DoubleSieve
