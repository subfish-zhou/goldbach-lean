import MathlibNt.Wu2008DoubleSieve.GoldbachWeights

/-!
# Exact Buchstab expansions for Wu's weighted inequality

Source: Wu (2008), proof of Lemma 2.2, the two displays between (2.3)
and (2.4). All sums here are finite actual prime-complement counts.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def FirstDivisor (P : Finset ℕ) (n q : ℕ) : Prop :=
  q ∣ n ∧ ∀ r ∈ P, r < q → ¬r ∣ n

theorem sum_firstDivisor (P : Finset ℕ) (n : ℕ) :
    (∑ q ∈ P, if FirstDivisor P n q then (1 : ℤ) else 0) =
      if divisorsIn P n = ∅ then 0 else 1 := by
  by_cases he : divisorsIn P n = ∅
  · rw [if_pos he]
    apply sum_eq_zero
    intro q hq
    apply if_neg
    intro hfirst
    have hmem : q ∈ divisorsIn P n := mem_filter.mpr ⟨hq, hfirst.1⟩
    rw [he] at hmem
    exact notMem_empty q hmem
  · rw [if_neg he]
    have hn : (divisorsIn P n).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    let a := (divisorsIn P n).min' hn
    have ha : a ∈ divisorsIn P n := (divisorsIn P n).min'_mem hn
    have hle : ∀ q ∈ divisorsIn P n, a ≤ q :=
      fun q hq => (divisorsIn P n).min'_le q hq
    have hfirst : FirstDivisor P n a := by
      refine ⟨(mem_filter.mp ha).2, ?_⟩
      intro r hr hra hrn
      exact (not_lt_of_ge (hle r (mem_filter.mpr ⟨hr, hrn⟩))) hra
    rw [Finset.sum_eq_single a]
    · exact if_pos hfirst
    · intro q hq hqa
      apply if_neg
      intro hqfirst
      have haq : a < q :=
        lt_of_le_of_ne (hle q (mem_filter.mpr ⟨hq, hqfirst.1⟩)) (Ne.symm hqa)
      exact hqfirst.2 a (mem_filter.mp ha).1 haq hfirst.1
    · intro haP
      exact (haP (mem_filter.mp ha).1).elim

noncomputable def firstMass {ι : Type*} (A : Finset ι) (v : ι → ℕ)
    (P : Finset ℕ) : ℤ :=
  ∑ q ∈ P, ((A.filter (fun i => FirstDivisor P (v i) q)).card : ℤ)

theorem firstMass_eq_sum {ι : Type*} (A : Finset ι) (v : ι → ℕ)
    (P : Finset ℕ) :
    firstMass A v P =
      ∑ i ∈ A, if divisorsIn P (v i) = ∅ then (0 : ℤ) else 1 := by
  unfold firstMass
  simp only [← Finset.sum_boole]
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun i _ => sum_firstDivisor P (v i))

theorem finite_buchstab {ι : Type*} (A : Finset ι) (v : ι → ℕ) (P : Finset ℕ) :
    ((siftedIndices A v P).card : ℤ) = (A.card : ℤ) - firstMass A v P := by
  have hsum :
      (∑ i ∈ A, ((if divisorsIn P (v i) = ∅ then (1 : ℤ) else 0) +
        (if divisorsIn P (v i) = ∅ then (0 : ℤ) else 1))) = (A.card : ℤ) := by
    calc
      _ = ∑ _i ∈ A, (1 : ℤ) := by
        apply sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      _ = _ := by simp
  rw [sum_add_distrib, Finset.sum_boole, ← firstMass_eq_sum] at hsum
  change ((siftedIndices A v P).card : ℤ) + firstMass A v P = (A.card : ℤ) at hsum
  omega

theorem firstCarrier_eq (N d M : ℕ) {z w : ℝ} {q : ℕ}
    (hq : q ∈ primeWindow M z w) :
    (sieveCarrier N d M z).filter
        (fun p => FirstDivisor (primeWindow M z w) ((N - p) / d) q) =
      sieveCarrier N (d * q) M (q : ℝ) := by
  rcases mem_primeWindow.mp hq with ⟨hqprime, _, hzq, hqw⟩
  rw [← singleCarrier_eq N d M hqprime (le_refl (q : ℝ))]
  ext p
  simp only [sieveCarrier, mem_filter]
  constructor
  · rintro ⟨⟨hp, hprime, hd, hs⟩, hfirst⟩
    refine ⟨⟨hp, hprime, hd, ?_⟩, hfirst.1⟩
    intro r hr hrM hrq
    by_cases hrz : (r : ℝ) < z
    · exact hs r hr hrM hrz
    · exact hfirst.2 r (mem_primeWindow.mpr
        ⟨hr, hrM, le_of_not_gt hrz, hrq.trans hqw⟩) (by exact_mod_cast hrq)
  · rintro ⟨⟨hp, hprime, hd, hs⟩, hqn⟩
    refine ⟨⟨hp, hprime, hd, fun r hr hrM hrz =>
      hs r hr hrM (hrz.trans_le hzq)⟩, hqn, ?_⟩
    intro r hr hrq
    rcases mem_primeWindow.mp hr with ⟨hrprime, hrM, _, _⟩
    exact hs r hrprime hrM (by exact_mod_cast hrq)

/-- One-step Buchstab identity with literal quotient sequences and real cutoffs. -/
theorem goldbach_buchstab (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    sieveCount N d M w = sieveCount N d M z -
      ∑ q ∈ primeWindow M z w, sieveCount N (d * q) M (q : ℝ) := by
  have h := finite_buchstab (sieveCarrier N d M z)
    (fun p => (N - p) / d) (primeWindow M z w)
  rw [siftedIndices_sieveCarrier N d M hzw] at h
  have hm : firstMass (sieveCarrier N d M z) (fun p => (N - p) / d)
      (primeWindow M z w) =
        ∑ q ∈ primeWindow M z w, sieveCount N (d * q) M (q : ℝ) := by
    unfold firstMass sieveCount
    apply sum_congr rfl
    intro q hq
    rw [firstCarrier_eq N d M hq]
  rw [hm] at h
  exact h

/-- Two iterations keep the positive pair term sifted at its smaller prime. -/
theorem goldbach_buchstab_twofold (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    sieveCount N d M w =
      sieveCount N d M z -
        (∑ c ∈ primeWindow M z w, sieveCount N (d * c) M z) +
        ∑ c ∈ primeWindow M z w, ∑ b ∈ primeWindow M z (c : ℝ),
          sieveCount N (d * c * b) M (b : ℝ) := by
  rw [goldbach_buchstab N d M hzw]
  have hinner :
      (∑ c ∈ primeWindow M z w, sieveCount N (d * c) M (c : ℝ)) =
        ∑ c ∈ primeWindow M z w,
          (sieveCount N (d * c) M z -
            ∑ b ∈ primeWindow M z (c : ℝ), sieveCount N (d * c * b) M (b : ℝ)) := by
    apply sum_congr rfl
    intro c hc
    exact goldbach_buchstab N (d * c) M (mem_primeWindow.mp hc).2.2.1
  rw [hinner, sum_sub_distrib]
  ring

/-- The positive pair term and the exact triple remainder in Wu Lemma 2.2.
The outer indices are the largest selected primes, so each increasing tuple
occurs exactly once without a factorial normalization. -/
theorem goldbach_buchstab_threefold (N d M : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    sieveCount N d M w =
      sieveCount N d M z -
        (∑ c ∈ primeWindow M z w, sieveCount N (d * c) M z) +
        (∑ c ∈ primeWindow M z w, ∑ b ∈ primeWindow M z (c : ℝ),
          sieveCount N (d * c * b) M z) -
        ∑ c ∈ primeWindow M z w, ∑ b ∈ primeWindow M z (c : ℝ),
          ∑ a ∈ primeWindow M z (b : ℝ),
            sieveCount N (d * c * b * a) M (a : ℝ) := by
  rw [goldbach_buchstab N d M hzw]
  have hexpand : ∀ c ∈ primeWindow M z w,
      sieveCount N (d * c) M (c : ℝ) =
        sieveCount N (d * c) M z -
          (∑ b ∈ primeWindow M z (c : ℝ), sieveCount N (d * c * b) M z) +
          ∑ b ∈ primeWindow M z (c : ℝ), ∑ a ∈ primeWindow M z (b : ℝ),
            sieveCount N (d * c * b * a) M (a : ℝ) := by
    intro c hc
    exact goldbach_buchstab_twofold N (d * c) M (mem_primeWindow.mp hc).2.2.1
  simp_rw [sum_congr rfl hexpand, sum_add_distrib, sum_sub_distrib]
  ring

/-- The second expansion in Wu Lemma 2.2, with the large prime in `[w,u)`.
The last term indexes exactly `z ≤ a < b < w ≤ c < u`. -/
theorem goldbach_buchstab_large_prime_sum (N d M : ℕ) {z w u : ℝ} (hzw : z ≤ w) :
    (∑ c ∈ primeWindow M w u, sieveCount N (d * c) M w) =
      (∑ c ∈ primeWindow M w u, sieveCount N (d * c) M z) -
        (∑ c ∈ primeWindow M w u, ∑ b ∈ primeWindow M z w,
          sieveCount N (d * c * b) M z) +
        ∑ c ∈ primeWindow M w u, ∑ b ∈ primeWindow M z w,
          ∑ a ∈ primeWindow M z (b : ℝ),
            sieveCount N (d * c * b * a) M (a : ℝ) := by
  have hexpand := sum_congr rfl (fun c (_ : c ∈ primeWindow M w u) =>
    goldbach_buchstab_twofold N (d * c) M hzw)
  simpa only [sum_add_distrib, sum_sub_distrib] using hexpand

end Wu2008DoubleSieve
