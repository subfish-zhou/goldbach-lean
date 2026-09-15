import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Finite repeated-divisibility and exceptional-output errors

These are bounds on filtered labelled carriers, not bounds on their images.
The bad-d condition is the actual complement of coprimality: a prime divides
both d and the positive complementary quotient. In particular it includes
selected primes sharing d as well as quotient primes sharing d.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- Positive complements admitting a repeated prime across d and m/d. -/
noncomputable def omega3BadComplements (N d : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun m => m ≠ 0 ∧ ∃ q ∈ d.primeFactors, d * q ∣ m

theorem omega3_bad_complements_card_le (N d : ℕ) :
    (omega3BadComplements N d).card ≤ ∑ q ∈ d.primeFactors, N / (d * q) := by
  have heq : omega3BadComplements N d =
      d.primeFactors.biUnion (fun q => (range (N + 1)).filter
        (fun m => m ≠ 0 ∧ d * q ∣ m)) := by
    ext m
    simp only [omega3BadComplements, mem_filter, mem_biUnion]
    aesop
  rw [heq]
  exact card_biUnion_le.trans (sum_le_sum fun q _ => (Nat.card_multiples' N (d * q)).le)

/-- Every allowed output is counted with all of its ordered selected labels.
The map to the complement loses no output because all outputs are below N. -/
theorem omega3_labels_card_le_allowed_outputs
    {L : Type*} {r N : ℕ} {η : ℝ}
    (S : Finset L) (out : L → ℕ) (t : L → Fin r → ℕ) (E : Finset ℕ)
    (hinj : Set.InjOn (fun a => (out a, t a)) S)
    (hN : 1 < N) (hη : 0 < η)
    (hout : ∀ a ∈ S, out a < N)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ N - out a ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    ((S.filter (fun a => out a ∈ E)).card : ℝ) ≤
      (1 / η) ^ r * (E.card : ℝ) := by
  let T := S.filter (fun a => out a ∈ E)
  have h :
      (T.card : ℝ) ≤ (1 / η) ^ r * ((E.image (fun b => N - b)).card : ℝ) := by
    refine omega3_labels_card_le_outputs T (fun a => N - out a) t
      (E.image (fun b => N - b)) ?_ ?_ hN hη ?_ ?_
    · intro a ha b hb heq
      obtain ⟨haS, _⟩ := mem_filter.mp ha
      obtain ⟨hbS, _⟩ := mem_filter.mp hb
      apply hinj haS hbS
      refine Prod.ext ?_ (show t a = t b from congr_arg Prod.snd heq)
      have := congr_arg Prod.fst heq
      have := hout a haS
      have := hout b hbS
      dsimp at *
      omega
    · intro a ha
      exact mem_image.mpr ⟨out a, (mem_filter.mp ha).2, rfl⟩
    · intro a ha
      exact ⟨Nat.sub_pos_of_lt (hout a (mem_filter.mp ha).1), Nat.sub_le _ _⟩
    · intro a ha
      exact ht a (mem_filter.mp ha).1
  exact h.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_image_le) (by positivity))

/-- Exact finite floor-sum bound for the true bad-d filtered label family. -/
theorem omega3_bad_labels_card_le
    {L : Type*} {r N d : ℕ} {η : ℝ}
    (S : Finset L) (out : L → ℕ) (t : L → Fin r → ℕ)
    (hinj : Set.InjOn (fun a => (out a, t a)) S)
    (hN : 1 < N) (hd : 0 < d) (hη : 0 < η)
    (hout : ∀ a ∈ S, out a < N)
    (hdvd : ∀ a ∈ S, d ∣ N - out a)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ N - out a ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    ((S.filter (fun a => ¬d.Coprime ((N - out a) / d))).card : ℝ) ≤
      (1 / η) ^ r * ∑ q ∈ d.primeFactors, ((N / (d * q) : ℕ) : ℝ) := by
  let T := S.filter (fun a => ¬d.Coprime ((N - out a) / d))
  have h : (T.card : ℝ) ≤ (1 / η) ^ r * ((omega3BadComplements N d).card : ℝ) := by
    refine omega3_labels_card_le_outputs T (fun a => N - out a) t
      (omega3BadComplements N d) ?_ ?_ hN hη ?_ ?_
    · intro a ha b hb heq
      obtain ⟨haS, _⟩ := mem_filter.mp ha
      obtain ⟨hbS, _⟩ := mem_filter.mp hb
      apply hinj haS hbS
      refine Prod.ext ?_ (show t a = t b from congr_arg Prod.snd heq)
      have := congr_arg Prod.fst heq
      have := hout a haS
      have := hout b hbS
      dsimp at *
      omega
    · intro a ha
      obtain ⟨haS, hbad⟩ := mem_filter.mp ha
      obtain ⟨q, hq, hqd, hqm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
      refine mem_filter.mpr ⟨mem_range.mpr (by omega),
        Nat.ne_of_gt (Nat.sub_pos_of_lt (hout a haS)), q,
        Nat.mem_primeFactors.mpr ⟨hq, hqd, Nat.ne_of_gt hd⟩, ?_⟩
      exact (Nat.dvd_div_iff_mul_dvd (hdvd a haS)).mp hqm
    · intro a ha
      exact ⟨Nat.sub_pos_of_lt (hout a (mem_filter.mp ha).1), Nat.sub_le _ _⟩
    · intro a ha
      exact ht a (mem_filter.mp ha).1
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast omega3_bad_complements_card_le N d

/-- The repeated-divisibility floor sum is genuinely small when every
prime factor of d lies above the source lower cutoff. -/
theorem omega3_bad_floor_sum_le {N d : ℕ} {η : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hdN : d ≤ N) (hη : 0 < η)
    (hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ)) :
    (∑ q ∈ d.primeFactors, ((N / (d * q) : ℕ) : ℝ)) ≤
      (1 / η) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
  have hpow : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) _
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcard : (d.primeFactors.card : ℝ) ≤ 1 / η := by
    have heq : largePrimeDivisors d ((N : ℝ) ^ η) = d.primeFactors :=
      filter_eq_self.mpr hlarge
    rw [← heq]
    exact largePrimeDivisors_card_le_inv hN hd hdN hη
  calc
    _ ≤ ∑ _q ∈ d.primeFactors, (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
      apply sum_le_sum
      intro q hq
      calc
        _ ≤ (N : ℝ) / ((d : ℝ) * (q : ℝ)) := by
          simpa only [Nat.cast_mul] using (Nat.cast_div_le (m := N) (n := d * q) (α := ℝ))
        _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hd' hpow)
          (mul_le_mul_of_nonneg_left (hlarge q hq) hd'.le)
    _ = (d.primeFactors.card : ℝ) * ((N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) := by simp
    _ ≤ (1 / η) * ((N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem omega3_bad_labels_card_le_power
    {L : Type*} {r N d : ℕ} {η : ℝ}
    (S : Finset L) (out : L → ℕ) (t : L → Fin r → ℕ)
    (hinj : Set.InjOn (fun a => (out a, t a)) S)
    (hN : 1 < N) (hd : 0 < d) (hdN : d ≤ N) (hη : 0 < η)
    (hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ))
    (hout : ∀ a ∈ S, out a < N)
    (hdvd : ∀ a ∈ S, d ∣ N - out a)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ N - out a ∧
      (N : ℝ) ^ η ≤ (t a j : ℝ)) :
    ((S.filter (fun a => ¬d.Coprime ((N - out a) / d))).card : ℝ) ≤
      (1 / η) ^ (r + 1) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
  calc
    _ ≤ (1 / η) ^ r * ∑ q ∈ d.primeFactors, ((N / (d * q) : ℕ) : ℝ) :=
      omega3_bad_labels_card_le S out t hinj hN hd hη hout hdvd ht
    _ ≤ (1 / η) ^ r * ((1 / η) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) :=
      mul_le_mul_of_nonneg_left (omega3_bad_floor_sum_le hN hd hdN hη hlarge) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end Wu2008DoubleSieve
