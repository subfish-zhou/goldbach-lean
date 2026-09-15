import MathlibNt.Wu2008DoubleSieve.Omega3CofactorSource
import MathlibNt.Wu2008DoubleSieve.Omega3ClosedEnlargement
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Reciprocal payment for non-coprime switched cofactors

Wu04 (5.6) is estimated with the proved bounded weighted cofactor fibre,
not the source's unsupported uniqueness assertion. A shared prime divisor
forces one reciprocal large-prime saving before the outer Euler mass.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_reciprocal_multiples_le (N p : ℕ) (hp : 0 < p) :
    (∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ)) ≤
      (1 + log N) / p := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hsum :
      (∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ)) ≤
        ∑ a ∈ Icc 1 N, 1 / ((p : ℝ) * a) := by
    let S := (Icc 1 N).filter (fun e => p ∣ e)
    have hinj : Set.InjOn (fun e => e / p) S := by
      intro e he f hf h
      have he' := (mem_filter.mp he).2
      have hf' := (mem_filter.mp hf).2
      have := congrArg (fun a => a * p) h
      simpa only [Nat.div_mul_cancel he', Nat.div_mul_cancel hf'] using this
    have hsub : S.image (fun e => e / p) ⊆ Icc 1 N := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := mem_image.mp ha
      obtain ⟨he, hd⟩ := mem_filter.mp he
      have he0 : 0 < e := (mem_Icc.mp he).1
      have hpE : p ≤ e := Nat.le_of_dvd he0 hd
      exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hp).mpr (by simpa using hpE),
        (Nat.div_le_self _ _).trans (mem_Icc.mp he).2⟩
    calc
      _ = ∑ a ∈ S.image (fun e => e / p), 1 / ((p : ℝ) * a) := by
        rw [sum_image hinj]
        apply sum_congr rfl
        intro e he
        have hd := (mem_filter.mp he).2
        have hmul : (p : ℝ) * (e / p : ℕ) = e := by
          exact_mod_cast Nat.mul_div_cancel' hd
        rw [hmul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
  calc
    _ ≤ ∑ a ∈ Icc 1 N, 1 / ((p : ℝ) * a) := hsum
    _ = (∑ a ∈ Icc 1 N, (a : ℝ)⁻¹) / p := by
      rw [sum_div]
      apply sum_congr rfl
      intro a _
      ring
    _ = (harmonic N : ℝ) / p := by
      rw [harmonic_eq_sum_Icc]
      simp
    _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log N) hpr.le

theorem omega3_rough_non_coprime_reciprocal_le (N q : ℕ) (E : Finset ℕ)
    {Y : ℝ} (hY : 0 < Y) (hq : 0 < q) (hqN : q ≤ N)
    (hE : ∀ e ∈ E, 0 < e ∧ e ≤ N)
    (hrough : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → Y ≤ p) :
    (∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ)) ≤
      (1 + log N) * log N / (Y * log 2) := by
  let P := q.primeFactors.filter (fun p : ℕ => Y ≤ (p : ℝ))
  have hlog : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
  have hsum :
      (∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ)) ≤
        ∑ p ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ) := by
    calc
      _ ≤ ∑ e ∈ E.filter (fun e => ¬ e.Coprime q),
          ∑ p ∈ P, if p ∣ e then 1 / (e : ℝ) else 0 := by
        apply sum_le_sum
        intro e he
        obtain ⟨he, hbad⟩ := mem_filter.mp he
        obtain ⟨p, hp, hpe, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
        have hpP : p ∈ P := mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, Nat.ne_of_gt hq⟩, hrough e he p hp hpe⟩
        simpa only [if_pos hpe] using
          (single_le_sum (f := fun r : ℕ => if r ∣ e then 1 / (e : ℝ) else 0)
            (fun r _ => by positivity) hpP :
            (if p ∣ e then 1 / (e : ℝ) else 0) ≤
              ∑ r ∈ P, if r ∣ e then 1 / (e : ℝ) else 0)
      _ = ∑ p ∈ P, ∑ e ∈ E.filter (fun e => ¬ e.Coprime q),
          if p ∣ e then 1 / (e : ℝ) else 0 := sum_comm
      _ ≤ _ := by
        apply sum_le_sum
        intro p _
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          obtain ⟨he, hp⟩ := mem_filter.mp he
          have heE := (mem_filter.mp he).1
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hE e heE).1, (hE e heE).2⟩, hp⟩
        · intro e _ _
          positivity
  have hcard : (P.card : ℝ) ≤ log N / log 2 := by
    have hω := primeFactors_card_mul_log_two_le q hq
    have hl : log (q : ℝ) ≤ log N :=
      log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqN)
    apply (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hc : (P.card : ℝ) ≤ q.primeFactors.card := by
      exact_mod_cast card_le_card (filter_subset _ _)
    nlinarith [log_pos (by norm_num : (1 : ℝ) < 2)]
  calc
    _ ≤ ∑ p ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ) := hsum
    _ ≤ ∑ _p ∈ P, (1 + log N) / Y := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hp, hYp⟩ := mem_filter.mp hp
      exact (omega3_reciprocal_multiples_le N p
        (Nat.prime_of_mem_primeFactors hp).pos).trans
          (div_le_div_of_nonneg_left (by positivity) hY hYp)
    _ = (P.card : ℝ) * ((1 + log N) / Y) := by simp
    _ ≤ (log N / log 2) * ((1 + log N) / Y) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end Wu2008DoubleSieve
