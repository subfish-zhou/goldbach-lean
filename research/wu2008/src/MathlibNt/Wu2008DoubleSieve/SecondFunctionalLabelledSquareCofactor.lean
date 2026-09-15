import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledMissingMass

/-! Large square cofactors: finite reciprocal tails, with all original weighted labels.
The existing Family geometry includes lower >= 2 and lower <= upper, even for
empty prime fibres. Thus its proved cofactor_le applies without deleting any label. -/
namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

namespace LabelledPhysical
/-- A large prime square divides the complete cofactor. -/
def Sq (e : ℕ) (Y : ℝ) : Prop := ∃ r : ℕ, r.Prime ∧ Y ≤ (r : ℝ) ∧ r^2 ∣ e

private theorem reciprocal_square_step {x : ℝ} (hx : 2 ≤ x) :
    1 / x^2 ≤ 1 / (x-1) - 1/x := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x-1 := by linarith
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ hm).mpr
  field_simp
  nlinarith

/-- A finite telescoping tail, with no infinite summation or integration. -/
theorem reciprocal_square_tail (N : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    (∑ r ∈ Icc ⌈Y⌉₊ N, 1 / (r : ℝ)^2) ≤ 1 / (Y-1) := by
  have hceil : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hceil2 : (2 : ℝ) ≤ (⌈Y⌉₊ : ℝ) := hY.trans hceil
  by_cases hN : ⌈Y⌉₊ ≤ N
  · have ht := sum_Icc_sub hN (fun r : ℕ => -(1 / ((r : ℝ)-1)))
    have hs : (∑ r ∈ Icc ⌈Y⌉₊ N, 1 / (r : ℝ)^2) ≤
        ∑ r ∈ Icc ⌈Y⌉₊ N, (-(1 / (((r+1 : ℕ) : ℝ)-1)) - -(1 / ((r : ℝ)-1))) := by
      apply sum_le_sum
      intro r hr
      have hr2 : (2 : ℝ) ≤ r := hceil2.trans (by exact_mod_cast (mem_Icc.mp hr).1)
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      linarith [reciprocal_square_step hr2]
    rw [ht] at hs
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hs
    have hn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have hd : 1 / ((⌈Y⌉₊ : ℝ)-1) ≤ 1 / (Y-1) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith
  · rw [Icc_eq_empty_of_lt (Nat.lt_of_not_ge hN), sum_empty]
    exact div_nonneg (by norm_num) (by linarith)

/-- Union over square divisors, after regrouping by the complete cofactor. -/
theorem square_reciprocal_le (N : ℕ) (E : Finset ℕ) {Y : ℝ} (hY : 2 ≤ Y)
    (hE : ∀ e ∈ E, 0 < e ∧ e ≤ N) :
    (∑ e ∈ E.filter (fun e => Sq e Y), 1 / (e : ℝ)) ≤
      (1 + log N) / (Y-1) := by
  let P := Icc ⌈Y⌉₊ N
  have hlog : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
  have hsum : (∑ e ∈ E.filter (fun e => Sq e Y), 1 / (e : ℝ)) ≤
      ∑ r ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => r^2 ∣ e), 1 / (e : ℝ) := by
    calc
      _ ≤ ∑ e ∈ E.filter (fun e => Sq e Y),
          ∑ r ∈ P, if r^2 ∣ e then 1 / (e : ℝ) else 0 := by
        apply sum_le_sum
        intro e he
        obtain ⟨he, r, _hr, hYr, hd⟩ := mem_filter.mp he
        have hrN : r ≤ N := (Nat.le_self_pow (by omega : 2 ≠ 0) r).trans
          ((Nat.le_of_dvd (hE e he).1 hd).trans (hE e he).2)
        have hrP : r ∈ P := mem_Icc.mpr ⟨Nat.ceil_le.mpr hYr, hrN⟩
        simpa only [if_pos hd] using
          (single_le_sum (f := fun r : ℕ => if r^2 ∣ e then 1 / (e : ℝ) else 0)
            (fun r _ => by positivity) hrP :
              (if r^2 ∣ e then 1 / (e : ℝ) else 0) ≤
                ∑ r ∈ P, if r^2 ∣ e then 1 / (e : ℝ) else 0)
      _ = ∑ r ∈ P, ∑ e ∈ E.filter (fun e => Sq e Y),
          if r^2 ∣ e then 1 / (e : ℝ) else 0 := sum_comm
      _ ≤ _ := by
        apply sum_le_sum
        intro r _
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          obtain ⟨he, hd⟩ := mem_filter.mp he
          have heE := (mem_filter.mp he).1
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hE e heE).1, (hE e heE).2⟩, hd⟩
        · intro e _ _
          positivity
  calc
    _ ≤ ∑ r ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => r^2 ∣ e), 1 / (e : ℝ) := hsum
    _ ≤ ∑ r ∈ P, (1+log N) / (r : ℝ)^2 := by
      apply sum_le_sum
      intro r hr
      have hYr : Y ≤ (r : ℝ) := Nat.ceil_le.mp (mem_Icc.mp hr).1
      have hr0 : 0 < r := by exact_mod_cast (show (0 : ℝ) < r by linarith)
      simpa only [Nat.cast_pow] using omega3_reciprocal_multiples_le N (r^2) (pow_pos hr0 _)
    _ = (1+log N) * ∑ r ∈ P, 1 / (r : ℝ)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    _ ≤ (1+log N) * (1/(Y-1)) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_tail N hY) (by positivity)
    _ = _ := by ring

namespace Family
universe u
variable {α : Type u} {N : ℕ} (L : Family α N)

/-- The literal square-exception raw mass; both sigma weights and fibre multiplicity remain. -/
noncomputable def squareRawMass (Y : ℝ) : ℝ :=
  ∑ c ∈ L.labels.filter (fun c => Sq (L.cofactor c) Y),
    L.weight c * ((L.primes c).card : ℝ)

/-- The fixed-E hypothesis bounds the full original weight, not its unweighted image. -/
theorem squareRawMass_le {Y F : ℝ} (hY : 2 ≤ Y) (hF : 0 ≤ F)
    (hfibre : ∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) :
    L.squareRawMass Y ≤ F * N * (1+log N) / (Y-1) := by
  let E := L.labels.image L.cofactor
  have hE : ∀ e ∈ E, 0 < e ∧ e ≤ N := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨(L.geometry c hc).1, L.cofactor_le hc⟩
  have hinner (e : ℕ) :
      (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
        L.weight c * (if Sq (L.cofactor c) Y then ((L.primes c).card : ℝ) else 0)) ≤
        if Sq e Y then F * N * (1 / (e : ℝ)) else 0 := by
    by_cases hb : Sq e Y
    · rw [if_pos hb]
      calc
        _ ≤ ∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
            L.weight c * ((N : ℝ) / e) := by
          apply sum_le_sum
          intro c hc
          obtain ⟨hc, he⟩ := mem_filter.mp hc
          rw [he, if_pos hb]
          apply mul_le_mul_of_nonneg_left _ (L.weight_nonneg c hc)
          simpa only [he] using L.primes_card_le hc
        _ = (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) * ((N : ℝ) / e) :=
          (sum_mul ..).symm
        _ ≤ F * ((N : ℝ) / e) := mul_le_mul_of_nonneg_right (hfibre e) (by positivity)
        _ = _ := by ring
    · rw [if_neg hb]
      apply le_of_eq
      apply sum_eq_zero
      intro c hc
      rw [(mem_filter.mp hc).2, if_neg hb, mul_zero]
  calc
    _ = ∑ c ∈ L.labels, L.weight c *
        (if Sq (L.cofactor c) Y then ((L.primes c).card : ℝ) else 0) := by
      simp only [squareRawMass, sum_filter, mul_ite, mul_zero]
    _ = ∑ e ∈ E, ∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
        L.weight c * (if Sq (L.cofactor c) Y then ((L.primes c).card : ℝ) else 0) :=
      (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) _).symm
    _ ≤ ∑ e ∈ E, if Sq e Y then F * N * (1 / (e : ℝ)) else 0 :=
      sum_le_sum (fun e _ => hinner e)
    _ = F * N * ∑ e ∈ E.filter (fun e => Sq e Y), 1 / (e : ℝ) := by
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ ≤ F * N * ((1+log N)/(Y-1)) :=
      mul_le_mul_of_nonneg_left (square_reciprocal_le N E hY hE) (by positivity)
    _ = _ := by ring

end Family
end LabelledPhysical
end Wu2008DoubleSieve
