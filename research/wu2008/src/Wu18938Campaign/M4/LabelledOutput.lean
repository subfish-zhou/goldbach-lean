import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledPhysicalSieve
import MathlibNt.Wu2008DoubleSieve.ConvolutionMultiplicity

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem labelled_output_from_cofactor {α : Type*} {N : ℕ} {η F : ℝ}
    (L : LabelledPhysical.Family α N) (hN : 1 < N) (hη : 0 < η) (hF : 0 ≤ F)
    (hlarge : ∀ c ∈ L.labels, (N : ℝ) ^ η ≤ L.lower c)
    (hfibre : ∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F)
    (ell : ℕ) :
    L.weightAt ell ≤ F * (1 / η) := by
  by_cases hs : ∃ c ∈ L.labels, ∃ q ∈ L.primes c, N - L.cofactor c * q = ell
  · obtain ⟨c0, hc0, q0, hq0, he0⟩ := hs
    have hq0pos := (mem_filter.mp hq0).2.1.pos
    have hprod0 : L.cofactor c0 * q0 = N - ell := by
      have := L.output_le hc0 hq0
      omega
    have hm : 0 < N - ell := hprod0 ▸ Nat.mul_pos (L.geometry c0 hc0).1 hq0pos
    let P := largePrimeDivisors (N - ell) ((N : ℝ) ^ η)
    have hP : (P.card : ℝ) ≤ 1 / η :=
      largePrimeDivisors_card_le_inv hN hm (Nat.sub_le N ell) hη
    have hsub (c : α) (hc : c ∈ L.labels) :
        (L.primes c).filter (fun q => N - L.cofactor c * q = ell) ⊆
          P.filter (fun q => L.cofactor c * q = N - ell) := by
      intro q hq
      obtain ⟨hq, he⟩ := mem_filter.mp hq
      have hprod : L.cofactor c * q = N - ell := by
        have := L.output_le hc hq
        omega
      refine mem_filter.mpr ⟨?_, hprod⟩
      apply mem_largePrimeDivisors.mpr
      refine ⟨(mem_filter.mp hq).2.1, ?_, hm.ne', ?_⟩
      · rw [← hprod]
        exact dvd_mul_left _ _
      · exact (hlarge c hc).trans (mem_filter.mp hq).2.2.1.le
    have hlocal (q : ℕ) (hq : q ∈ P) :
        (∑ c ∈ L.labels.filter (fun c => L.cofactor c * q = N - ell), L.weight c) ≤ F := by
      let S := L.labels.filter (fun c => L.cofactor c * q = N - ell)
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha⟩ := hS
        have hqp := (mem_largePrimeDivisors.mp hq).1.pos
        have hinc : S ⊆ L.labels.filter (fun c => L.cofactor c = L.cofactor a) := by
          intro c hc
          obtain ⟨hc, he⟩ := mem_filter.mp hc
          refine mem_filter.mpr ⟨hc, ?_⟩
          exact Nat.eq_of_mul_eq_mul_right hqp (he.trans (mem_filter.mp ha).2.symm)
        exact (sum_le_sum_of_subset_of_nonneg hinc
          (fun c hc _ => L.weight_nonneg c (mem_filter.mp hc).1)).trans (hfibre _)
      · change (∑ c ∈ S, _) ≤ _
        rw [not_nonempty_iff_eq_empty.mp hS, sum_empty]
        exact hF
    calc
      L.weightAt ell ≤ ∑ c ∈ L.labels, L.weight c *
          ((P.filter (fun q => L.cofactor c * q = N - ell)).card : ℝ) :=
        sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (card_le_card (hsub c hc))) (L.weight_nonneg c hc))
      _ = ∑ q ∈ P, ∑ c ∈ L.labels.filter
          (fun c => L.cofactor c * q = N - ell), L.weight c := by
        simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          mul_sum, mul_ite, mul_one, mul_zero, sum_filter]
        exact sum_comm
      _ ≤ ∑ _q ∈ P, F := sum_le_sum hlocal
      _ = F * (P.card : ℝ) := by simp [mul_comm]
      _ ≤ F * (1 / η) := mul_le_mul_of_nonneg_left hP hF
  · have hz : L.weightAt ell = 0 := by
      apply sum_eq_zero
      intro c hc
      have he : (L.primes c).filter (fun q => N - L.cofactor c * q = ell) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro q hq
        exact hs ⟨c, hc, q, (mem_filter.mp hq).1, (mem_filter.mp hq).2⟩
      rw [he, card_empty, Nat.cast_zero, mul_zero]
    rw [hz]
    positivity

theorem labelled_small_from_output {α : Type*} {N : ℕ} {F Z : ℝ}
    (L : LabelledPhysical.Family α N) (hF : 0 ≤ F) (hZ : 0 ≤ Z)
    (hout : ∀ ell, ell.Prime → L.weightAt ell ≤ F) :
    L.small Z ≤ F * (Z + 1) := by
  let S := (range (N + 1)).filter (fun (ell : ℕ) => ell.Prime ∧ (ell : ℝ) < Z)
  have he : L.small Z = ∑ ell ∈ S, L.weightAt ell := by
    have h := L.output_test (fun ell => if ell.Prime ∧ (ell : ℝ) < Z then 1 else 0)
    simpa only [LabelledPhysical.Family.small, S, sum_filter, card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum,
      mul_ite, mul_one, mul_zero] using h.symm
  have hsub : S ⊆ range (⌊Z⌋₊ + 1) := by
    intro ell hell
    have hlt := (mem_filter.mp hell).2.2
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hZ).mpr hlt.le))
  calc
    L.small Z = ∑ ell ∈ S, L.weightAt ell := he
    _ ≤ ∑ _ell ∈ S, F := sum_le_sum (fun ell hell => hout ell (mem_filter.mp hell).2.1)
    _ = F * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ F * ((⌊Z⌋₊ + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (by exact_mod_cast (show S.card ≤ ⌊Z⌋₊ + 1 by simpa using card_le_card hsub)) hF
    _ ≤ F * (Z + 1) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (add_le_add (Nat.floor_le hZ) le_rfl) hF

end Wu18938Campaign.M4
