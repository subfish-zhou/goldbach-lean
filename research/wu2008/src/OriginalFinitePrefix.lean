import OriginalFiniteGeometry

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open LiLiuPrereqBuchstab
namespace OriginalU8

def thirds (N : ℕ) (ρ : ℝ) (n s : ℕ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  (range (N+1)).filter fun t => n ∈ shortLabels N ρ k ∧ (s,t) ∈ labels N ρ k

/-- Actual rectangle mass splits into original relaxed pair fibres, without quotienting labels. -/
theorem original_mass_fibres {N : ℕ} {e ρ : ℝ} (hN : 1 ≤ (N : ℝ))
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ × ℕ}
    (hb : 3 ≤ ρ^k.1) (hk : Occupied N e ρ k) :
    rectangleMass N ρ k = ∑ rs ∈ relaxedPairs N ρ, ((thirds N ρ rs.1 rs.2 k).card : ℝ) := by
  classical
  rw [rectangleMass_card]
  have hc : (shortLabels N ρ k ×ˢ labels N ρ k).card =
      ((relaxedPairs N ρ).sigma fun rs => thirds N ρ rs.1 rs.2 k).card := by
    apply card_bij (fun q _ => ⟨(q.1,q.2.1),q.2.2⟩)
    · intro q hq
      obtain ⟨hn,hz⟩ := mem_product.mp hq
      apply mem_sigma.mpr
      refine ⟨(original_pair_prefix hN hρ hρu hb hk hn hz).1,mem_filter.mpr ⟨?_,hn,hz⟩⟩
      exact mem_range.mpr (Nat.lt_succ_of_le ((labels_mem N ρ k q.2.1 q.2.2).mp hz).2.1)
    · intro q _ r _ he
      have h1 : (q.1,q.2.1) = (r.1,r.2.1) := congrArg Sigma.fst he
      have h2 : q.2.2 = r.2.2 := congrArg (fun x : (rs : ℕ × ℕ) × ℕ => x.2) he
      have hn : q.1 = r.1 := congrArg (fun p : ℕ × ℕ => p.1) h1
      have hs : q.2.1 = r.2.1 := congrArg (fun p : ℕ × ℕ => p.2) h1
      exact Prod.ext hn (Prod.ext hs h2)
    · intro q hq
      obtain ⟨_,ht⟩ := mem_sigma.mp hq
      obtain ⟨_,hn,hz⟩ := mem_filter.mp ht
      exact ⟨(q.1.1,q.1.2,q.2),mem_product.mpr ⟨hn,hz⟩,rfl⟩
  rw [hc,card_sigma,Nat.cast_sum]

/-- One prefix for each pair across ALL original occupied cells; this is a genuine injection. -/
theorem original_thirds_primePi {N : ℕ} {e ρ : ℝ} (hN : 1 ≤ N)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hb : ∀ k ∈ U8Literal.occupied N e ρ, 3 ≤ ρ^k.1) (n s : ℕ) :
    ((∑ k ∈ U8Literal.occupied N e ρ, (thirds N ρ n s k).card : ℕ) : ℝ) ≤
      primePi (ρ^3*(N : ℝ)/((n : ℝ)*s)) := by
  classical
  have h : (∑ k ∈ U8Literal.occupied N e ρ, (thirds N ρ n s k).card) ≤
      ((range (⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊+1)).filter Nat.Prime).card := by
    rw [← card_sigma]
    apply card_le_card_of_injOn (fun q => q.2)
    · intro q hq
      obtain ⟨hk,ht⟩ := mem_sigma.mp hq
      obtain ⟨_,hn,hz⟩ := mem_filter.mp ht
      have hp := original_pair_prefix (by exact_mod_cast hN) hρ hρu (hb q.1 hk)
        (U8Literal.Join.occupied_to_original hN hρ hk) hn hz
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hp.2.2)),hp.2.1⟩
    · intro q hq r hr he
      obtain ⟨hk,hqt⟩ := mem_sigma.mp hq
      obtain ⟨hk',hrt⟩ := mem_sigma.mp hr
      obtain ⟨_,hqn,hqz⟩ := mem_filter.mp hqt
      obtain ⟨_,hrn,hrz⟩ := mem_filter.mp hrt
      have hqz' : (s,r.2) ∈ labels N ρ q.1 := by simpa only [he] using hqz
      have hkey := original_label_unique hρ hρu (hb q.1 hk) (hb r.1 hk')
        (U8Literal.Join.occupied_to_original hN hρ hk)
        (U8Literal.Join.occupied_to_original hN hρ hk') hqn hqz' hrn hrz
      exact Sigma.ext hkey (heq_of_eq he)
  have hc : ((range (⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊+1)).filter Nat.Prime).card =
      Nat.primeCounting ⌊ρ^3*(N : ℝ)/((n : ℝ)*s)⌋₊ := by
    simp [Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  rw [hc] at h
  exact Nat.cast_le.mpr h

/-- Finite transport of cell weights; neither final mass nor asymptotics is a premise. -/
theorem original_weighted_prefix {N : ℕ} {e ρ : ℝ} (hN : 1 ≤ N)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hb : ∀ k ∈ U8Literal.occupied N e ρ, 3 ≤ ρ^k.1)
    (W : (ℕ × ℕ × ℕ) → ℝ) (V : ℕ → ℝ)
    (hV : ∀ rs ∈ relaxedPairs N ρ, 0 ≤ V rs.1)
    (hWV : ∀ k ∈ U8Literal.occupied N e ρ, ∀ n ∈ shortLabels N ρ k, W k ≤ V n) :
    (∑ k ∈ U8Literal.occupied N e ρ, W k * rectangleMass N ρ k) ≤
      ∑ rs ∈ relaxedPairs N ρ, V rs.1 * primePi (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2)) := by
  classical
  calc
    _ = ∑ k ∈ U8Literal.occupied N e ρ, ∑ rs ∈ relaxedPairs N ρ,
        W k * ((thirds N ρ rs.1 rs.2 k).card : ℝ) := by
      apply sum_congr rfl
      intro k hk
      rw [original_mass_fibres (by exact_mod_cast hN) hρ hρu (hb k hk)
        (U8Literal.Join.occupied_to_original hN hρ hk),mul_sum]
    _ ≤ ∑ k ∈ U8Literal.occupied N e ρ, ∑ rs ∈ relaxedPairs N ρ,
        V rs.1 * ((thirds N ρ rs.1 rs.2 k).card : ℝ) := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro rs _
      by_cases ht : (thirds N ρ rs.1 rs.2 k).Nonempty
      · obtain ⟨t,ht⟩ := ht
        exact mul_le_mul_of_nonneg_right (hWV k hk rs.1 (mem_filter.mp ht).2.1) (Nat.cast_nonneg _)
      · rw [not_nonempty_iff_eq_empty.mp ht]
        simp
    _ = ∑ rs ∈ relaxedPairs N ρ,
        V rs.1 * ((∑ k ∈ U8Literal.occupied N e ρ, (thirds N ρ rs.1 rs.2 k).card : ℕ) : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro rs _
      rw [Nat.cast_sum,mul_sum]
    _ ≤ _ := sum_le_sum fun rs hrs =>
      mul_le_mul_of_nonneg_left (original_thirds_primePi hN hρ hρu hb rs.1 rs.2) (hV rs hrs)

end OriginalU8
