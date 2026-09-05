import MathlibNt.AnalyticNumberTheory.LargeSieve.PrefixMaximal

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

lemma sum_Ioc_nat_eq_sum_Icc_int (M : ℤ) (a b : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ioc a b, f (M + n)) = ∑ n ∈ Finset.Icc (M + a + 1) (M + b), f n := by
  refine Finset.sum_bij (fun (n : ℕ) _ => M + (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    have hn1 : a < n := Finset.mem_Ioc.mp hn |>.1
    have hn2 : n ≤ b := Finset.mem_Ioc.mp hn |>.2
    rw [Finset.mem_Icc]
    omega
  · intro n1 _ n2 _ h
    omega
  · intro n hn
    have hn1 : M + a + 1 ≤ n := Finset.mem_Icc.mp hn |>.1
    have hn2 : n ≤ M + b := Finset.mem_Icc.mp hn |>.2
    use (n - M).toNat
    have H : (n - M).toNat ∈ Finset.Ioc a b := by
      rw [Finset.mem_Ioc]
      omega
    use H
    omega
  · intro n hn
    rfl

lemma sum_Ioc_telescope_eq (y L : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range L,
        ∑ n ∈ Finset.Ioc ((y / 2^(k+1)) * 2^(k+1)) ((y / 2^k) * 2^k), f n) =
      ∑ n ∈ Finset.Ioc ((y / 2^L) * 2^L) y, f n := by
  induction' L with L ih
  · simp
  · rw [Finset.sum_range_succ, ih, add_comm]
    have h1 : (y / 2^(L+1)) * 2^(L+1) ≤ (y / 2^L) * 2^L := by
      calc
        (y / 2^(L+1)) * 2^(L+1) = (y / (2^L * 2)) * (2^L * 2) := by rw [pow_succ]
        _ = (y / 2^L / 2) * (2 * 2^L) := by rw [Nat.div_div_eq_div_mul, mul_comm (2^L) 2]
        _ = ((y / 2^L / 2) * 2) * 2^L := by rw [mul_assoc]
        _ ≤ (y / 2^L) * 2^L := Nat.mul_le_mul_right (2^L) (Nat.div_mul_le_self (y / 2^L) 2)
    have h2 : (y / 2^L) * 2^L ≤ y := Nat.div_mul_le_self y (2^L)
    rw [← Finset.sum_Ioc_consecutive f h1 h2]

lemma div_mod_two_eq (y k : ℕ) :
    (y / 2^k) = 2 * (y / 2^(k+1)) + (y / 2^k) % 2 := by
  have H1 : y / 2^(k+1) = (y / 2^k) / 2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rw [H1]
  exact (Nat.div_add_mod (y / 2^k) 2).symm

lemma decomp_eq (y N : ℕ) (hy : y ≤ N) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 y, f n) =
      ∑ k ∈ (Finset.range (Nat.log2 N + 1)).filter (fun k => (y / 2^k) % 2 = 1),
        ∑ n ∈ Finset.Ioc ((2 * (y / 2^(k+1))) * 2^k) ((2 * (y / 2^(k+1))) * 2^k + 2^k), f n := by
  have hL : y < 2^(Nat.log2 N + 1) := by
    calc
      y ≤ N := hy
      _ < 2^(Nat.log2 N + 1) := Nat.lt_log2_self
  have h_div_L : y / 2^(Nat.log2 N + 1) = 0 := Nat.div_eq_of_lt hL
  have h_eq1 := sum_Ioc_telescope_eq y (Nat.log2 N + 1) f
  rw [h_div_L] at h_eq1
  simp only [zero_mul] at h_eq1
  rw [← h_eq1]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Nat.log2 N + 1)) (fun k => (y / 2^k) % 2 = 1)]
  have h_zero : ∑ k ∈ (Finset.range (Nat.log2 N + 1)).filter (fun k => ¬((y / 2^k) % 2 = 1)),
      ∑ n ∈ Finset.Ioc ((y / 2^(k+1)) * 2^(k+1)) ((y / 2^k) * 2^k), f n = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : (y / 2^k) % 2 = 0 := by
      have h_mod := Nat.mod_lt (y / 2^k) (by decide : 0 < 2)
      have h_not := Finset.mem_filter.mp hk |>.2
      omega
    have hk2 : (y / 2^k) * 2^k = (y / 2^(k+1)) * 2^(k+1) := by
      calc
        (y / 2^k) * 2^k = (2 * (y / 2^(k+1)) + 0) * 2^k := by rw [div_mod_two_eq y k, hk1]
        _ = 2 * (y / 2^(k+1)) * 2^k := by rw [add_zero]
        _ = (y / 2^(k+1)) * (2 * 2^k) := by ring
        _ = (y / 2^(k+1)) * 2^(k+1) := by rw [pow_succ, mul_comm 2 (2^k)]
    rw [hk2, Finset.Ioc_eq_empty_of_le (le_refl _)]
    simp
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : (y / 2^k) % 2 = 1 := Finset.mem_filter.mp hk |>.2
  have hk2 : (y / 2^k) * 2^k = (2 * (y / 2^(k+1))) * 2^k + 2^k := by
    calc
      (y / 2^k) * 2^k = (2 * (y / 2^(k+1)) + 1) * 2^k := by rw [div_mod_two_eq y k, hk1]
      _ = (2 * (y / 2^(k+1))) * 2^k + 2^k := by ring
  have hk3 : (y / 2^(k+1)) * 2^(k+1) = (2 * (y / 2^(k+1))) * 2^k := by
    calc
      (y / 2^(k+1)) * 2^(k+1) = (y / 2^(k+1)) * (2 * 2^k) := by rw [pow_succ, mul_comm (2^k) 2]
      _ = 2 * (y / 2^(k+1)) * 2^k := by ring
  rw [hk2, hk3]

lemma decomp_j_lt (y N k : ℕ) (hy : y ≤ N) : 2 * (y / 2^(k+1)) < N + 1 := by
  have H1 : y / 2^(k+1) ≤ N / 2 := by
    have : y / 2^(k+1) ≤ N / 2^(k+1) := Nat.div_le_div_right hy
    have H2 : N / 2^(k+1) = (N / 2^k) / 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
    rw [H2] at this
    have H3 : N / 2^k ≤ N := Nat.div_le_self N (2^k)
    have H4 : (N / 2^k) / 2 ≤ N / 2 := Nat.div_le_div_right H3
    exact le_trans this H4
  have H5 : (N / 2) * 2 ≤ N := Nat.div_mul_le_self N 2
  omega

lemma Ioc_disjoint (a b c d : ℤ) (h : b ≤ c) : Disjoint (Finset.Ioc a b) (Finset.Ioc c d) := by
  rw [Finset.disjoint_left]
  intro x hx
  have h1 : x ≤ b := Finset.mem_Ioc.mp hx |>.2
  intro hx2
  have h2 : c < x := Finset.mem_Ioc.mp hx2 |>.1
  omega

lemma sum_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Finset ℤ) (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (T : Finset ℤ) (h_sub : ∀ i ∈ s, S i ⊆ T) (c : ℤ → ℝ) (hc : ∀ n ∈ T, 0 ≤ c n) :
    (∑ i ∈ s, ∑ n ∈ S i, c n) ≤ ∑ n ∈ T, c n := by
  have H : ∑ i ∈ s, ∑ n ∈ S i, c n = ∑ n ∈ s.biUnion S, c n := (Finset.sum_biUnion h_disj).symm
  rw [H]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    have ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact h_sub i hi hxi
  · intro x hx hnx
    exact hc x hx

theorem weighted_primitive_prefix_maximal
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  let ι := Fin (Nat.log2 N + 1) × Fin (N + 1)
  let blockStart : ι → ℤ := fun i => M + (i.2.val * 2^i.1.val : ℕ)
  let blockLength : ι → ℕ := fun i => if (i.2.val * 2^i.1.val + 2^i.1.val : ℕ) ≤ N then 2^i.1.val else 0
  let prefixBlocks : ℕ → Finset ι := fun y =>
    if hy : y ≤ N then
      ((Finset.range (Nat.log2 N + 1)).filter (fun k => (y / 2^k) % 2 = 1)).attach
        |>.image fun ⟨k, hk⟩ =>
          have hk_lt : k < Nat.log2 N + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk |>.1)
          ⟨⟨k, hk_lt⟩, ⟨2 * (y / 2^(k+1)), decomp_j_lt y N k hy⟩⟩
    else ∅

  have hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
    (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
      ∑ i ∈ prefixBlocks y,
        ∑ n ∈ Finset.Icc (blockStart i + 1) (blockStart i + blockLength i), f n := by
    intro y hy f
    have hy2 : y ≤ N := by rw [Finset.mem_range] at hy; omega
    have H1 : (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) = ∑ n ∈ Finset.Ioc 0 y, f (M + n) := by
      have := sum_Ioc_nat_eq_sum_Icc_int M 0 y f
      simp only [Nat.cast_zero, add_zero] at this
      exact this.symm
    rw [H1]
    have H2 := decomp_eq y N hy2 (fun n => f (M + n))
    rw [H2]
    dsimp [prefixBlocks]
    rw [dif_pos hy2]
    rw [Finset.sum_image]
    · rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro ⟨k, hk⟩ _
      have hk1 : (y / 2^k) % 2 = 1 := Finset.mem_filter.mp hk |>.2
      have hk2 : 2 * (y / 2^(k+1)) * 2^k + 2^k ≤ N := by
        have H : y / 2^k = 2 * (y / 2^(k+1)) + 1 := by
          calc
            y / 2^k = 2 * (y / 2^(k+1)) + (y / 2^k) % 2 := div_mod_two_eq y k
            _ = 2 * (y / 2^(k+1)) + 1 := by rw [hk1]
        have H2_eq : 2 * (y / 2^(k+1)) * 2^k + 2^k = (y / 2^k) * 2^k := by
          calc
            2 * (y / 2^(k+1)) * 2^k + 2^k = (2 * (y / 2^(k+1)) + 1) * 2^k := by ring
            _ = (y / 2^k) * 2^k := by rw [← H]
        rw [H2_eq]
        have H3 : (y / 2^k) * 2^k ≤ y := Nat.div_mul_le_self y (2^k)
        omega
      dsimp [blockStart, blockLength]
      rw [if_pos hk2]
      have h_sum := sum_Ioc_nat_eq_sum_Icc_int M (2 * (y / 2 ^ (k + 1)) * 2 ^ k) (2 * (y / 2 ^ (k + 1)) * 2 ^ k + 2 ^ k) f
      have H3 : (M + ↑(2 * (y / 2 ^ (k + 1)) * 2 ^ k) + 1) = M + 2 * ↑(y / 2 ^ (k + 1)) * 2 ^ k + 1 := by
        push_cast
        ring
      have H4 : M + ↑(2 * (y / 2 ^ (k + 1)) * 2 ^ k + 2 ^ k) = M + 2 * ↑(y / 2 ^ (k + 1)) * 2 ^ k + ↑(2 ^ k) := by
        push_cast
        ring
      rw [H3, H4] at h_sum
      exact h_sum
    · intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
      injection hab with h_eq
      injection h_eq with h_eq2
      ext
      exact h_eq2

  have hcard : ∀ y ∈ Finset.range (N + 1), (prefixBlocks y).card ≤ Nat.log2 N + 1 := by
    intro y _
    dsimp [prefixBlocks]
    split_ifs
    · apply le_trans Finset.card_image_le
      apply le_trans Finset.card_attach.le
      apply le_trans (Finset.card_filter_le _ _)
      exact (Finset.card_range _).le
    · simp

  have hlength : ∀ i, blockLength i ≤ N := by
    intro i
    dsimp [blockLength]
    split_ifs with h
    · omega
    · omega

  have hoverlap : (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1) (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    have H : (∑ k : Fin (Nat.log2 N + 1), ∑ j : Fin (N + 1),
      ∑ n ∈ Finset.Icc (blockStart (k, j) + 1) (blockStart (k, j) + blockLength (k, j)), ‖b n‖ ^ 2) ≤
      ∑ k : Fin (Nat.log2 N + 1), ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      apply sum_biUnion_le (Finset.univ) (fun j => Finset.Icc (blockStart (k, j) + 1) (blockStart (k, j) + blockLength (k, j)))
      · intro j1 _ j2 _ hneq
        dsimp [blockStart, blockLength]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_Icc] at hx1 hx2
        split_ifs at hx1 hx2 with h1 h2
        · push_cast at hx1 hx2
          have hlt : j1.val < j2.val ∨ j2.val < j1.val := by
            have : j1.val ≠ j2.val := by intro hh; apply hneq; ext; exact hh
            omega
          cases hlt with
          | inl h_lt =>
            have : j1.val + 1 ≤ j2.val := h_lt
            have H_le : j1.val * 2 ^ k.val + 2 ^ k.val ≤ j2.val * 2 ^ k.val := by
              calc
                j1.val * 2 ^ k.val + 2 ^ k.val = (j1.val + 1) * 2 ^ k.val := by ring
                _ ≤ j2.val * 2 ^ k.val := Nat.mul_le_mul_right _ this
            have H_le_z : (j1.val * 2 ^ k.val + 2 ^ k.val : ℕ) ≤ j2.val * 2 ^ k.val := H_le
            have H_le_int :
                (j1.val : ℤ) * (2 ^ k.val : ℤ) + (2 ^ k.val : ℤ) ≤
                  (j2.val : ℤ) * (2 ^ k.val : ℤ) := by
              exact_mod_cast H_le_z
            omega
          | inr h_lt =>
            have : j2.val + 1 ≤ j1.val := h_lt
            have H_le : j2.val * 2 ^ k.val + 2 ^ k.val ≤ j1.val * 2 ^ k.val := by
              calc
                j2.val * 2 ^ k.val + 2 ^ k.val = (j2.val + 1) * 2 ^ k.val := by ring
                _ ≤ j1.val * 2 ^ k.val := Nat.mul_le_mul_right _ this
            have H_le_int :
                (j2.val : ℤ) * (2 ^ k.val : ℤ) + (2 ^ k.val : ℤ) ≤
                  (j1.val : ℤ) * (2 ^ k.val : ℤ) := by
              exact_mod_cast H_le
            omega
        · omega
        · omega
        · omega
      · intro j _
        dsimp [blockStart, blockLength]
        split_ifs with h
        · intro x hx
          rw [Finset.mem_Icc] at hx ⊢
          push_cast at hx
          have h1 : 0 ≤ (j.val : ℤ) * (2 ^ k.val : ℤ) := by positivity
          have h2 : (j.val * 2 ^ k.val + 2 ^ k.val : ℕ) ≤ N := h
          have h2z : (j.val : ℤ) * (2 ^ k.val : ℤ) + (2 ^ k.val : ℤ) ≤ (N : ℤ) := by
            exact_mod_cast h2
          omega
        · intro x hx
          rw [Finset.mem_Icc] at hx
          omega
      · intro x _
        positivity
    simpa [Finset.sum_const, nsmul_eq_mul] using H

  exact weighted_primitive_prefix_maximal_of_dyadic_decomposition b M N Q hQ blockStart blockLength prefixBlocks hdecomp hcard hlength hoverlap

end AnalyticNumberTheory.LargeSieve
