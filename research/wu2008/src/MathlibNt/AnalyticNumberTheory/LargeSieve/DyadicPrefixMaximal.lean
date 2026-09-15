import MathlibNt.AnalyticNumberTheory.LargeSieve.PrefixMaximal

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

lemma sum_Ioc_nat_eq_sum_Icc_int (M : ℤ) (a b : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ioc a b, f (M + n)) = ∑ n ∈ Finset.Icc (M + a + 1) (M + b), f n := by
  refine Finset.sum_bij (fun (n : ℕ) _ => M + (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.mp hn
    rw [Finset.mem_Icc]
    omega
  · intro n1 _ n2 _ h
    omega
  · intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Icc.mp hn
    refine ⟨(n - M).toNat, ?_, ?_⟩
    · rw [Finset.mem_Ioc]
      omega
    · omega
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
  have hbit := div_mod_two_eq y k
  have hquotient := Nat.div_le_self y (2^k)
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
  rw [← Finset.sum_biUnion h_disj]
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
      simpa only [Nat.cast_zero, add_zero] using (sum_Ioc_nat_eq_sum_Icc_int M 0 y f).symm
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
          simpa only [hk1] using div_mod_two_eq y k
        have H2_eq : 2 * (y / 2^(k+1)) * 2^k + 2^k = (y / 2^k) * 2^k := by
          calc
            2 * (y / 2^(k+1)) * 2^k + 2^k = (2 * (y / 2^(k+1)) + 1) * 2^k := by ring
            _ = (y / 2^k) * 2^k := by rw [← H]
        rw [H2_eq]
        exact (Nat.div_mul_le_self y (2^k)).trans hy2
      dsimp [blockStart, blockLength]
      rw [if_pos hk2]
      have h_sum := sum_Ioc_nat_eq_sum_Icc_int M (2 * (y / 2 ^ (k + 1)) * 2 ^ k)
        (2 * (y / 2 ^ (k + 1)) * 2 ^ k + 2 ^ k) f
      push_cast at h_sum
      simpa only [Nat.cast_pow, Nat.cast_ofNat, add_assoc] using h_sum
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
      -- At a fixed scale, the end of an earlier aligned block precedes the next start.
      have hblockEnd_le_start (a b : ℕ) (hab : a < b) :
          (a : ℤ) * 2 ^ k.val + 2 ^ k.val ≤ (b : ℤ) * 2 ^ k.val := by
        have hsucc : a + 1 ≤ b := hab
        have hscaled := Nat.mul_le_mul_right (2 ^ k.val) hsucc
        exact_mod_cast (show a * 2 ^ k.val + 2 ^ k.val ≤ b * 2 ^ k.val by
          simpa only [Nat.add_mul, one_mul] using hscaled)
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
            have hsep := hblockEnd_le_start j1.val j2.val h_lt
            omega
          | inr h_lt =>
            have hsep := hblockEnd_le_start j2.val j1.val h_lt
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
          have h2z : (j.val : ℤ) * (2 ^ k.val : ℤ) + (2 ^ k.val : ℤ) ≤ (N : ℤ) := by
            exact_mod_cast h
          omega
        · intro x hx
          rw [Finset.mem_Icc] at hx
          omega
      · intro x _
        positivity
    simpa [Finset.sum_const, nsmul_eq_mul] using H

  exact weighted_primitive_prefix_maximal_of_dyadic_decomposition b M N Q hQ blockStart blockLength prefixBlocks hdecomp hcard hlength hoverlap

end AnalyticNumberTheory.LargeSieve
