import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeDeltaOriginal

/-!
# Shared fixed-scale large-common-modulus bound for original W

The actual nonzero shifted differences satisfy `|m*n-a| ≤ 4*Cscale*x`.
Two divisor estimates pay these signed modulus rows; a third pays the
nonzero beta difference, which still satisfies `|n₁-n₂| ≤ x`.
Consequently the fixed enlargement enters the constant as
`(4*Cscale)^(2*ε/3)`, without changing the main power `x^ε`.
The diagonal costs its square mass, not the square of its absolute mass.
No WF property of a restricted weight is asserted.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- On the actual nonzero bump, only the auxiliary divisor-growth enclosure
is enlarged. Neither the bump scale nor the original residue is changed. -/
theorem kDelta_natAbs_mul_sub_le_of_cutoff {M T x Cscale : ℝ}
    (hCscale : 1 ≤ Cscale) (hx : 1 ≤ x) (hM : 0 < M)
    (hMT : M * T ≤ x) {m n : ℕ} (hn : (n : ℝ) ≤ T)
    (hm : scaledDyadicCutoff M m ≠ 0) (a : ℤ)
    (ha : |(a : ℝ)| ≤ Cscale * x) :
    (((m : ℤ) * n - a).natAbs : ℝ) ≤ (4 * Cscale) * x := by
  have hxx : x ≤ Cscale * x := le_mul_of_one_le_left (by linarith) hCscale
  simpa only [mul_assoc] using
    natAbs_mul_sub_le_of_cutoff hM (hMT.trans hxx) hn hm a ha

private theorem kDelta_pair_sum_le {M Y B : ℝ}
    (hM : 1 ≤ M) (hY : 0 < Y) (hB : 1 ≤ B)
    (N : Finset ℕ) (β : ℕ → ℝ)
    (hdiff : ∀ n₁ ∈ N, ∀ n₂ ∈ N, n₁ ≠ n₂ →
      (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) ≤ B) :
    (∑ p ∈ N ×ˢ N, |β p.1 * β p.2| *
      (if p.1 = p.2 then 5 * M else
        (4 * M / Y + 1) * (fouvryTau 2 ((p.1 : ℤ) - p.2).natAbs : ℝ))) ≤
      5 * B * (M * (∑ n ∈ N, β n ^ 2) +
        (M / Y + 1) * (∑ n ∈ N, |β n|) ^ 2) := by
  have hMY : 0 ≤ M / Y := div_nonneg (by linarith) hY.le
  have hmass : 0 ≤ ∑ n ∈ N, β n ^ 2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hfull : (∑ p ∈ N ×ˢ N, |β p.1 * β p.2|) = (∑ n ∈ N, |β n|) ^ 2 := by
    simp only [sum_product, abs_mul, ← mul_sum, ← sum_mul, pow_two]
  calc
    _ ≤ ∑ p ∈ N ×ˢ N,
        ((if p.1 = p.2 then 5 * M * |β p.1 * β p.2| else 0) +
          ((4 * M / Y + 1) * B) * |β p.1 * β p.2|) := by
      apply sum_le_sum
      intro p hp
      split_ifs with he
      · have hh : 0 ≤ ((4 * M / Y + 1) * B) * |β p.1 * β p.2| := by positivity
        nlinarith
      · simp only [zero_add]
        have hh := hdiff _ (mem_product.mp hp).1 _ (mem_product.mp hp).2 he
        have hh' := mul_le_mul_of_nonneg_left hh
          (show 0 ≤ |β p.1 * β p.2| * (4 * M / Y + 1) by positivity)
        nlinarith
    _ = 5 * M * (∑ n ∈ N, β n ^ 2) +
        ((4 * M / Y + 1) * B) * (∑ n ∈ N, |β n|) ^ 2 := by
      rw [sum_add_distrib, ← mul_sum, hfull]
      congr 1
      simp [sum_product, ← mul_sum, ← pow_two]
    _ ≤ _ := by
      have hdiag : 5 * M * (∑ n ∈ N, β n ^ 2) ≤
          5 * B * (M * (∑ n ∈ N, β n ^ 2)) := by
        nlinarith [mul_le_mul_of_nonneg_right hB
          (show 0 ≤ 5 * M * (∑ n ∈ N, β n ^ 2) by positivity)]
      have hoff : ((4 * M / Y + 1) * B) * (∑ n ∈ N, |β n|) ^ 2 ≤
          5 * B * ((M / Y + 1) * (∑ n ∈ N, |β n|) ^ 2) := by
        have hscalar : (4 * M / Y + 1) * B ≤ 5 * B * (M / Y + 1) := by
          rw [mul_div_assoc]
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hscalar (sq_nonneg (∑ n ∈ N, |β n|))]
      linarith

/-- The constant precedes all scales, supports, coefficients, residues and
masks. The beta coefficient is arbitrary apart from the stated support
condition; only the modulus coefficient has a fixed divisor order. -/
theorem wMaskedOriginal_abs_le_largeDelta_pair_mass_kscale (j : ℕ)
    {ε Cscale : ℝ} (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ Y : ℝ, 0 < Y → ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * (∑ n ∈ N, β n ^ 2) +
          (M / Y + 1) * (∑ n ∈ N, |β n|) ^ 2) := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 3 by linarith)
  obtain ⟨E, hE, htwo⟩ := fouvryTau_le_const_rpow (k := 2) (by norm_num)
    (show 0 < ε / 3 by linarith)
  refine ⟨5 * D ^ 2 * (4 * Cscale) ^ (2 * ε / 3) * (1 + E), by positivity, ?_⟩
  intro M T x hM hT hx hMT N Q hN β c hc a ha hsupport Y hY P hP
  let A : ℝ := D * (4 * Cscale * x) ^ (ε / 3)
  let B : ℝ := (1 + E) * x ^ (ε / 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hx0 : 0 < x := by linarith
  have hB : 1 ≤ B := by
    have hp := Real.one_le_rpow hx (show 0 ≤ ε / 3 by linarith)
    dsimp [B]
    nlinarith
  have hnT (n : ℕ) (hn : n ∈ N) : (n : ℝ) ≤ T :=
    (by exact_mod_cast (mem_Ioc.mp (hN hn)).2 : (n : ℝ) ≤ ⌊T⌋₊).trans
      (Nat.floor_le (by linarith))
  have hrow (n : ℕ) (hn : n ∈ N) (hβn : β n ≠ 0)
      (m : ℕ) (hm : scaledDyadicCutoff M m ≠ 0) :
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ A := by
    have hne := mul_sub_ne_zero_of_not_dvd m n a (hsupport n hn hβn)
    calc
      _ ≤ (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) :=
        sum_modEq_abs_le_fouvryTau j Q c hc m n a hne
      _ ≤ D * (((m : ℤ) * n - a).natAbs : ℝ) ^ (ε / 3) :=
        hdiv _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
      _ ≤ A := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact Real.rpow_le_rpow (by positivity)
          (kDelta_natAbs_mul_sub_le_of_cutoff hCscale hx (by linarith) hMT (hnT n hn) hm a ha)
          (by linarith)
  have hdiff (n₁ : ℕ) (hn₁ : n₁ ∈ N) (n₂ : ℕ) (hn₂ : n₂ ∈ N)
      (hne : n₁ ≠ n₂) :
      (fouvryTau 2 ((n₁ : ℤ) - n₂).natAbs : ℝ) ≤ B := by
    have hne' : (n₁ : ℤ) - n₂ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have hTx : T ≤ x := by nlinarith
    have hnx : (((n₁ : ℤ) - n₂).natAbs : ℝ) ≤ x := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      apply abs_sub_le_iff.mpr
      constructor <;> nlinarith [hnT n₁ hn₁, hnT n₂ hn₂,
        Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) n₂]
    calc
      _ ≤ E * (((n₁ : ℤ) - n₂).natAbs : ℝ) ^ (ε / 3) :=
        htwo _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne'))
      _ ≤ E * x ^ (ε / 3) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        exact Real.rpow_le_rpow (by positivity) hnx (by linarith)
      _ ≤ B := by dsimp [B]; nlinarith [Real.rpow_nonneg hx0.le (ε / 3)]
  have hAsq : A ^ 2 = D ^ 2 * (4 * Cscale) ^ (2 * ε / 3) * x ^ (2 * ε / 3) := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * Cscale * x)]
    norm_num
    rw [show ε / 3 * 2 = 2 * ε / 3 by ring,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Cscale) hx0.le]
    ring
  have hAB : A ^ 2 * (5 * B) =
      (5 * D ^ 2 * (4 * Cscale) ^ (2 * ε / 3) * (1 + E)) * x ^ ε := by
    rw [hAsq]
    dsimp [B]
    calc
      _ = (5 * D ^ 2 * (4 * Cscale) ^ (2 * ε / 3) * (1 + E)) *
          (x ^ (2 * ε / 3) * x ^ (ε / 3)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hx0, show 2 * ε / 3 + ε / 3 = ε by ring]
  calc
    _ ≤ A ^ 2 * ∑ p ∈ N ×ˢ N, |β p.1 * β p.2| *
        (if p.1 = p.2 then 5 * M else
          (4 * M / Y + 1) * (fouvryTau 2 ((p.1 : ℤ) - p.2).natAbs : ℝ)) :=
      wMaskedOriginal_abs_le_largeDelta_row_cap hM hY hA N Q β c a hrow P hP
    _ ≤ A ^ 2 * (5 * B * (M * (∑ n ∈ N, β n ^ 2) +
        (M / Y + 1) * (∑ n ∈ N, |β n|) ^ 2)) :=
      mul_le_mul_of_nonneg_left (kDelta_pair_sum_le hM hY hB N β hdiff) (sq_nonneg A)
    _ = _ := by rw [← mul_assoc, hAB]

/-- Evaluating the beta square and absolute masses with fixed-order divisor
means leaves the diagonal at length `T`, while the off-diagonal receives
the factor `M / Y + 1`. -/
theorem wMaskedOriginal_abs_le_largeDelta_kscale {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    {ε Cscale : ℝ} (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ Y : ℝ, 0 < Y → ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * T * (1 + Real.log T) ^ (k ^ 2 - 1) +
          (M / Y + 1) * (T * (1 + Real.log T) ^ (k - 1)) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := wMaskedOriginal_abs_le_largeDelta_pair_mass_kscale j hε hCscale
  refine ⟨C, hC, ?_⟩
  intro M T x hM hT hx hMT N Q hN β c hβ hc a ha hsupport Y hY P hP
  apply (hb M T x hM hT hx hMT N Q hN β c hc a ha hsupport Y hY P hP).trans
  have hsq := sum_alpha_sq_le_fouvryTau hk hT N hN β hβ
  have habs : (∑ n ∈ N, |β n|) ≤ T * (1 + Real.log T) ^ (k - 1) := by
    calc
      _ ≤ ∑ n ∈ N, (fouvryTau k n : ℝ) := sum_le_sum hβ
      _ ≤ ∑ n ∈ Ioc 0 ⌊T⌋₊, (fouvryTau k n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ ↦ Nat.cast_nonneg _)
      _ ≤ _ := sum_fouvryTau_le_real hk hT
  rw [mul_assoc M T]
  gcongr

/-- The constant precedes all scales, supports, coefficients, residues and
masks. The beta coefficient is arbitrary apart from the stated support
condition; only the modulus coefficient has a fixed divisor order. -/
theorem wMaskedOriginal_abs_le_largeDelta_pair_mass (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ Y : ℝ, 0 < Y → ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * (∑ n ∈ N, β n ^ 2) +
          (M / Y + 1) * (∑ n ∈ N, |β n|) ^ 2) := by
  simpa only [one_mul] using
    (wMaskedOriginal_abs_le_largeDelta_pair_mass_kscale
      (Cscale := 1) j hε le_rfl)

/-- Evaluating the beta square and absolute masses with fixed-order divisor
means leaves the diagonal at length `T`, while the off-diagonal receives
the factor `M / Y + 1`. -/
theorem wMaskedOriginal_abs_le_largeDelta {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ Y : ℝ, 0 < Y → ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.1.1.gcd t.1.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * T * (1 + Real.log T) ^ (k ^ 2 - 1) +
          (M / Y + 1) * (T * (1 + Real.log T) ^ (k - 1)) ^ 2) := by
  simpa only [one_mul] using
    (wMaskedOriginal_abs_le_largeDelta_kscale
      (Cscale := 1) hk j hε le_rfl)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
