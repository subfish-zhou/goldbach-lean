import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeSupportHarmonic
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaClean

/-!
# Sparse modulus support and inverse-lcm mass

The canonical supported parts `δ₁,δ₂` force a large square divisor in the
corresponding modulus. A gcd harmonic row estimate and three fixed-order
divisor bounds preserve this saving for signed inverse-lcm weights.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Large canonical `δ₁` forces a large square divisor of the first modulus. -/
theorem deltaOne_mem_largeSquareDivisorSet (r N₁ N₂ : ℕ)
    {q T : ℕ} {Y : ℝ} (hq : q ∈ Ioc 0 T) (hY : 0 ≤ Y)
    (hlarge : Y < ((wGCDData q r N₁ N₂).δ₁ : ℝ)) :
    q ∈ largeSquareDivisorSet T (Real.sqrt Y) :=
  wGCDData_mem_largeSquareDivisorSet 0 0 r hq hY hlarge

/-- Large canonical `δ₂` forces a large square divisor of the second modulus. -/
theorem deltaTwo_mem_largeSquareDivisorSet (q N₁ N₂ : ℕ)
    {r T : ℕ} {Y : ℝ} (hr : r ∈ Ioc 0 T) (hY : 0 ≤ Y)
    (hlarge : Y < ((wGCDData q r N₁ N₂).δ₂ : ℝ)) :
    r ∈ largeSquareDivisorSet T (Real.sqrt Y) := by
  apply wGCDData_mem_largeSquareDivisorSet 0 0 q hr hY
  simpa only [wGCDData, Nat.gcd_comm] using hlarge

/-- A deterministic sparse inverse-lcm estimate: two coefficient bounds and
one divisor bound suffice. The support may be any subset of the sparse set. -/
theorem sum_abs_lcm_weight_sparse_le {L Z A B : ℝ}
    (hL : 1 ≤ L) (hZ : 0 < Z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Q S : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (hSQ : S ⊆ Q)
    (hS : S ⊆ largeSquareDivisorSet ⌊L⌋₊ Z)
    (c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ A)
    (hτ : ∀ q ∈ S, (fouvryTau 2 q : ℝ) ≤ B) :
    (∑ q ∈ S, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|) ≤
      2 * A ^ 2 * B * (1 + Real.log L) ^ 2 / Z := by
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg hL]
  have hh : (∑ q ∈ S, (1 : ℝ) / q) ≤ (2 / Z) * (1 + Real.log L) :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_one_div_largeSquareDivisorSet_le hL hZ)
  calc
    _ ≤ ∑ q ∈ S, ∑ r ∈ Q, A ^ 2 * ((1 : ℝ) / (q.lcm r : ℝ)) := by
      apply sum_le_sum
      intro q hq
      apply sum_le_sum
      intro r hr
      rw [abs_div, abs_mul, Nat.abs_cast]
      calc
        _ ≤ (A * A) / (q.lcm r : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul (hc q (hSQ hq)) (hc r hr) (abs_nonneg _) hA)
            (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = A ^ 2 * ∑ q ∈ S, ∑ r ∈ Q, (1 : ℝ) / (q.lcm r : ℝ) := by
      simp only [mul_sum]
    _ ≤ A ^ 2 * ∑ q ∈ S, (fouvryTau 2 q : ℝ) / q * (1 + Real.log L) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      apply sum_le_sum
      intro q hq
      exact sum_one_div_lcm_le_tau_log hL Q hQ (mem_Ioc.mp (hQ (hSQ hq))).1
    _ ≤ A ^ 2 * ∑ q ∈ S, B / q * (1 + Real.log L) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hτ q hq) (Nat.cast_nonneg q)) hlog
    _ = A ^ 2 * B * (1 + Real.log L) * (∑ q ∈ S, (1 : ℝ) / q) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro _ _
      ring
    _ ≤ A ^ 2 * B * (1 + Real.log L) * ((2 / Z) * (1 + Real.log L)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- Constants depend only on the fixed divisor order and positive exponent,
and precede all changing scales, supports, and signed coefficients. -/
theorem sum_abs_lcm_weight_sparse_uniform (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L x Z : ℝ, 1 ≤ L → L ≤ x → 0 < Z →
      ∀ Q S : Finset ℕ, Q ⊆ Ioc 0 ⌊L⌋₊ → S ⊆ Q →
        S ⊆ largeSquareDivisorSet ⌊L⌋₊ Z →
      ∀ c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      (∑ q ∈ S, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|) ≤
        C * x ^ ε * (1 + Real.log L) ^ 2 / Z := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 3 by linarith)
  obtain ⟨E, hE, htwo⟩ := fouvryTau_le_const_rpow (k := 2) (by norm_num)
    (show 0 < ε / 3 by linarith)
  refine ⟨2 * D ^ 2 * E, by positivity, ?_⟩
  intro L x Z hL hLx hZ Q S hQ hSQ hS c hc
  have hx : 0 < x := lt_of_lt_of_le (by linarith : 0 < L) hLx
  have hqx (q : ℕ) (hq : q ∈ Q) : (q : ℝ) ≤ x :=
    (by exact_mod_cast (mem_Ioc.mp (hQ hq)).2 : (q : ℝ) ≤ ⌊L⌋₊).trans
      ((Nat.floor_le (by linarith)).trans hLx)
  have hpow (q : ℕ) (hq : q ∈ Q) : (q : ℝ) ^ (ε / 3) ≤ x ^ (ε / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (hqx q hq) (by linarith)
  have hc' (q : ℕ) (hq : q ∈ Q) : |c q| ≤ D * x ^ (ε / 3) := by
    calc
      _ ≤ (fouvryTau j q : ℝ) := hc q hq
      _ ≤ (fouvryTau (j + 1) q : ℝ) := by exact_mod_cast fouvryTau_le_succ j q
      _ ≤ D * (q : ℝ) ^ (ε / 3) := hdiv q (mem_Ioc.mp (hQ hq)).1
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow q hq) hD.le
  have hτ (q : ℕ) (hq : q ∈ S) : (fouvryTau 2 q : ℝ) ≤ E * x ^ (ε / 3) :=
    (htwo q (mem_Ioc.mp (hQ (hSQ hq))).1).trans
      (mul_le_mul_of_nonneg_left (hpow q (hSQ hq)) hE.le)
  have he : (x ^ (ε / 3)) ^ 2 * x ^ (ε / 3) = x ^ ε := by
    rw [← pow_succ, ← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  calc
    _ ≤ 2 * (D * x ^ (ε / 3)) ^ 2 * (E * x ^ (ε / 3)) *
        (1 + Real.log L) ^ 2 / Z :=
      sum_abs_lcm_weight_sparse_le hL hZ (by positivity) (by positivity)
        Q S hQ hSQ hS c hc' hτ
    _ = _ := by
      rw [mul_pow]
      calc
        _ = (2 * D ^ 2 * E) * ((x ^ (ε / 3)) ^ 2 * x ^ (ε / 3)) *
            (1 + Real.log L) ^ 2 / Z := by ring
        _ = _ := by rw [he]

/-- Either coordinate may carry the large square divisor. Arbitrary further
pair restrictions are allowed; overlap of the two sparse strips costs at most
a factor of two, and the original lcm denominator is unchanged. -/
theorem sum_abs_lcm_weight_sparse_pairs_uniform (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
   ∃ C : ℝ, 0 < C ∧ ∀ L x Z : ℝ, 1 ≤ L → L ≤ x → 0 < Z →
     ∀ Q : Finset ℕ, Q ⊆ Ioc 0 ⌊L⌋₊ →
     ∀ c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
     ∀ F : Finset (ℕ × ℕ), F ⊆ Q ×ˢ Q →
       (∀ p ∈ F, p.1 ∈ largeSquareDivisorSet ⌊L⌋₊ Z ∨
         p.2 ∈ largeSquareDivisorSet ⌊L⌋₊ Z) →
     (∑ p ∈ F, |c p.1 * c p.2 / (p.1.lcm p.2 : ℝ)|) ≤
       C * x ^ ε * (1 + Real.log L) ^ 2 / Z := by
 obtain ⟨C, hC, hbound⟩ := sum_abs_lcm_weight_sparse_uniform j hε
 refine ⟨2 * C, by positivity, ?_⟩
 intro L x Z hL hLx hZ Q hQ c hc F hF hFs
 let S := Q.filter (fun q => q ∈ largeSquareDivisorSet ⌊L⌋₊ Z)
 let f : ℕ × ℕ → ℝ := fun p => |c p.1 * c p.2 / (p.1.lcm p.2 : ℝ)|
 let E := ∑ q ∈ S, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|
 have hleft :
     (∑ p ∈ Q ×ˢ Q, if p.1 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0) =
       E := by
   simp only [sum_product, E, S, sum_filter, f, sum_ite_irrel, sum_const_zero]
 have hright :
     (∑ p ∈ Q ×ˢ Q, if p.2 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0) =
       E := by
   rw [sum_product, sum_comm]
   simpa only [sum_product, f, Nat.lcm_comm, mul_comm] using hleft
 have hE : E ≤ C * x ^ ε * (1 + Real.log L) ^ 2 / Z :=
   hbound L x Z hL hLx hZ Q S hQ (filter_subset _ _)
     (fun _ hq => (mem_filter.mp hq).2) c hc
 calc
   _ ≤ ∑ p ∈ F,
       ((if p.1 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0) +
         (if p.2 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0)) := by
     apply sum_le_sum
     intro p hp
     have hf : 0 ≤ f p := abs_nonneg _
     have hs := hFs p hp
     change f p ≤ _
     rcases hs with hs | hs <;> simp only [if_pos hs] <;> split_ifs <;> linarith
   _ ≤ ∑ p ∈ Q ×ˢ Q,
       ((if p.1 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0) +
         (if p.2 ∈ largeSquareDivisorSet ⌊L⌋₊ Z then f p else 0)) := by
     apply sum_le_sum_of_subset_of_nonneg hF
     intro p _ _
     have hf : 0 ≤ f p := abs_nonneg _
     split_ifs <;> linarith
   _ = E + E := by rw [sum_add_distrib, hleft, hright]
   _ ≤ C * x ^ ε * (1 + Real.log L) ^ 2 / Z +
       C * x ^ ε * (1 + Real.log L) ^ 2 / Z := add_le_add hE hE
   _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
