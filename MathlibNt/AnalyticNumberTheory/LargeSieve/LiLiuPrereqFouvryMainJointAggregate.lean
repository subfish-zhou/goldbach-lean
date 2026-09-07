import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainRestrictedArithmetic

/-! # The complete restricted main arithmetic aggregate

Cauchy--Schwarz is applied jointly over the common index and all ordered
bases, after the r mean. The two resulting sums use different fiberings of
the same retained carrier. No unrestricted common-index residual is used.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private def core (v : WGramSecondaryBase) : ℕ × (ℕ × ℤ) × (ℕ × ℤ) :=
  (v.1, (v.2.1.1, v.2.1.2.2), (v.2.2.1, v.2.2.2.2))

private def pair (v : WGramSecondaryBase) : ℕ × ℕ :=
  (v.2.1.2.1, v.2.2.2.1)

private def join (b : ℕ × (ℕ × ℤ) × (ℕ × ℤ)) (p : ℕ × ℕ) :
    WGramSecondaryBase :=
  (b.1, (b.2.1.1, p.1, b.2.1.2), (b.2.2.1, p.2, b.2.2.2))

private theorem join_core (v : WGramSecondaryBase) : join (core v) (pair v) = v := rfl

private def indexGcd (a : ℤ) (v : WGramSecondaryBase) : ℝ :=
  (v.1.gcd (iv3MainConstant v.2.1.1 v.2.2.1 v.2.1.2.1 v.2.2.2.1
    a v.2.1.2.2 v.2.2.2.2).natAbs : ℝ)

private def jointGcd (d : ℕ) (a : ℤ) (v : WGramSecondaryBase) : ℝ :=
  (((v.2.1.2.1 * v.2.2.2.1).gcd
    (iv3CorrelationNumerator d v.1 v.2.1.1 v.2.2.1 v.2.1.2.1 v.2.2.2.1
      a v.2.1.2.2 v.2.2.2.2).natAbs : ℝ) *
    fouvryTau 2 (iv3CorrelationNumerator d v.1 v.2.1.1 v.2.2.1
      v.2.1.2.1 v.2.2.2.1 a v.2.1.2.2 v.2.2.2.2).natAbs)

private theorem index_sum_le
    {d N M S Hmax : ℕ} {a : ℤ} {H : Finset ℤ}
    {G : Finset WGramSecondaryBase} (ha : a ≠ 0)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ h.natAbs ≤ Hmax)
    (hG : ∀ v ∈ G, mainRestrictedData d a N M S H v)
    {T : ℝ} (hT : 0 ≤ T)
    (hτ : ∀ k : ℕ, 0 < k → k ≤ mainRestrictedMax a d N M Hmax S →
      (fouvryTau 2 k : ℝ) ≤ T) :
    (∑ v ∈ G, indexGcd a v) ≤
      (N : ℝ) * M ^ 2 * S ^ 2 * (H.card : ℝ) ^ 2 * T := by
  let E := (Ioc 0 M ×ˢ (Ioc 0 S ×ˢ H)) ×ˢ (Ioc 0 M ×ˢ (Ioc 0 S ×ˢ H))
  have hsub : G.image Prod.snd ⊆ E := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨_, hm, hm', hs, hs', hh, hh', _⟩ := hG v hv
    exact mem_product.mpr ⟨mem_product.mpr ⟨hm, mem_product.mpr ⟨hs, hh⟩⟩,
      mem_product.mpr ⟨hm', mem_product.mpr ⟨hs', hh'⟩⟩⟩
  have hcard : ((G.image Prod.snd).card : ℝ) ≤
      (M : ℝ) ^ 2 * S ^ 2 * (H.card : ℝ) ^ 2 := by
    have hc : ((G.image Prod.snd).card : ℝ) ≤ E.card := by
      exact_mod_cast card_le_card hsub
    apply hc.trans_eq
    simp only [E, card_product, Nat.card_Ioc, Nat.sub_zero, Nat.cast_mul]
    ring
  have hf (b : WGramMainBase) (hb : b ∈ G.image Prod.snd) :
      (∑ v ∈ G.filter (fun v => v.2 = b), indexGcd a v) ≤ N * T := by
    obtain ⟨w, hw, he⟩ := mem_image.mp hb
    obtain ⟨_, hm, hm', hs, hs', hh, hh', _, _, hmain, _⟩ := hG w hw
    have hB : iv3MainConstant b.1.1 b.2.1 b.1.2.1 b.2.2.1 a b.1.2.2 b.2.2.2 ≠ 0 := by
      rw [← he]
      exact iv3MainConstant_ne_zero ha (mem_Ioc.mp hm).1 (mem_Ioc.mp hm').1 hmain
    let B := (iv3MainConstant b.1.1 b.2.1 b.1.2.1 b.2.2.1 a b.1.2.2 b.2.2.2).natAbs
    have hBmax : B ≤ mainRestrictedMax a d N M Hmax S := by
      dsimp only [B]
      rw [← he]
      exact mainRestricted_constant_le (mem_Ioc.mp hm).2 (mem_Ioc.mp hm').2
        (mem_Ioc.mp hs).2 (mem_Ioc.mp hs').2 (hH _ hh).2 (hH _ hh').2
    let F := G.filter (fun v => v.2 = b)
    have hinj : Set.InjOn (fun v : WGramSecondaryBase => v.1) F := by
      intro v hv w hw hn
      exact Prod.ext hn ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)
    have hsumeq : (∑ v ∈ F, indexGcd a v) =
        ∑ n ∈ F.image Prod.fst, (n.gcd B : ℝ) := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro v hv
      change (v.1.gcd (iv3MainConstant v.2.1.1 v.2.2.1 v.2.1.2.1 v.2.2.2.1
        a v.2.1.2.2 v.2.2.2.2).natAbs : ℝ) = _
      rw [(mem_filter.mp hv).2]
    have hnsub : F.image Prod.fst ⊆ Ioc 0 N := by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
      exact (hG v (mem_filter.mp hv).1).1
    have hsum : (∑ n ∈ Ioc 0 N, (n.gcd B : ℝ)) ≤ N * (B.divisors.card : ℝ) := by
      exact_mod_cast (show (∑ n ∈ Ioc 0 N, n.gcd B) ≤ N * B.divisors.card by
        simpa only [Nat.gcd_comm] using sum_gcd_le (Int.natAbs_ne_zero.mpr hB) N)
    calc
      _ = ∑ n ∈ F.image Prod.fst, (n.gcd B : ℝ) := hsumeq
      _ ≤ ∑ n ∈ Ioc 0 N, (n.gcd B : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hnsub (fun _ _ _ => by positivity)
      _ ≤ N * (B.divisors.card : ℝ) := hsum
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [fouvryTau_two] using
          hτ B (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hB)) hBmax)
        (Nat.cast_nonneg N)
  calc
    _ = ∑ b ∈ G.image Prod.snd, ∑ v ∈ G.filter (fun v => v.2 = b), indexGcd a v :=
      mainRestricted_sum_fibers G Prod.snd _
    _ ≤ ∑ _b ∈ G.image Prod.snd, (N : ℝ) * T := sum_le_sum hf
    _ = ((G.image Prod.snd).card : ℝ) * (N * T) := by simp
    _ ≤ ((M : ℝ) ^ 2 * S ^ 2 * (H.card : ℝ) ^ 2) * (N * T) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg N) hT)
    _ = _ := by ring

private theorem joint_sum_le
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hjoint : ∀ (a U V : ℤ) (S : ℕ) (P : Finset (ℕ × ℕ)),
      a ≠ 0 → U ≠ 0 → V ≠ 0 →
      (∀ p ∈ P, (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
        mainJointNumerator a U V p.1 p.2 ≠ 0) →
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
        fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs) ≤
        C * (S : ℝ) ^ 2 * (1 + Real.log S) *
          ((a.natAbs * (U.natAbs + V.natAbs) * S : ℕ) : ℝ) ^ δ)
    {d N M S Hmax : ℕ} {a : ℤ} {H : Finset ℤ}
    {G : Finset WGramSecondaryBase} (ha : a ≠ 0) (hS : 0 < S)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ h.natAbs ≤ Hmax)
    (hG : ∀ v ∈ G, mainRestrictedData d a N M S H v) :
    (∑ v ∈ G, jointGcd d a v) ≤
      ((N : ℝ) * M ^ 2 * (H.card : ℝ) ^ 2) *
        (C * S ^ 2 * (1 + Real.log S) * (mainRestrictedMax a d N M Hmax S : ℝ) ^ δ) := by
  let E := Ioc 0 N ×ˢ ((Ioc 0 M ×ˢ H) ×ˢ (Ioc 0 M ×ˢ H))
  let B := C * S ^ 2 * (1 + Real.log S) * (mainRestrictedMax a d N M Hmax S : ℝ) ^ δ
  have hlog : 0 ≤ 1 + Real.log (S : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hS : (1 : ℝ) ≤ S)
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsub : G.image core ⊆ E := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨hn, hm, hm', _, _, hh, hh', _⟩ := hG v hv
    exact mem_product.mpr ⟨hn, mem_product.mpr
      ⟨mem_product.mpr ⟨hm, hh⟩, mem_product.mpr ⟨hm', hh'⟩⟩⟩
  have hcard : ((G.image core).card : ℝ) ≤ (N : ℝ) * M ^ 2 * (H.card : ℝ) ^ 2 := by
    have hc : ((G.image core).card : ℝ) ≤ E.card := by exact_mod_cast card_le_card hsub
    apply hc.trans_eq
    simp only [E, card_product, Nat.card_Ioc, Nat.sub_zero, Nat.cast_mul]
    ring
  have hf (b : ℕ × (ℕ × ℤ) × (ℕ × ℤ)) (hb : b ∈ G.image core) :
      (∑ v ∈ G.filter (fun v => core v = b), jointGcd d a v) ≤ B := by
    obtain ⟨w, hw, he⟩ := mem_image.mp hb
    obtain ⟨hn, hm, hm', _, _, hh, hh', hd, hd', _⟩ := hG w hw
    let U := mainRestrictedU d b.1 b.2.1.1 b.2.2.1 b.2.1.2
    let V := mainRestrictedU d b.1 b.2.2.1 b.2.1.1 b.2.2.2
    have hU : U ≠ 0 := by
      dsimp only [U]; rw [← he]
      exact mainRestrictedU_ne_zero (hH _ hh).1 (mem_Ioc.mp hm').1 hd
    have hV : V ≠ 0 := by
      dsimp only [V]; rw [← he]
      exact mainRestrictedU_ne_zero (hH _ hh').1 (mem_Ioc.mp hm).1 hd'
    have hmax : a.natAbs * (U.natAbs + V.natAbs) * S ≤ mainRestrictedMax a d N M Hmax S := by
      dsimp only [U, V]; rw [← he]
      exact mainRestricted_joint_scale_le (mem_Ioc.mp hn).2 (mem_Ioc.mp hm).2
        (mem_Ioc.mp hm').2 (hH _ hh).2 (hH _ hh').2
    let F := G.filter (fun v => core v = b)
    let P := F.image pair
    have hinj : Set.InjOn pair F := by
      intro v hv w hw hp
      rw [← join_core v, ← join_core w, hp,
        (mem_filter.mp hv).2, (mem_filter.mp hw).2]
    have hP (p : ℕ × ℕ) (hp : p ∈ P) :
        (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
          mainJointNumerator a U V p.1 p.2 ≠ 0 := by
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hp
      have hvd := hG v (mem_filter.mp hv).1
      refine ⟨mem_Ioc.mp hvd.2.2.2.1, mem_Ioc.mp hvd.2.2.2.2.1, ?_⟩
      dsimp only [U, V]
      rw [← (mem_filter.mp hv).2]
      exact (mainRestricted_numerator d v.1 v.2.1.1 v.2.2.1 v.2.1.2.1
        v.2.2.2.1 a v.2.1.2.2 v.2.2.2.2) ▸ hvd.2.2.2.2.2.2.2.2.2.2
    have hsumeq : (∑ v ∈ F, jointGcd d a v) =
        ∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
          fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs := by
      rw [show P = F.image pair from rfl, sum_image hinj]
      apply sum_congr rfl
      intro v hv
      dsimp only [U, V]
      rw [← (mem_filter.mp hv).2]
      simp only [jointGcd, core, pair, mainRestricted_numerator]
    calc
      _ = _ := hsumeq
      _ ≤ C * (S : ℝ) ^ 2 * (1 + Real.log S) *
          ((a.natAbs * (U.natAbs + V.natAbs) * S : ℕ) : ℝ) ^ δ :=
        hjoint a U V S P ha hU hV hP
      _ ≤ B := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmax) hδ) (by positivity)
  calc
    _ = ∑ b ∈ G.image core, ∑ v ∈ G.filter (fun v => core v = b), jointGcd d a v :=
      mainRestricted_sum_fibers G core _
    _ ≤ ∑ _b ∈ G.image core, B := sum_le_sum hf
    _ = ((G.image core).card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

/-- An explicit bound with no remaining arithmetic or base sum.
The constants are chosen before every coefficient and every finite carrier. -/
theorem mainRestricted_sqrt_gcd_sum {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cτ Cjoint : ℝ, 0 < Cτ ∧ 0 < Cjoint ∧
    ∀ (d N M Hmax S R : ℕ) (a : ℤ) (H : Finset ℤ) (G : Finset WGramSecondaryBase),
      a ≠ 0 → 0 < S →
      (∀ h ∈ H, h ≠ 0 ∧ h.natAbs ≤ Hmax) →
      (∀ v ∈ G, mainRestrictedData d a N M S H v) →
      (∑ v ∈ G, ∑ r ∈ Ioc 0 R, Real.sqrt
        ((v.1 * r * v.2.1.2.1 * v.2.2.2.1).gcd
          (iv3CorrelationNumerator d v.1 v.2.1.1 v.2.2.1 v.2.1.2.1 v.2.2.2.1
            a v.2.1.2.2 v.2.2.2.2).natAbs : ℝ)) ≤
        R * (Real.sqrt ((N : ℝ) * M ^ 2 * S ^ 2 * (H.card : ℝ) ^ 2 *
            (Cτ * (mainRestrictedMax a d N M Hmax S : ℝ) ^ δ)) *
          Real.sqrt (((N : ℝ) * M ^ 2 * (H.card : ℝ) ^ 2) *
            (Cjoint * S ^ 2 * (1 + Real.log S) *
              (mainRestrictedMax a d N M Hmax S : ℝ) ^ δ))) := by
  obtain ⟨Cτ, hCτ, hτ⟩ := fouvryTau_le_const_rpow (k := 2) (by decide) hδ
  obtain ⟨Cjoint, hCjoint, hjoint⟩ := mainJoint_mean_subpower hδ
  refine ⟨Cτ, Cjoint, hCτ, hCjoint, ?_⟩
  intro d N M Hmax S R a H G ha hS hH hG
  have hi := index_sum_le ha hH hG
    (show 0 ≤ Cτ * (mainRestrictedMax a d N M Hmax S : ℝ) ^ δ by positivity)
    (fun k hk hkmax => (hτ k hk).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hkmax) hδ.le) hCτ.le))
  have hj := joint_sum_le hδ.le hCjoint.le hjoint ha hS hH hG
  calc
    _ ≤ ∑ v ∈ G, (R : ℝ) *
        (Real.sqrt (indexGcd a v) * Real.sqrt (jointGcd d a v)) := by
      apply sum_le_sum
      intro v hv
      simpa only [indexGcd, jointGcd, Nat.cast_mul, fouvryTau_two] using
        iv3_main_sqrt_gcd_r_sum (hG v hv).2.2.2.2.2.2.2.2.2.2 R
    _ = R * ∑ v ∈ G, Real.sqrt (indexGcd a v) * Real.sqrt (jointGcd d a v) :=
      (mul_sum _ _ _).symm
    _ ≤ R * (Real.sqrt (∑ v ∈ G, indexGcd a v) *
        Real.sqrt (∑ v ∈ G, jointGcd d a v)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le G
        (fun _ => by dsimp [indexGcd]; positivity)
        (fun _ => by dsimp [jointGcd]; positivity)) (Nat.cast_nonneg R)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hi) (Real.sqrt_le_sqrt hj)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Nat.cast_nonneg R)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
