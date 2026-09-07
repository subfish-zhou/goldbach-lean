import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySeparatedCorrelation
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFloorDomain

/-!
# Reconstruction of an actual IV.3 k₁ section

The six-key and the five fixed coordinates `(r',n₁,n₂,s',h)` recover the
original extracted tuple, not merely its phase. Canonicality below is
expressed by prime support and coprimality, without an extraction oracle.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wKSectionDeltaPrime (K : WExtractedKey) : ℕ :=
  K.1.2.2.1 * K.1.2.2.2.2 / K.2

def wKSectionData (K : WExtractedKey) (r n₁ n₂ s k : ℕ) : WGCDData :=
  { d := K.1.1, d₁ := K.1.2.1, δ := K.1.2.2.1,
    δ₁ := K.1.2.2.2.1, δ₂ := K.1.2.2.2.2,
    k₁ := k, k₂ := r * s, n₁ := n₁, n₂ := n₂ }

def wKSectionTuple (K : WExtractedKey) (r n₁ n₂ s : ℕ) (h : ℤ) (k : ℕ) :
    WExtractedTuple × ℤ :=
  (((((K.2, wKSectionDeltaPrime K), (r, s))),
    (K.1.2.2.1 * K.1.2.2.2.1 * k, (K.1.1 * K.1.2.1 * n₁, K.1.1 * n₂))), h)

/-- All canonical restrictions independent of the varying first modulus.
The remaining canonical restrictions are just two coprimalities on `k`. -/
def wKSectionFixedCanonical (K : WExtractedKey) (r n₁ n₂ s : ℕ) : Prop :=
  0 < K.1.1 ∧ 0 < K.1.2.1 ∧ 0 < K.1.2.2.1 ∧
  0 < K.1.2.2.2.1 ∧ 0 < K.1.2.2.2.2 ∧
  0 < r ∧ 0 < s ∧ 0 < n₁ ∧ 0 < n₂ ∧
  (∀ p : ℕ, p.Prime → p ∣ K.1.2.1 → p ∣ K.1.1) ∧
  (∀ p : ℕ, p.Prime → p ∣ K.1.2.2.2.1 → p ∣ K.1.2.2.1) ∧
  (∀ p : ℕ, p.Prime → p ∣ K.1.2.2.2.2 → p ∣ K.1.2.2.1) ∧
  n₁.Coprime K.1.1 ∧ (r * s).Coprime K.1.2.2.1 ∧
  (K.1.2.1 * n₁).Coprime n₂ ∧
  K.1.2.2.2.1.Coprime (K.1.2.2.2.2 * (r * s))

theorem wKSectionData_valid
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s) (hk : 0 < k)
    (hkδ : k.Coprime K.1.2.2.1)
    (hkr : k.Coprime (K.1.2.2.2.2 * (r * s))) :
    (wKSectionData K r n₁ n₂ s k).Valid
      (K.1.2.2.1 * K.1.2.2.2.1 * k)
      (K.1.2.2.1 * K.1.2.2.2.2 * (r * s))
      (K.1.1 * K.1.2.1 * n₁) (K.1.1 * n₂) := by
  obtain ⟨hd, hd₁, hδ, hδ₁, hδ₂, hr, hs, hn₁, hn₂,
    hds, hδs₁, hδs₂, hnd, hrs, hn, hδr⟩ := hf
  have hkp := hδr.mul_left hkr
  refine ⟨hd, hd₁, hδ, hδ₁, hδ₂, hk, Nat.mul_pos hr hs, hn₁, hn₂,
    rfl, rfl, rfl, rfl, ?_, ?_, hds, hδs₁, hδs₂, hnd, hkδ, hrs, hn, hkp⟩
  · change K.1.1 = _
    rw [mul_assoc, Nat.gcd_mul_left, hn.gcd_eq_one, mul_one]
  · change K.1.2.2.1 = _
    rw [mul_assoc K.1.2.2.1, mul_assoc K.1.2.2.1, Nat.gcd_mul_left,
      hkp.gcd_eq_one, mul_one]

theorem wKSectionTuple_original
    {K : WExtractedKey} (he : K.2 * wKSectionDeltaPrime K =
      K.1.2.2.1 * K.1.2.2.2.2) (r n₁ n₂ s k : ℕ) (h : ℤ) :
    wExtractedOriginal (wKSectionTuple K r n₁ n₂ s h k).1 =
      (wKSectionData K r n₁ n₂ s k).original := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    change (K.2 * r) * (wKSectionDeltaPrime K * s) =
      K.1.2.2.1 * K.1.2.2.2.2 * (r * s)
    calc
      _ = (K.2 * wKSectionDeltaPrime K) * (r * s) := by ring
      _ = _ := by rw [he]
  · rfl

theorem wKSectionTuple_canonical
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s) (hk : 0 < k)
    (hkδ : k.Coprime K.1.2.2.1)
    (hkr : k.Coprime (K.1.2.2.2.2 * (r * s)))
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (h : ℤ) :
    wGCDTuple (wExtractedOriginal (wKSectionTuple K r n₁ n₂ s h k).1) =
      wKSectionData K r n₁ n₂ s k := by
  rw [wKSectionTuple_original he]
  exact (wKSectionData_valid hf hk hkδ hkr).eq_canonical.symm

/-- Actual key-fiber membership gives exact reconstruction, including
the first beta coordinate that does not occur in the analytic five-grid. -/
theorem wExtractedKeyFiber_kSection_reconstruct
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    wKSectionTuple K t.1.1.2.1 (wGCDTuple (wExtractedOriginal t.1)).n₁
      (wGCDTuple (wExtractedOriginal t.1)).n₂ t.1.1.2.2 t.2
      (wGCDTuple (wExtractedOriginal t.1)).k₁ = t := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  obtain ⟨hk, hΔ, _, _, hΔ'⟩ := wExtractedKeyFiber_spec ht
  have hd := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.1) hk
  have hd₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) hk
  have hδ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.1) hk
  have hδ₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.2.1) hk
  have hq := hv.q_eq
  have hn₁ := hv.N₁_eq
  have hn₂ := hv.N₂_eq
  change (wGCDTuple (wExtractedOriginal t.1)).d = K.1.1 at hd
  change (wGCDTuple (wExtractedOriginal t.1)).d₁ = K.1.2.1 at hd₁
  change (wGCDTuple (wExtractedOriginal t.1)).δ = K.1.2.2.1 at hδ
  change (wGCDTuple (wExtractedOriginal t.1)).δ₁ = K.1.2.2.2.1 at hδ₁
  rw [hd, hd₁] at hn₁
  rw [hd] at hn₂
  rw [hδ, hδ₁] at hq
  change t.1.2.1 = _ at hq
  change t.1.2.2.1 = _ at hn₁
  change t.1.2.2.2 = _ at hn₂
  unfold wKSectionTuple
  refine Prod.ext ?_ rfl
  refine Prod.ext ?_ (Prod.ext hq.symm (Prod.ext hn₁.symm hn₂.symm))
  exact Prod.ext (Prod.ext hΔ.symm hΔ'.symm) rfl

/-- Equal fixed section coordinates and equal `k₁` force equality of
original tuples. There is no loss of multiplicity in the subsequent sum. -/
theorem wExtractedKeyFiber_kSection_injective
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t u : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K)
    (hu : u ∈ wExtractedKeyFiber H N Q a P R S ξ b K)
    (hr : t.1.1.2.1 = u.1.1.2.1)
    (hn₁ : (wGCDTuple (wExtractedOriginal t.1)).n₁ =
      (wGCDTuple (wExtractedOriginal u.1)).n₁)
    (hn₂ : (wGCDTuple (wExtractedOriginal t.1)).n₂ =
      (wGCDTuple (wExtractedOriginal u.1)).n₂)
    (hs : t.1.1.2.2 = u.1.1.2.2) (hh : t.2 = u.2)
    (hk : (wGCDTuple (wExtractedOriginal t.1)).k₁ =
      (wGCDTuple (wExtractedOriginal u.1)).k₁) : t = u := by
  rw [← wExtractedKeyFiber_kSection_reconstruct hN hQ ht,
    ← wExtractedKeyFiber_kSection_reconstruct hN hQ hu, hr, hn₁, hn₂, hs, hh, hk]

theorem wExtractedKeyFiber_kSection_data
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    wGCDTuple (wExtractedOriginal t.1) =
      wKSectionData K t.1.1.2.1 (wGCDTuple (wExtractedOriginal t.1)).n₁
        (wGCDTuple (wExtractedOriginal t.1)).n₂ t.1.1.2.2
        (wGCDTuple (wExtractedOriginal t.1)).k₁ := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have he := (wExtractedKeyFiber_spec ht).1
  apply WGCDData.ext
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.1) he
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) he
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.1) he
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.2.1) he
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.2.2) he
  · rfl
  · exact wExtracted_k₂_eq hN hQ hz
  · rfl
  · rfl

/-- The canonical constraints are consequences of real membership.
This converse is needed for equality of carriers, rather than an inclusion. -/
theorem wExtractedKeyFiber_kSection_arithmetic
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    wKSectionFixedCanonical K t.1.1.2.1 v.n₁ v.n₂ t.1.1.2.2 ∧
      0 < v.k₁ ∧ v.k₁.Coprime K.1.2.2.1 ∧
      v.k₁.Coprime (K.1.2.2.2.2 * (t.1.1.2.1 * t.1.1.2.2)) ∧
      0 < K.2 ∧ 0 < wKSectionDeltaPrime K ∧
      K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2 := by
  dsimp only
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hd := wExtractedKeyFiber_kSection_data hN hQ ht
  rw [hd] at hv
  have hmem := mem_wFactorExtractionTuples_iff.mp hz
  have hs := wExtractedKeyFiber_spec ht
  have he := (wExtracted_extraction_spec hz).2.2.1
  rw [hd] at he
  change t.1.1.1.1 * t.1.1.1.2 = K.1.2.2.1 * K.1.2.2.2.2 at he
  rw [hs.2.1, hs.2.2.2.2] at he
  have hp := Nat.coprime_mul_iff_left.mp hv.k_primitive
  have hΔ' : 0 < wKSectionDeltaPrime K := by
    change 0 < K.1.2.2.1 * K.1.2.2.2.2 / K.2
    rw [← hs.2.2.2.2]
    exact hs.2.2.2.1
  exact ⟨⟨hv.d_pos, hv.d₁_pos, hv.δ_pos, hv.δ₁_pos, hv.δ₂_pos,
    (mem_Ioc.mp hmem.2.2.1).1, (mem_Ioc.mp hmem.2.2.2.1).1,
    hv.n₁_pos, hv.n₂_pos, hv.d₁_support, hv.δ₁_support, hv.δ₂_support,
    hv.n₁_d, hv.k₂_δ, hv.n_primitive, hp.1⟩,
    hv.k₁_pos, hv.k₁_δ, hp.2, hs.2.2.1, hΔ', he⟩

/-- Even before assuming the variable coprimalities, actual membership
forces the reconstructed coordinates to be the canonical ones. -/
theorem wKSectionTuple_canonical_of_mem
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ} {h : ℤ}
    (hd : 0 < K.1.1) (hd₁ : 0 < K.1.2.1)
    (hδ : 0 < K.1.2.2.1) (hδ₁ : 0 < K.1.2.2.2.1)
    (ht : wKSectionTuple K r n₁ n₂ s h k ∈
      wExtractedKeyFiber H N Q a P R S ξ b K) :
    wGCDTuple (wExtractedOriginal (wKSectionTuple K r n₁ n₂ s h k).1) =
      wKSectionData K r n₁ n₂ s k := by
  let t := wKSectionTuple K r n₁ n₂ s h k
  have he := wExtractedKeyFiber_kSection_reconstruct hN hQ ht
  have hk := congrArg (fun u : WExtractedTuple × ℤ => u.1.2.1) he
  have hn₁ := congrArg (fun u : WExtractedTuple × ℤ => u.1.2.2.1) he
  have hn₂ := congrArg (fun u : WExtractedTuple × ℤ => u.1.2.2.2) he
  change (K.1.2.2.1 * K.1.2.2.2.1) *
    (wGCDTuple (wExtractedOriginal t.1)).k₁ = (K.1.2.2.1 * K.1.2.2.2.1) * k at hk
  change (K.1.1 * K.1.2.1) * (wGCDTuple (wExtractedOriginal t.1)).n₁ =
    (K.1.1 * K.1.2.1) * n₁ at hn₁
  change K.1.1 * (wGCDTuple (wExtractedOriginal t.1)).n₂ = K.1.1 * n₂ at hn₂
  have hk' := Nat.mul_left_cancel (Nat.mul_pos hδ hδ₁) hk
  have hn₁' := Nat.mul_left_cancel (Nat.mul_pos hd hd₁) hn₁
  have hn₂' := Nat.mul_left_cancel hd hn₂
  calc
    _ = wKSectionData K r (wGCDTuple (wExtractedOriginal t.1)).n₁
      (wGCDTuple (wExtractedOriginal t.1)).n₂ s
      (wGCDTuple (wExtractedOriginal t.1)).k₁ :=
        wExtractedKeyFiber_kSection_data hN hQ ht
    _ = _ := by rw [hk', hn₁', hn₂']

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
