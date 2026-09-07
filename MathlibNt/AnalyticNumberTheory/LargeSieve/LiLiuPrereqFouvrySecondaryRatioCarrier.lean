import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryRatioBox

/-!
# The logarithmic ratio count on the actual secondary carrier

The code retains the common first beta coordinate, both second beta indices,
both sieve coordinates, and both signed frequencies. Only the known fixed
sign is removed. Thus ordered multiplicities are not lost.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem frequency_bounds {i : ℕ} {positive : Bool} {h : ℤ}
    (hh : h ∈ wGramResonanceScaleFrequencies i positive) :
    h.natAbs ∈ Ioc 0 (2 ^ (i + 1)) := by
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
  have hp : 0 < 2 ^ i := by positivity
  have hn' : n ∈ Ioc 0 (2 ^ (i + 1)) :=
    mem_Ioc.mpr ⟨hp.trans_le (mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩
  cases positive <;> simpa using hn'

theorem wGramSecondaryRatioCode_mem_box
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {v : WGramSecondaryBase}
    (hv : v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))) :
    wGramSecondaryRatioCode v ∈ wGramSecondaryRatioBox K F j := by
  obtain ⟨hn, hm, hm', hs, hs', hh, hh', he⟩ :=
    wGramSecondaryBases_scale_data hN hNF hR hS hM hZ hv
  have heabs := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at heabs
  refine mem_product.mpr ⟨mem_product.mpr ⟨hn, mem_product.mpr ⟨hm, hm'⟩⟩, ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨frequency_bounds hh, ?_⟩,
    mem_product.mpr ⟨frequency_bounds hh', ?_⟩⟩, heabs⟩
  · simpa only [wGramSecondaryRatioCode, wGramResonanceScaleInterval,
      pow_succ, Nat.mul_comm] using hs
  · have hp : 0 < 2 ^ j 4 := by positivity
    apply mem_Ioc.mpr
    exact ⟨hp.trans_le (mem_Ico.mp hs').1,
      (mem_Ico.mp hs').2.le.trans_eq (by rw [pow_succ, Nat.mul_comm])⟩

theorem wGramSecondaryRatioCode_injective
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    Set.InjOn wGramSecondaryRatioCode
      (wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c))) := by
  intro v hv w hw he
  have hvd := wGramSecondaryBases_scale_data hN hNF hR hS hM hZ hv
  have hwd := wGramSecondaryBases_scale_data hN hNF hR hS hM hZ hw
  have hh := secondary_frequency_natAbs_injective (j 0) positive
    hvd.2.2.2.2.2.1 hwd.2.2.2.2.2.1 (congrArg (fun q => q.2.1.1) he)
  have hh' := secondary_frequency_natAbs_injective (j 0) positive
    hvd.2.2.2.2.2.2.1 hwd.2.2.2.2.2.2.1 (congrArg (fun q => q.2.2.1) he)
  apply Prod.ext
  · exact congrArg (fun q => q.1.1) he
  · apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun q => q.1.2.1) he
      · apply Prod.ext
        · exact congrArg (fun q => q.2.1.2) he
        · exact hh
    · apply Prod.ext
      · exact congrArg (fun q => q.1.2.2) he
      · apply Prod.ext
        · exact congrArg (fun q => q.2.2.2) he
        · exact hh'

/-- Every fixed-data base in the existing r-mean is counted. The final
factor is `O(H*S*log H)`, rather than the independent `H²*S²` box. -/
theorem wGramSecondaryBases_card_le_ratio
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    ((wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))).card : ℝ) ≤
      (2 ^ j 2 : ℕ) * (F / K.1.1 : ℕ) ^ 2 *
        (4 * (2 ^ (j 0 + 1) : ℕ) * (2 ^ j 4 : ℕ) *
          (1 + Real.log (2 ^ (j 0 + 1) : ℕ))) := by
  apply le_trans _ (wGramSecondaryRatioBox_card_le K F j)
  exact_mod_cast card_le_card_of_injOn wGramSecondaryRatioCode
    (fun _ hv => wGramSecondaryRatioCode_mem_box hN hNF hR hS hM hZ hv)
    (wGramSecondaryRatioCode_injective hN hNF hR hS hM hZ K b j cap positive c)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
