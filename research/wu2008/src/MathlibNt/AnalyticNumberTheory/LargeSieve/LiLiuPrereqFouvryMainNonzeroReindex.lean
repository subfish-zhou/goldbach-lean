import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainNonzero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceReindex

/-!
# Main nonzero occupied labels, with the common index and r varying

Only the two ordered inner triples are fixed. The original beta/zeta weight
is independent of both averaged coordinates; the shared k multiplicity
remains in the already constructed Gram section.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WGramMainBase := (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℤ)

def wGramMainJoin (v : WGramMainBase) (p : ℕ × ℕ) : WGramLabel :=
  ((p.2, p.1), v)

theorem wGramMainJoin_base (L : WGramLabel) :
    wGramMainJoin L.2 (L.1.2, L.1.1) = L := rfl

def wGramMainLabels (K : WExtractedKey) (a : ℤ)
    (V : Finset (WExtractedTuple × ℤ)) : Finset WGramLabel :=
  (wGramLabels V).filter
    (fun L => wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L)

def wGramMainBases (G : Finset WGramLabel) : Finset WGramMainBase :=
  G.image Prod.snd

def wGramMainFiber (G : Finset WGramLabel) (v : WGramMainBase) : Finset (ℕ × ℕ) :=
  (G.filter (fun L => L.2 = v)).image (fun L => (L.1.2, L.1.1))

theorem mem_wGramMainFiber {G : Finset WGramLabel}
    {v : WGramMainBase} {p : ℕ × ℕ} :
    p ∈ wGramMainFiber G v ↔ wGramMainJoin v p ∈ G := by
  constructor
  · intro hp
    obtain ⟨L, hL, rfl⟩ := mem_image.mp hp
    obtain ⟨hL, hv⟩ := mem_filter.mp hL
    rw [← hv, wGramMainJoin_base]
    exact hL
  · intro hp
    exact mem_image.mpr ⟨wGramMainJoin v p, mem_filter.mpr ⟨hp, rfl⟩, rfl⟩

theorem sum_wGramMainFiber {A : Type*} [AddCommMonoid A]
    (G : Finset WGramLabel) (F : WGramLabel → A) :
    ∑ L ∈ G, F L =
      ∑ v ∈ wGramMainBases G,
        ∑ p ∈ wGramMainFiber G v, F (wGramMainJoin v p) := by
  rw [show (∑ L ∈ G, F L) =
      ∑ v ∈ wGramMainBases G, ∑ L ∈ G.filter (fun L => L.2 = v), F L from
    (sum_fiberwise_of_maps_to
      (fun L hL => mem_image.mpr ⟨L, hL, rfl⟩) F).symm]
  apply sum_congr rfl
  intro v _
  rw [wGramMainFiber, sum_image]
  · apply sum_congr rfl
    intro L hL
    rw [← (mem_filter.mp hL).2, wGramMainJoin_base]
  · intro L hL L' hL' he
    have hv := (mem_filter.mp hL).2.trans (mem_filter.mp hL').2.symm
    change (L.1.2, L.1.1) = (L'.1.2, L'.1.1) at he
    rw [← wGramMainJoin_base L, ← wGramMainJoin_base L', hv, he]

theorem wGramMainJoin_weight (K : WExtractedKey) (β ζ : ℕ → ℝ)
    (v : WGramMainBase) (p : ℕ × ℕ) :
    wGramWeight K β ζ (wGramMainJoin v p) =
      (ζ (wKSectionDeltaPrime K * v.1.2.1) * β (K.1.1 * v.1.1)) *
        (ζ (wKSectionDeltaPrime K * v.2.2.1) * β (K.1.1 * v.2.1)) := rfl


theorem wGramLabels_n_mem_dyadic
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {L : WGramLabel}
    (hL : L ∈ wGramLabels (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) :
    L.1.2 ∈ Ioc (2 ^ j 2 - 1) (2 ^ (j 2 + 1) - 1) := by
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  have ht := (mem_product.mp (mem_filter.mp hp).1).1
  have hb := (mem_filter.mp (mem_filter.mp ht).1).1
  have he := congrFun (mem_filter.mp hb).2.1 2
  have hpos := wAnalyticCoordinates_pos hN (fun _ hq => (mem_Ioc.mp hq).1)
    (mem_filter.mp hb).1 2
  have hdy := (Nat.log_eq_iff (Or.inr ⟨by decide, hpos.ne'⟩)).mp he
  change 2 ^ j 2 ≤ (wGCDTuple (wExtractedOriginal t.1)).n₁ ∧
    (wGCDTuple (wExtractedOriginal t.1)).n₁ < 2 ^ (j 2 + 1) at hdy
  change (wGCDTuple (wExtractedOriginal t.1)).n₁ ∈
    Ioc (2 ^ j 2 - 1) (2 ^ (j 2 + 1) - 1)
  have hpow : 0 < 2 ^ j 2 := by positivity
  exact mem_Ioc.mpr (by omega)

def wGramMainBox (K : WExtractedKey) (a : ℤ) (j : Fin 5 → ℕ)
    (v : WGramMainBase) : Finset (ℕ × ℕ) :=
  ((Ioc (2 ^ j 2 - 1) (2 ^ (j 2 + 1) - 1)).filter
    (fun n => iv3CorrelationNumerator K.1.2.1 n v.1.1 v.2.1 v.1.2.1 v.2.2.1
      a v.1.2.2 v.2.2.2 ≠ 0)) ×ˢ Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1)



end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
