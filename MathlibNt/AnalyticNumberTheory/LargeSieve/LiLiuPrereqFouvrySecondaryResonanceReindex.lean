import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonance
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceDomain

/-!
# Actual secondary labels, with only the common r varying

The base retains `(n,n₂,s,h,n₂',s',h')`. Reindexing is exact on occupied
ordered labels; in particular neither beta index nor frequency is identified.
The signed coefficient weight is independent of the fiber coordinate `r`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WGramSecondaryBase := ℕ × (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℤ)

def wGramSecondaryBase (L : WGramLabel) : WGramSecondaryBase :=
  (L.1.2, L.2)

def wGramSecondaryJoin (v : WGramSecondaryBase) (r : ℕ) : WGramLabel :=
  ((r, v.1), v.2)

theorem wGramSecondaryJoin_base (L : WGramLabel) :
    wGramSecondaryJoin (wGramSecondaryBase L) L.1.1 = L := rfl

def wGramSecondaryLabels (K : WExtractedKey) (a : ℤ)
    (V : Finset (WExtractedTuple × ℤ)) : Finset WGramLabel :=
  (wGramLabels V).filter (fun L => wGramNumerator K a L ≠ 0 ∧ wGramSecondaryResonant L)

def wGramSecondaryBases (G : Finset WGramLabel) : Finset WGramSecondaryBase :=
  G.image wGramSecondaryBase

def wGramSecondaryFiber (G : Finset WGramLabel) (v : WGramSecondaryBase) : Finset ℕ :=
  (G.filter (fun L => wGramSecondaryBase L = v)).image (fun L => L.1.1)

theorem mem_wGramSecondaryFiber {G : Finset WGramLabel}
    {v : WGramSecondaryBase} {r : ℕ} :
    r ∈ wGramSecondaryFiber G v ↔ wGramSecondaryJoin v r ∈ G := by
  constructor
  · intro hr
    obtain ⟨L, hL, rfl⟩ := mem_image.mp hr
    obtain ⟨hL, hv⟩ := mem_filter.mp hL
    rw [← hv, wGramSecondaryJoin_base]
    exact hL
  · intro hr
    exact mem_image.mpr ⟨wGramSecondaryJoin v r, mem_filter.mpr ⟨hr, rfl⟩, rfl⟩

theorem sum_wGramSecondaryFiber {A : Type*} [AddCommMonoid A]
    (G : Finset WGramLabel) (F : WGramLabel → A) :
    ∑ L ∈ G, F L =
      ∑ v ∈ wGramSecondaryBases G,
        ∑ r ∈ wGramSecondaryFiber G v, F (wGramSecondaryJoin v r) := by
  rw [show (∑ L ∈ G, F L) =
      ∑ v ∈ wGramSecondaryBases G,
        ∑ L ∈ G.filter (fun L => wGramSecondaryBase L = v), F L from
    (sum_fiberwise_of_maps_to
      (fun L hL => mem_image.mpr ⟨L, hL, rfl⟩) F).symm]
  apply sum_congr rfl
  intro v _
  rw [wGramSecondaryFiber, sum_image]
  · apply sum_congr rfl
    intro L hL
    rw [← (mem_filter.mp hL).2, wGramSecondaryJoin_base]
  · intro L hL L' hL' he
    have hv := (mem_filter.mp hL).2.trans (mem_filter.mp hL').2.symm
    change L.1.1 = L'.1.1 at he
    rw [← wGramSecondaryJoin_base L, ← wGramSecondaryJoin_base L', hv, he]

theorem wGramSecondaryJoin_weight (K : WExtractedKey) (β ζ : ℕ → ℝ)
    (v : WGramSecondaryBase) (r : ℕ) :
    wGramWeight K β ζ (wGramSecondaryJoin v r) =
      (ζ (wKSectionDeltaPrime K * v.2.1.2.1) * β (K.1.1 * v.2.1.1)) *
        (ζ (wKSectionDeltaPrime K * v.2.2.2.1) * β (K.1.1 * v.2.2.1)) := rfl

theorem sum_wGramSecondaryFiber_weight (G : Finset WGramLabel)
    (K : WExtractedKey) (β ζ : ℕ → ℝ) (F : WGramLabel → ℝ) :
    ∑ L ∈ G, |wGramWeight K β ζ L| * F L =
      ∑ v ∈ wGramSecondaryBases G,
        |wGramWeight K β ζ (wGramSecondaryJoin v 0)| *
          ∑ r ∈ wGramSecondaryFiber G v, F (wGramSecondaryJoin v r) := by
  rw [sum_wGramSecondaryFiber]
  apply sum_congr rfl
  intro v _
  simp only [wGramSecondaryJoin_weight, mul_sum]

/-- The interval follows from the actual dyadic block, not from an assumed
support bound on arbitrary labels. Both endpoints are natural numbers. -/
theorem wGramLabels_r_mem_dyadic
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {L : WGramLabel}
    (hL : L ∈ wGramLabels (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) :
    L.1.1 ∈ Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1) := by
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  have ht := (mem_product.mp (mem_filter.mp hp).1).1
  have hb := (mem_filter.mp (mem_filter.mp ht).1).1
  have he := congrFun (mem_filter.mp hb).2.1 3
  have hpos := wAnalyticCoordinates_pos hN (fun _ hq => (mem_Ioc.mp hq).1)
    (mem_filter.mp hb).1 3
  have hdy := (Nat.log_eq_iff (Or.inr ⟨by decide, hpos.ne'⟩)).mp he
  change 2 ^ j 3 ≤ t.1.1.2.1 ∧ t.1.1.2.1 < 2 ^ (j 3 + 1) at hdy
  change t.1.1.2.1 ∈ Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1)
  have hpow : 0 < 2 ^ j 3 := by positivity
  exact mem_Ioc.mpr (by omega)

theorem wGramSecondaryFiber_subset_dyadic
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    (v : WGramSecondaryBase) :
    wGramSecondaryFiber (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) v ⊆
        Ioc (2 ^ j 3 - 1) (2 ^ (j 3 + 1) - 1) := by
  intro r hr
  exact wGramLabels_r_mem_dyadic hN (mem_filter.mp (mem_wGramSecondaryFiber.mp hr)).1

/-- Only occupied bases are tested. Positivity and the nonzero correlation
numerator are recovered from a label witness, so empty fibers need no inputs. -/
theorem wGramSecondaryBases_data
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {v : WGramSecondaryBase}
    (hv : v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))) :
    0 < v.1 ∧ 0 < v.2.1.2.1 ∧ 0 < v.2.2.2.1 ∧
      v.2.2.2.2 * v.2.1.2.1 = v.2.1.2.2 * v.2.2.2.1 ∧
      iv3CorrelationNumerator K.1.2.1 v.1 v.2.1.1 v.2.2.1
        v.2.1.2.1 v.2.2.2.1 a v.2.1.2.2 v.2.2.2.2 ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
  obtain ⟨hL, hl, hsec⟩ := mem_filter.mp hL
  obtain ⟨hf, hf', _⟩ := wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1)
    (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c) hL
  have hcoords {r n m s : ℕ} (h : wKSectionFixedCanonical K r n m s) :
      0 < n ∧ 0 < s := by
    obtain ⟨_, _, _, _, _, _, hs, hn, _⟩ := h
    exact ⟨hn, hs⟩
  exact ⟨(hcoords hf).1, (hcoords hf).2, (hcoords hf').2, hsec, hl⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
