import U8PhysicalCompatible
import OriginalSieve

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace U8Literal.Join

theorem longLabels_eq (N : ℕ) (ρ : ℝ) (k : Key) :
    longLabels N ρ k = OriginalU8.labels N ρ k := by
  ext z
  obtain ⟨p,r⟩ := z
  rw [OriginalU8.labels_mem]
  simp only [longLabels, mem_filter, mem_product, mem_range, Nat.lt_succ_iff]
  tauto

theorem longProducts_eq (N : ℕ) (ρ : ℝ) (k : Key) :
    longProducts N ρ k = OriginalU8.products (OriginalU8.labels N ρ k) := by
  unfold longProducts OriginalU8.products
  rw [longLabels_eq]

theorem longAlpha_eq (N : ℕ) (ρ : ℝ) (k : Key) (m : ℕ) :
    longAlpha N ρ k m = OriginalU8.alpha (OriginalU8.labels N ρ k) m := by
  unfold longAlpha OriginalU8.alpha
  rw [longLabels_eq]

theorem wholeInterval_eq (N : ℕ) (ρ : ℝ) (k : Key) :
    shortPrimeSupport N ρ k = OriginalU8.primeSupport N ρ k := rfl

theorem beta_eq (N n : ℕ) : rectangleBeta N n = OriginalU8.beta N n := rfl

theorem sifted_eq (N : ℕ) (ρ : ℝ) (k : Key) (P : Finset ℕ) :
    rectangleSifted N ρ k P = OriginalU8.sifted N ρ k P := by
  unfold rectangleSifted OriginalU8.sifted
  simp only [longProducts_eq, wholeInterval_eq, longAlpha_eq, beta_eq]
  rfl

/-- The witness is from the original physical prefix, before sifting any output. -/
theorem occupied_to_original {N : ℕ} (hN : 1 ≤ N) {e ρ : ℝ} (hρ : 1 < ρ)
    {k : Key} (hk : k ∈ occupied N e ρ) : OriginalU8.Occupied N e ρ k := by
  obtain ⟨x,hx,hkey⟩ := mem_image.mp hk
  have hs := (mem_filter.mp hx).1
  have he := (mem_filter.mp hx).2
  have hc : x ∈ cell N e ρ k := mem_filter.mpr ⟨hx,hkey⟩
  obtain ⟨hn,hl⟩ := cell_rectangle hN hρ hc
  have hd := physicalSmall_data hs
  have hb := (mem_shortPrimeSupport hN hρ k _).mp hn
  refine ⟨x.1.1,(x.1.2,x.2),?_,hd.1,hd.2.2.2.1,?_,?_,?_,?_⟩
  · rwa [← longLabels_eq]
  · exact max_le hb.1 hb.2.1
  · exact lt_min hb.2.2.1 hb.2.2.2
  · simpa only [Nat.cast_mul,mul_assoc] using he
  · have hp := hd.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact_mod_cast (show x.1.1*(x.1.2*x.2) < N by simpa only [Nat.mul_assoc] using hp)

/-- One common cutoff and the actual external centers, with every loss retained.
The original physicalSmall is not renamed, quotiented, or supplied as a premise. -/
theorem physicalSmall_external (A : ℕ) {e ε δ η : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      ((physicalSmall N).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ,
          ∑ t ∈ externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            ∑ d ∈ (P.prod id).divisors,
              externalTerm true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d *
                OriginalU8.center N ρ k d) +
        (∑ k ∈ occupied N e ρ,
          ((externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z).card : ℝ) *
            ((4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)) /
              Real.log (4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1))^A)) -
        (∑ k ∈ occupied N e ρ,
          ∑ t ∈ externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            OriginalU8.exceptional N ρ δ k P η z t) +
        (outputBad N e P).card + (smallPrefix N e).card := by
  obtain ⟨N₁,hS⟩ := OriginalU8.sieve_fixed_eta A he he1 hε hεa hεδ hδ hη hηu
  refine ⟨max N₁ 1,?_⟩
  intro N hN ρ hρ hρu P hP hPN z hcut
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_right N₁ 1).trans hN
  have hs := physicalSmall_le_rectangles_add_losses hN1 e hρ P
  have hb := sum_le_sum (s := occupied N e ρ) (fun k hk =>
    hS N ((le_max_left N₁ 1).trans hN) ρ hρ hρu k
      (occupied_to_original hN1 hρ hk) P hP hPN z hcut)
  simp only [← sifted_eq, sum_sub_distrib, sum_add_distrib] at hb
  exact hs.trans (add_le_add (add_le_add hb le_rfl) le_rfl)

open scoped Classical in
/-- The same result with the literal original physicalT8 filter displayed in its type. -/
theorem physicalT8_small_external (A : ℕ) {e ε δ η : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      (((Wu2008DoubleSieve.SeventhEighth.physicalT8 N).filter
        (fun x => (x.1.1 : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ,
          ∑ t ∈ externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            ∑ d ∈ (P.prod id).divisors,
              externalTerm true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d *
                OriginalU8.center N ρ k d) +
        (∑ k ∈ occupied N e ρ,
          ((externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z).card : ℝ) *
            ((4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)) /
              Real.log (4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1))^A)) -
        (∑ k ∈ occupied N e ρ,
          ∑ t ∈ externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            OriginalU8.exceptional N ρ δ k P η z t) +
        (outputBad N e P).card + (smallPrefix N e).card := by
  simpa only [physicalSmall] using
    physicalSmall_external A he he1 hε hεa hεδ hδ hη hηu

end U8Literal.Join
