import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveMultiplicity

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset

/-- The original closed small-output sum, with its unchanged convolution coefficient. -/
noncomputable def closedSmall {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) (Z : ℝ) : ℝ :=
  ∑ x ∈ actualProfiles N δ p W j, (convolutionCoeff W x.1 : ℝ) *
    ((actualFibre N δ p j x).filter (fun q => ((N-gamma16Cofactor x*q : ℕ) : ℝ) ≤ Z)).card

/-- Output primality supplies the lower endpoint; all closed upper atoms are retained. -/
theorem small_card_disintegration (N Z : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) (j : Fin 4)
    (x : Gamma16Profile) :
    (∑ ell ∈ Icc 1 Z, ((actualFibre N δ p j x).filter
      (fun q => N-gamma16Cofactor x*q = ell)).card) =
      ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q ≤ Z)).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext q
  simp only [mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · intro h
    have hp : (N-gamma16Cofactor x*q).Prime := (mem_filter.mp h.1).2.2.2.2.2.2
    exact ⟨h.1,hp.pos,h.2⟩

/-- Exact real/floor disintegration of the actual weighted carrier. -/
theorem closedSmall_disintegration {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) {Z : ℝ} (hZ : 0 ≤ Z) :
    closedSmall N δ p W j Z =
      ∑ ell ∈ Icc 1 ⌊Z⌋₊, ∑ x ∈ actualProfiles N δ p W j,
        (convolutionCoeff W x.1 : ℝ) *
          ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card := by
  rw [sum_comm]
  unfold closedSmall
  apply sum_congr rfl
  intro x _
  rw [← mul_sum, ← Nat.cast_sum, small_card_disintegration]
  simp only [Nat.le_floor_iff hZ]

/-- Finite output grouping pays the number of integer outputs once, not per profile. -/
theorem closedSmall_le_of_output_bound {i N : ℕ} {δ C Z : ℝ}
    (p : SecondFunctionalParameters) (W : Fin i → Finset ℕ) (j : Fin 4)
    (hZ : 0 ≤ Z) (hC : 0 ≤ C)
    (h : ∀ ell, (∑ x ∈ actualProfiles N δ p W j, (convolutionCoeff W x.1 : ℝ) *
      ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤ C) :
    closedSmall N δ p W j Z ≤ C*Z := by
  rw [closedSmall_disintegration N δ p W j hZ]
  calc
    _ ≤ ∑ _ell ∈ Icc 1 ⌊Z⌋₊, C := sum_le_sum (fun ell _ => h ell)
    _ = C*(⌊Z⌋₊ : ℝ) := by simp [mul_comm]
    _ ≤ C*Z := mul_le_mul_of_nonneg_left (Nat.floor_le hZ) hC


theorem source_layer_le_actual {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (e : ℕ) :
    (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre e,
      (sourceFamily N δ Δ V p j).weight x) ≤
    ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
      (fun x => gamma16Cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1,he⟩
  · intro x _ _
    exact Nat.cast_nonneg _

theorem source_layer_card_le_weight {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (e : ℕ) :
    (((sourceFamily N δ Δ V p j).layerFibre e).card : ℝ) ≤
    ∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre e,
      (sourceFamily N δ Δ V p j).weight x := by
  calc
    _ = ∑ _x ∈ (sourceFamily N δ Δ V p j).layerFibre e, (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun x hx => by
      have hp : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
        (mem_filter.mp (mem_filter.mp hx).1).1
      have hd := (profile_data hp).1
      change (1 : ℝ) ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)
      exact_mod_cast (show 1 ≤ convolutionCoeff (convolutionWuWindows N Δ V) x.1 from
        mem_boxConvolutionSupport.mp hd)

/-- The physical Small uses a strict cutoff; this bridge retains the closed boundary. -/
theorem source_small_le_closed {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) (Z : ℝ) :
    (sourceFamily N δ Δ V p j).small Z ≤
      closedSmall N δ p (convolutionWuWindows N Δ V) j Z := by
  let L := sourceFamily N δ Δ V p j
  have hsub : L.labels ⊆ actualProfiles N δ p (convolutionWuWindows N Δ V) j :=
    filter_subset _ _
  calc
    _ ≤ ∑ x ∈ L.labels, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => ((N-gamma16Cofactor x*q : ℕ) : ℝ) ≤ Z)).card := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Nat.cast_le.mpr
      apply card_le_card
      intro q hq
      obtain ⟨hq,hprime,hlt⟩ := mem_filter.mp hq
      have hd : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 < d :=
        fun _ hd => boxConvolutionSupport_pos
          (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
      have he := (actualFamily_fibres p (convolutionWuWindows N Δ V) j hd (hsub hx)).2
      have hmem : q ∈ ((actualFamily N δ p (convolutionWuWindows N Δ V) j hd).primes x).filter
          (fun q => (N-gamma16Cofactor x*q).Prime) := mem_filter.mpr ⟨hq,hprime⟩
      rw [he] at hmem
      exact mem_filter.mpr ⟨hmem,hlt.le⟩
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- One threshold, chosen before every box, mother parameter, word and real cutoff. -/
theorem source_all_multiplicities (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let W := convolutionWuWindows N Δ V
      let H := max 1 (1/(wuLocalExponent k δ / 10))
      (∀ j : Fin 4,
        (∀ e, (∑ x ∈ (actualProfiles N δ p W j).filter (fun x => gamma16Cofactor x = e),
          (convolutionCoeff W x.1 : ℝ)) ≤ H^(k+3)) ∧
        (∀ ell, (∑ x ∈ actualProfiles N δ p W j, (convolutionCoeff W x.1 : ℝ) *
          ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤ H^(k+4)) ∧
        (∀ e, (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre e,
          (sourceFamily N δ Δ V p j).weight x) ≤ H^(k+3)) ∧
        (∀ e, (((sourceFamily N δ Δ V p j).layerFibre e).card : ℝ) ≤ H^(k+3)) ∧
        (∀ Z : ℝ, 0 ≤ Z → closedSmall N δ p W j Z ≤ H^(k+4)*Z) ∧
        (∀ Z : ℝ, 0 ≤ Z → (sourceFamily N δ Δ V p j).small Z ≤ H^(k+4)*Z)) ∧
      (∀ Z : ℝ, 0 ≤ Z → (∑ j : Fin 4, closedSmall N δ p W j Z) ≤ 4*H^(k+4)*Z) ∧
      (∀ Z : ℝ, 0 ≤ Z → (∑ j : Fin 4, (sourceFamily N δ Δ V p j).small Z) ≤ 4*H^(k+4)*Z) := by
  obtain ⟨T,hT,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  let W := convolutionWuWindows N Δ V
  let H := max 1 (1/(wuLocalExponent k δ / 10))
  have hf (j : Fin 4) := hm N hN i Δ V hb p hp j
  have hl (j : Fin 4) (e : ℕ) :
      (∑ x ∈ (sourceFamily N δ Δ V p j).layerFibre e,
        (sourceFamily N δ Δ V p j).weight x) ≤ H^(k+3) :=
    (source_layer_le_actual N δ Δ V p j e).trans ((hf j).1 e)
  have hc (j : Fin 4) (Z : ℝ) (hZ : 0 ≤ Z) :
      closedSmall N δ p W j Z ≤ H^(k+4)*Z :=
    closedSmall_le_of_output_bound p W j hZ (by dsimp [H]; positivity) (hf j).2
  have hs (j : Fin 4) (Z : ℝ) (hZ : 0 ≤ Z) :
      (sourceFamily N δ Δ V p j).small Z ≤ H^(k+4)*Z :=
    (source_small_le_closed N δ Δ V p j Z).trans (hc j Z hZ)
  refine ⟨fun j => ⟨(hf j).1,(hf j).2,hl j,
    fun e => (source_layer_card_le_weight N δ Δ V p j e).trans (hl j e), hc j, hs j⟩, ?_, ?_⟩
  · intro Z hZ
    calc
      _ ≤ ∑ _j : Fin 4, H^(k+4)*Z := sum_le_sum (fun j _ => hc j Z hZ)
      _ = _ := by simp [H]; ring
  · intro Z hZ
    calc
      _ ≤ ∑ _j : Fin 4, H^(k+4)*Z := sum_le_sum (fun j _ => hs j Z hZ)
      _ = _ := by simp [H]; ring

end Wu2008DoubleSieve.FourPrimeNonunit
