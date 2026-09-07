import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFRemainder

noncomputable section
open Classical Finset G12RectangleWF
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12FlexibleWF

/-- The finite pushforward uses the physical weights and inherits the B10 density. -/
def sieve (N : ℕ) (hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ) : BoundingSieve :=
  { goldbachB10BoundingSieve N hEven 0 0 0 Z (mass N A) with
    support := A.image (fun p => N-p.2*p.1)
    weights := fun n => ∑ p ∈ A.filter (fun p => N-p.2*p.1=n),
      goldbachG12NormalizedCoefficient N p.1
    weights_nonneg := fun _ => sum_nonneg
      (fun p _ => (goldbachG12NormalizedCoefficient_bounds N p.1).1) }

theorem sieve_totalMass (N : ℕ) (hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ) :
    (sieve N hEven A Z).totalMass = mass N A := rfl

theorem sieve_test (N : ℕ) (hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ (sieve N hEven A Z).support.filter P, (sieve N hEven A Z).weights n) =
      ∑ p ∈ A, if P (N-p.2*p.1) then goldbachG12NormalizedCoefficient N p.1 else 0 := by
  let out := fun p : ℕ × ℕ => N-p.2*p.1
  let U := (A.image out).filter P
  have hf := sum_fiberwise_eq_sum_filter A U out
    (fun p => goldbachG12NormalizedCoefficient N p.1)
  have he : A.filter (fun p => out p ∈ U) = A.filter (fun p => P (out p)) := by
    ext p
    simp only [mem_filter]
    exact ⟨fun hp => ⟨hp.1,(mem_filter.mp hp.2).2⟩,
      fun hp => ⟨hp.1,mem_filter.mpr ⟨mem_image.mpr ⟨p,hp.1,rfl⟩,hp.2⟩⟩⟩
  rw [he] at hf
  simpa only [sieve, U, out, sum_filter] using hf

theorem sieve_rem (N : ℕ) (hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (sieve N hEven A Z).rem d = residue N A d := by
  have hm : (sieve N hEven A Z).multSum d =
      ∑ p ∈ A, if d ∣ N-p.2*p.1 then goldbachG12NormalizedCoefficient N p.1 else 0 := by
    unfold BoundingSieve.multSum
    rw [← sum_filter]
    exact sieve_test N hEven A Z (fun n => d ∣ n)
  unfold BoundingSieve.rem
  rw [hm, sieve_totalMass]
  have hnu : (sieve N hEven A Z).nu d = (1 : ℝ)/d.totient :=
    goldbachB10BoundingSieve_nu_eq_inv_totient (ε := 0) (b := 0) (c := 0)
      (X := mass N A) hEven hd
  rw [hnu]
  unfold residue
  ring

/-- Any genuine global subfamily inherits the established small-output bound. -/
theorem smallOutput_le (N : ℕ) (hN : 2 ≤ N) (ε Z : ℝ) (A : Finset (ℕ × ℕ))
    (hA : A.image linkedEmbed ⊆ goldbachG12LinkedAtoms N ε) :
    smallOutput N A Z ≤ 8000*(Nat.ceil Z : ℝ) := by
  have hm : (∑ p ∈ A,
      if N-p.2*p.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N p.1 else 0) ≤
      goldbachG12LinkedSmallOutputMass N ε Z := by
    rw [linked_small_test]
    calc
      _ = ∑ x ∈ A.image linkedEmbed,
          if N-x.2*x.1 < Nat.ceil Z then goldbachG12NormalizedCoefficient N x.1 else 0 := by
        rw [sum_image]
        · rfl
        · exact fun _ _ _ _ h => linkedEmbed_injective h
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hA
        (fun x _ _ => by split_ifs; exact (goldbachG12NormalizedCoefficient_bounds N x.1).1; positivity)
  have he := labels_test N A (fun p => if N-p.2*p.1 < Nat.ceil Z then 1 else 0)
  change smallOutput N A Z = _ at he
  rw [he]
  simp only [mul_ite, mul_one, mul_zero]
  have hb := goldbachG12LinkedSmallOutputMass_le hN ε Z
  linarith

/-- The actual upper endpoint V, not 2T, supplies subtraction safety. -/
theorem rectangle_safe (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (p : ℕ × ℕ) (hp : p ∈ G12FlexibleRectangle.rectangle N ε M U T V) :
    p.2*p.1 < N := by
  obtain ⟨hm,hr⟩ := mem_product.mp hp
  have hn := (mem_filter.mp hm).2.2.2.2
  have hrV := (mem_Ioc.mp (mem_filter.mp hr).1).2
  exact (Nat.mul_le_mul_right p.1 hrV).trans_lt hn

theorem rectangle_image_subset (N : ℕ) (ε : ℝ) (M U T V : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (V : ℝ) < (N : ℝ)^(1/10 : ℝ)) :
    (G12FlexibleRectangle.rectangle N ε M U T V).image linkedEmbed ⊆
      goldbachG12LinkedAtoms N ε := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
  have hm := G12FlexibleRectangle.rectangle_subset_mother N ε M U T V hlow hhigh hp
  have hd := (G12LowRectangle.mother_linked_iff N p.1 p.2 ε).mp hm
  exact mem_sigma.mpr ⟨hd.1,hd.2.1⟩

/-- Arbitrarily thin actual rectangles consume the same external family on the
full original modulus interval. Both signed transport corrections are retained. -/
theorem exists_rectangle_full_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ (N : ℕ) (_hN : 2 ≤ N) (_hEven : Even N) (ε Z : ℝ) (M U T V : ℕ),
          (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
          2 ≤ Z → Z ≤ Real.sqrt Q →
          let A := G12FlexibleRectangle.rectangle N ε M U T V
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let Euler := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C * (η + (η^8)⁻¹ * Real.exp (6*K+2) * Real.log Q^(-(1/3 : ℝ)))
          (∀ t ∈ externalTags true P D η Z,
            WellFactorable (externalTerm true P D η Z t) Q ∧
            SignedWellFactorable 1 Q (fun d => externalTerm true P D η Z t d)) ∧
          (400 * ∑ p ∈ A,
            goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0)) ≤
            400 * mass N A * Euler * (jr1965F (Real.log Q / Real.log Z) + E) +
            400 * (∑ t ∈ externalTags true P D η Z,
              let c := externalTerm true P D η Z t
              G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊) c -
                G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) c -
                outsidePrimorial N A Z Q c) + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,h⟩ := exists_atom_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,h⟩ := h η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ N hN hEven ε Z M U T V hlow hhigh hZ hZQ
  obtain ⟨hf,hu⟩ := h Q hQ N hEven (G12FlexibleRectangle.rectangle N ε M U T V) Z hZ hZQ
  dsimp only at hf hu ⊢
  refine ⟨fun t ht => ⟨hf t ht, wellFactorable_to_signed (hf t ht)⟩,?_⟩
  rw [primeCount_eq_original,
    external_remainder_decomposition N hEven _ Z Q η
      (fun p hp => (rectangle_safe N ε M U T V p hp).le) hf] at hu
  exact hu.trans (add_le_add_right (smallOutput_le N hN ε Z _
    (rectangle_image_subset N ε M U T V hlow hhigh)) _)

/-- Each actual external member is passed unchanged to the flexible C2 producer. -/
theorem family_C2_bound (A : ℕ) {Cscale ζ : ℝ}
    (hCscale : 1 ≤ Cscale) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ M U T V : ℕ,
      1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
      ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
      (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ ε η Z : ℝ, ∀ t : List ℕ,
      let Q := x^((5-5*ν)/9-ζ)
      let c := externalTerm true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z t
      WellFactorable c Q →
        |G12FlexibleRectangle.discrepancy N (G12FlexibleRectangle.rectangle N ε M U T V)
          (Ioc 0 ⌊Q⌋₊) c| ≤ x/Real.log x^A := by
  filter_upwards [G12FlexibleRectangle.rectangle_C2_bound 1 A hCscale hζ] with x hx
  intro M U T V hM hMU hU hT hTV hV ν hprod hν hνu hscale N hN hNC ε η Z t
  dsimp only
  intro hf
  exact hx M U T V hM hMU hU hT hTV hV ν hprod hν hνu hscale N hN hNC ε _
    (wellFactorable_to_signed hf)

end G12FlexibleWF
