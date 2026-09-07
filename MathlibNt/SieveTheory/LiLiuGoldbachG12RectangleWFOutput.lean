import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFRemainder

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12RectangleWF

/-- The output pushforward has exactly the physical rectangle mass. -/
theorem sieve_totalMass (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ) :
    (sieve N hEven ε Z M T).totalMass = mass N ε M T := rfl

theorem sieve_test (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ (sieve N hEven ε Z M T).support.filter P,
      (sieve N hEven ε Z M T).weights n) =
      ∑ p ∈ G12LowRectangle.rectangle N ε M T,
        if P (N-p.2*p.1) then goldbachG12NormalizedCoefficient N p.1 else 0 := by
  let A := G12LowRectangle.rectangle N ε M T
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
  simpa only [sieve, outputWeight, A, U, out, sum_filter] using hf

theorem sieve_rem (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (sieve N hEven ε Z M T).rem d = residue N ε M T d := by
  have hm : (sieve N hEven ε Z M T).multSum d =
      ∑ p ∈ G12LowRectangle.rectangle N ε M T,
        if d ∣ N-p.2*p.1 then goldbachG12NormalizedCoefficient N p.1 else 0 := by
    unfold BoundingSieve.multSum
    rw [← sum_filter]
    exact sieve_test N hEven ε Z M T (fun n => d ∣ n)
  unfold BoundingSieve.rem
  rw [hm, sieve_nu, goldbachB10BoundingSieve_nu_eq_inv_totient hEven hd, sieve_totalMass]
  unfold residue
  ring

/-- On its original primorial carrier the signed remainder is exactly C2
minus the explicit gcd gate, with no other correction. -/
theorem restricted_common_identity (N : ℕ) (ε Z : ℝ) (M T : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ (goldbachB10ProdPrimes N Z).divisors, c d * residue N ε M T d) =
      G12LowRectangle.discrepancy N (G12LowRectangle.rectangle N ε M T)
        (goldbachB10ProdPrimes N Z).divisors c -
      gate N (G12LowRectangle.rectangle N ε M T) (goldbachB10ProdPrimes N Z).divisors c := by
  rw [← common_eq_discrepancy_sub_gate]
  have he : reducedModuli (goldbachB10ProdPrimes N Z).divisors (N : ℤ) =
      (goldbachB10ProdPrimes N Z).divisors := by
    apply filter_eq_self.mpr
    intro d hd
    have hc := (goldbachB10_dvd_prodPrimes_coprime_N (Nat.dvd_of_mem_divisors hd)).symm
    simpa only [Int.gcd_natCast_natCast] using hc
  unfold common
  rw [he]
  apply sum_congr rfl
  intro d _
  rw [residue_eq]
  rfl

/-- A literal repeated-label small-output count, not a manufactured error term. -/
theorem smallOutput_eq_original (N : ℕ) (ε Z : ℝ) (M T : ℕ) :
    smallOutput N ε Z M T = 400 * ∑ p ∈ G12LowRectangle.rectangle N ε M T,
      goldbachG12NormalizedCoefficient N p.1 * (if N-p.2*p.1 < Nat.ceil Z then 1 else 0) :=
  labels_test N ε M T (fun p => if N-p.2*p.1 < Nat.ceil Z then 1 else 0)

/-- The final finite output sieve and full-interval C2 bridge use one and the
same constructed external family. The signed transport term is retained,
not silently dropped or replaced by a squarefree mask. -/
theorem exists_rectangle_full_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ (N : ℕ) (_hEven : Even N) (ε Z : ℝ) (M T : ℕ),
          2 ≤ Z → Z ≤ Real.sqrt Q →
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let V := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C * (η + (η^8)⁻¹ * Real.exp (6*K+2) * Real.log Q^(-(1/3 : ℝ)))
          (∀ t ∈ externalTags true P D η Z,
            SignedWellFactorable 1 Q (fun d => externalTerm true P D η Z t d)) ∧
          (400 * ∑ p ∈ G12LowRectangle.rectangle N ε M T,
            goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0)) ≤
            400 * mass N ε M T * V * (jr1965F (Real.log Q / Real.log Z) + E) +
            400 * (∑ t ∈ externalTags true P D η Z,
              let c := externalTerm true P D η Z t
              G12LowRectangle.discrepancy N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) c -
                gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) c -
                outsidePrimorial N ε Z Q M T c) + smallOutput N ε Z M T := by
  obtain ⟨K,C,hK,hC,h⟩ := exists_rectangle_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,h⟩ := h η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ N hEven ε Z M T hZ hZQ
  obtain ⟨hf,hu⟩ := h Q hQ N hEven ε Z M T hZ hZQ
  dsimp only at hf hu ⊢
  refine ⟨fun t ht => wellFactorable_to_signed (hf t ht),?_⟩
  rw [primeCount_eq_original,
    external_remainder_decomposition N hEven ε Z Q η M T hf] at hu
  exact hu

/-- The full-interval discrepancy of each actual external member consumes
C2 directly. This does not assert payment of either explicit gate. -/
theorem family_C2_bound (A : ℕ) {Cscale ζ : ℝ}
    (hCscale : 1 ≤ Cscale) (hζ : 0 < ζ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ M T : ℕ, 1 ≤ M → 1 ≤ T →
      ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
      (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
      ∀ ε η Z : ℝ, ∀ t : List ℕ,
      let Q := x^((5-5*ν)/9-ζ)
      let c := externalTerm true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z t
      WellFactorable c Q →
        |G12LowRectangle.discrepancy N (G12LowRectangle.rectangle N ε M T)
          (Ioc 0 ⌊Q⌋₊) c| ≤ x/Real.log x^A := by
  filter_upwards [G12LowRectangle.rectangle_C2_bound 1 A hCscale hζ] with x hx
  intro M T hM hT ν hprod hν hνu hscale N hN hNC ε η Z t
  dsimp only
  intro hf
  exact hx M T hM hT ν hprod hν hνu hscale N hN hNC ε _
    (wellFactorable_to_signed hf)

end G12RectangleWF
