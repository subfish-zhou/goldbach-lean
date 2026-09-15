import R2FouvryGeometry

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace WuPaper.R2Fouvry

theorem original_error_uniform (j A : ℕ) {e ε δ : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : U8Literal.Key,
      OriginalU8.Occupied N e ρ k → ∀ c : ℕ → ℝ,
      SignedWellFactorable j (OriginalU8.level N ρ δ k) c →
      |OriginalU8.error N ρ δ k c| ≤
        physicalScale ρ k/Real.log (physicalScale ρ k)^A := by
  have he0 : 0 < e := by linarith
  obtain ⟨N₁,hparams⟩ := original_parameters he he1 hε hεa hεδ hδ
  obtain ⟨N₂,hbig⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (100/1327) (by norm_num))
  obtain ⟨x₀,hC2⟩ := eventually_atTop.mp (primeC2_clean_unconditional 2 j A hε hε)
  refine ⟨max N₁ (max N₂ (max x₀ 1)),?_⟩
  intro N hN ρ hρ hρu k hk c hc
  obtain ⟨hN₁,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hN₂,hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hNx₀,hN1⟩ := max_le_iff.mp hrest
  let T := shortScale ρ k
  let M := longScale ρ k
  let x := physicalScale ρ k
  let ν := Real.log T/Real.log x
  obtain ⟨hM,hx,hT,hid,hlo,hhi,hNx,hQ,hlevel⟩ :=
    hparams N hN₁ ρ hρ hρu k hk
  have hsix : (6 : ℝ) ≤ (N : ℝ)^(100/1327 : ℝ) := by
    simpa using hbig N hN₂
  have hshort := (OriginalU8.geometry he0 hρ hρu hk).2.2.2.1
  have hthree : 3 ≤ ρ^k.1 := by nlinarith
  let z := OriginalU8.interval hρ hρu k hthree hk
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  let idx : BetaCleanIndex PrimeC2Interval.scale ε :=
    { index := z
      residue := N
      scale := x
      one_le_T := hT
      one_le_scale := hx.le
      residue_ne_zero := by exact_mod_cast hNpos.ne'
      residue_le_scale := by simpa using hNx.le
      scale_rpow_le := by
        change x^ε ≤ T
        rw [hid]
        exact Real.rpow_le_rpow_of_exponent_le hx.le hlo }
  have hlocal := hc.level_mono hQ hlevel
  have hb := hC2 x (hNx₀.trans hNx.le) idx M ν hM rfl hlo hhi hid
    (OriginalU8.products (OriginalU8.labels N ρ k))
    (fun m hm => OriginalU8.products_bounds hρ hρu hm)
    (OriginalU8.alpha (OriginalU8.labels N ρ k)) c
    (fun m _ => OriginalU8.alpha_order_two _
      (OriginalU8.labels_positive N ρ k) m)
    hlocal N (by exact_mod_cast hNpos.ne') (by simpa using hNx.le)
  have hclean : betaClean primeSWBeta (N : ℤ) = OriginalU8.beta N :=
    funext (primeSWBeta_clean_nat N)
  change |signedError (OriginalU8.products (OriginalU8.labels N ρ k))
    (primeSWInterval z.lower z.upper) (Ioc 0 ⌊OriginalU8.level N ρ δ k⌋₊)
    (OriginalU8.alpha (OriginalU8.labels N ρ k)) (OriginalU8.beta N) c N| ≤
      x/Real.log x^A
  rw [signedError_level_eq_of_support hlevel _ _ _ _ _ _ (hc.factorSupported hQ)]
  simpa only [idx,hclean] using hb

theorem original_rosser_error_uniform (A : ℕ) {e ε δ η : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : U8Literal.Key,
      OriginalU8.Occupied N e ρ k →
      ∀ (upper : Bool) (P : Finset ℕ) (z : ℝ),
      let Q := OriginalU8.level N ρ δ k
      let D := externalInternalLevel Q η
      1 ≤ Q ∧ 2 ≤ D ∧
      ((externalTags upper P D η z).card : ℝ) < Real.exp (8*(η⁻¹)^3) ∧
      ∀ t ∈ externalTags upper P D η z,
        SignedWellFactorable 1 Q (fun d => externalTerm upper P D η z t d) ∧
        |OriginalU8.error N ρ δ k (fun d => externalTerm upper P D η z t d)| ≤
          physicalScale ρ k/Real.log (physicalScale ρ k)^A := by
  have he0 : 0 < e := by linarith
  obtain ⟨N₁,herr⟩ := original_error_uniform 1 A he he1 hε hεa hεδ hδ.le
  obtain ⟨N₂,hparams⟩ := original_parameters he he1 hε hεa hεδ hδ.le
  obtain ⟨N₃,hgate⟩ := g9WF_exists_internal_level_gate
    (show 0 ≤ δ by linarith) hδ hη 1
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro N hN ρ hρ hρu k hk upper P z
  obtain ⟨hN₁,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hN₂,hN₃⟩ := max_le_iff.mp hrest
  have hp := hparams N hN₂ ρ hρ hρu k hk
  have hg := OriginalU8.geometry he0 hρ hρu hk
  obtain ⟨_,hQ,_,hD,_⟩ := hgate N (shortScale ρ k) hN₃ hp.2.2.1 hg.2.2.2.2
  refine ⟨hQ,hD,(externalTags_card_and_wellFactorable upper P z hD hη hηu).1,?_⟩
  intro t ht
  have hw := externalTerm_signedWellFactorable upper P z t
    (zero_le_one.trans hQ) hD hη hηu ht
  exact ⟨hw,herr N hN₁ ρ hρ hρu k hk _ hw⟩

end WuPaper.R2Fouvry

#check @WuPaper.R2Fouvry.original_error_uniform
#check @WuPaper.R2Fouvry.original_rosser_error_uniform
#print axioms WuPaper.R2Fouvry.original_error_uniform
#print axioms WuPaper.R2Fouvry.original_rosser_error_uniform
