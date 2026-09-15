import R2FouvryConsumer
import OriginalPayment

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace WuPaper.R2Fouvry

theorem original_sieve_cell_paid (A : ℕ) {e ε δ η : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : U8Literal.Key,
      OriginalU8.Occupied N e ρ k → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      let D := externalInternalLevel (OriginalU8.level N ρ δ k) η
      OriginalU8.sifted N ρ k P ≤
        (∑ t ∈ externalTags true P D η z, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d*OriginalU8.center N ρ k d) +
        (N : ℝ)/Real.log (N : ℝ)^A := by
  have he0 : 0 < e := by linarith
  let B : ℝ := Real.exp (8*(η⁻¹)^3)
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨N₁,hsieve⟩ := original_sieve_cell (A+1) he he1 hε hεa hεδ hδ hη hηu
  obtain ⟨N₂,hfamily⟩ :=
    original_rosser_error_uniform (A+1) he he1 hε hεa hεδ hδ hη hηu
  obtain ⟨N₃,hexc⟩ := OriginalU8.exceptional_log_payment (A+1)
    he0 (hε.le.trans hεδ.le) hδ hη hηu (by norm_num : (0 : ℝ) < 1)
  refine ⟨max N₁ (max N₂ (max N₃ (Real.exp (4*B+1)))),?_⟩
  intro N hN ρ hρ hρu k hk P hP hPN z hcut
  obtain ⟨hN₁,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hN₂,hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hN₃,hNexp⟩ := max_le_iff.mp hrest
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hNexp
  have hlog : 4*B+1 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr hNexp
  have hlpos : 0 < Real.log (N : ℝ) := by linarith
  have hNx := high_product_residue he hρ hρu hk
  have hxN : physicalScale ρ k ≤ 4*(N : ℝ) :=
    (OriginalU8.geometry he0 hρ hρu hk).2.2.1
  have hlogx : Real.log (N : ℝ) ≤ Real.log (physicalScale ρ k) :=
    Real.log_le_log hNpos hNx.le
  have hden : Real.log (N : ℝ)^(A+1) ≤ Real.log (physicalScale ρ k)^(A+1) :=
    pow_le_pow_left₀ hlpos.le hlogx _
  have hratio : physicalScale ρ k/Real.log (physicalScale ρ k)^(A+1) ≤
      4*((N : ℝ)/Real.log (N : ℝ)^(A+1)) := by
    calc
      _ ≤ physicalScale ρ k/Real.log (N : ℝ)^(A+1) :=
        div_le_div_of_nonneg_left (hNpos.trans hNx).le (pow_pos hlpos _) hden
      _ ≤ (4*(N : ℝ))/Real.log (N : ℝ)^(A+1) :=
        div_le_div_of_nonneg_right hxN (pow_nonneg hlpos.le _)
      _ = _ := by ring
  let S := externalTags true P
    (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z
  have hcard : (S.card : ℝ) ≤ B := (hfamily N hN₂ ρ hρ hρu k hk true P z).2.2.1.le
  have hcost : (S.card : ℝ)*
      (physicalScale ρ k/Real.log (physicalScale ρ k)^(A+1)) ≤
      4*B*((N : ℝ)/Real.log (N : ℝ)^(A+1)) := by
    calc
      _ ≤ (S.card : ℝ)*(4*((N : ℝ)/Real.log (N : ℝ)^(A+1))) :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
      _ ≤ B*(4*((N : ℝ)/Real.log (N : ℝ)^(A+1))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hE := hexc N hN₃ ρ hρ hρu k hk P z
  have hneg : -(∑ t ∈ S, OriginalU8.exceptional N ρ δ k P η z t) ≤
      ∑ t ∈ S, |OriginalU8.exceptional N ρ δ k P η z t| := by
    rw [← sum_neg_distrib]
    exact sum_le_sum (fun _ _ => neg_le_abs _)
  have hpay : (4*B+1)*((N : ℝ)/Real.log (N : ℝ)^(A+1)) ≤
      (N : ℝ)/Real.log (N : ℝ)^A := by
    calc
      _ ≤ Real.log (N : ℝ)*((N : ℝ)/Real.log (N : ℝ)^(A+1)) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = _ := by rw [pow_succ]; field_simp
  have hs := hsieve N hN₁ ρ hρ hρu k hk P hP hPN z hcut
  dsimp only at hs ⊢
  change _ ≤ 1*(N : ℝ)/Real.log (N : ℝ)^(A+1) at hE
  dsimp only [S] at hcost hneg
  rw [add_sub_assoc] at hs
  apply hs.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 4*B*((N : ℝ)/Real.log (N : ℝ)^(A+1)) +
        (N : ℝ)/Real.log (N : ℝ)^(A+1) := by
      simpa only [one_mul,sub_eq_add_neg] using add_le_add hcost (hneg.trans hE)
    _ = (4*B+1)*((N : ℝ)/Real.log (N : ℝ)^(A+1)) := by ring
    _ ≤ _ := hpay

theorem original_physical_prefix_paid (A : ℕ) {e ε δ η : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      ((U8Literal.physicalPrefix N e).card : ℝ) ≤
        (∑ k ∈ U8Literal.occupied N e ρ,
          ∑ t ∈ externalTags true P
            (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
            ∑ d ∈ (P.prod id).divisors,
              externalTerm true P
                (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d*
                  OriginalU8.center N ρ k d) +
        ((U8Literal.occupied N e ρ).card : ℝ)*((N : ℝ)/Real.log (N : ℝ)^A) +
        (U8Literal.outputBad N e P).card := by
  obtain ⟨N₁,hcell⟩ := original_sieve_cell_paid A he he1 hε hεa hεδ hδ hη hηu
  refine ⟨max N₁ 1,?_⟩
  intro N hN ρ hρ hρu P hP hPN z hcut
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_right N₁ 1).trans hN
  have hs := U8Literal.physicalPrefix_le_rectangles_add_outputBad hN1 e hρ P
  have hb := sum_le_sum (s := U8Literal.occupied N e ρ) (fun k hk =>
    hcell N ((le_max_left N₁ 1).trans hN) ρ hρ hρu k
      (U8Literal.Join.occupied_to_original hN1 hρ hk) P hP hPN z hcut)
  simp only [← U8Literal.Join.sifted_eq,sum_add_distrib,sum_const,nsmul_eq_mul] at hb
  exact hs.trans (add_le_add hb le_rfl)

end WuPaper.R2Fouvry

#check @WuPaper.R2Fouvry.original_sieve_cell_paid
#check @WuPaper.R2Fouvry.original_physical_prefix_paid
#print axioms WuPaper.R2Fouvry.original_sieve_cell_paid
#print axioms WuPaper.R2Fouvry.original_physical_prefix_paid
