import U8SingleLineageJoin
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeC2

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace WuPaper.R2Fouvry

def shortScale (ρ : ℝ) (k : U8Literal.Key) : ℝ := (2/3 : ℝ)*ρ^k.1

def longScale (ρ : ℝ) (k : U8Literal.Key) : ℝ := ρ^(k.2.1+k.2.2)

def physicalScale (ρ : ℝ) (k : U8Literal.Key) : ℝ :=
  4*longScale ρ k*shortScale ρ k

theorem physicalScale_eq_four (ρ : ℝ) (k : U8Literal.Key) :
    physicalScale ρ k = 4*(longScale ρ k*shortScale ρ k) := by
  unfold physicalScale
  ring

theorem occupied_product_lower {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) {k : U8Literal.Key} (hk : OriginalU8.Occupied N e ρ k) :
    e*(N : ℝ) < ρ^3*longScale ρ k*ρ^k.1 := by
  obtain ⟨n,z,hz,hp,_,hl,hu,hw,_⟩ := hk
  have hm : z.1*z.2 ∈ fouvryG9LongProducts N ρ k :=
    mem_image_of_mem (fun z : ℕ × ℕ => z.1*z.2) (mem_filter.mp hz).1
  have hmu := (fouvryG9LongProducts_bounds hρ hm).2
  have hn := (lt_min_iff.mp hu).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
  have hm0 : (0 : ℝ) < (z.1*z.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos (OriginalU8.labels_positive N ρ k z hz).1
      (OriginalU8.labels_positive N ρ k z hz).2
  have hb := mul_lt_mul hn hmu.le hm0 (pow_nonneg (by linarith : 0 ≤ ρ) _)
  rw [pow_succ] at hb
  dsimp [longScale]
  nlinarith only [hw,hb]

theorem high_product_residue {N : ℕ} {e ρ : ℝ}
    (he : (3/4 : ℝ) ≤ e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : U8Literal.Key} (hk : OriginalU8.Occupied N e ρ k) :
    (N : ℝ) < physicalScale ρ k := by
  have hb := occupied_product_lower hρ hk
  have hr0 : 0 ≤ ρ := by linarith
  have hr3 : ρ^3 ≤ (5/4 : ℝ)^3 := pow_le_pow_left₀ hr0 hρu 3
  have hm0 : 0 ≤ longScale ρ k*ρ^k.1 := by
    unfold longScale
    positivity
  have hp := mul_le_mul_of_nonneg_right hr3 hm0
  have heN := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)
  unfold physicalScale shortScale
  nlinarith only [hb,hp,heN,hm0]

theorem strict_nu {x T : ℝ} (hx : 1 < x) (hT : T = x^(Real.log T/Real.log x))
    (hTN : T ≤ x^(1/10 : ℝ)) :
    Real.log T/Real.log x ≤ 1/10 := by
  exact (Real.rpow_le_rpow_left_iff hx).mp (by rwa [← hT])

theorem original_parameters {e ε δ : ℝ}
    (he : (3/4 : ℝ) ≤ e) (he1 : e ≤ 1) (hε : 0 < ε)
    (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : U8Literal.Key,
      OriginalU8.Occupied N e ρ k →
      let T := shortScale ρ k
      let M := longScale ρ k
      let x := physicalScale ρ k
      let ν := Real.log T/Real.log x
      1 ≤ M ∧ 1 < x ∧ 1 ≤ T ∧ T = x^ν ∧ ε ≤ ν ∧
        ν ≤ 1/10 ∧ (N : ℝ) < x ∧
        1 ≤ OriginalU8.level N ρ δ k ∧
        OriginalU8.level N ρ δ k ≤ x^((5-5*ν)/9-ε) := by
  have he0 : 0 < e := by linarith
  obtain ⟨N₁,hp⟩ := OriginalU8.parameters he0 he1 hε hεa hεδ hδ
  refine ⟨max N₁ 1,?_⟩
  intro N hN ρ hρ hρu k hk
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hM,hx,hT,hid,hlo,_,_,hlev,_⟩ :=
    hp N ((le_max_left _ _).trans hN) ρ hρ hρu k hk
  have hNx := high_product_residue he hρ hρu hk
  have hTu := (OriginalU8.geometry he0 hρ hρu hk).2.2.2.2
  have hTx : shortScale ρ k ≤ (physicalScale ρ k)^(1/10 : ℝ) :=
    hTu.trans (Real.rpow_le_rpow (Nat.cast_nonneg N) hNx.le (by norm_num))
  exact ⟨hM,hx,hT,hid,hlo,strict_nu hx hid hTx,hNx,
    g9Scale_global_level_ge_one hN1 hT hTu hδ,hlev⟩

end WuPaper.R2Fouvry

#check @WuPaper.R2Fouvry.shortScale
#check @WuPaper.R2Fouvry.longScale
#check @WuPaper.R2Fouvry.physicalScale
#check @WuPaper.R2Fouvry.physicalScale_eq_four
#check @WuPaper.R2Fouvry.occupied_product_lower
#check @WuPaper.R2Fouvry.high_product_residue
#check @WuPaper.R2Fouvry.strict_nu
#check @WuPaper.R2Fouvry.original_parameters
#print axioms WuPaper.R2Fouvry.shortScale
#print axioms WuPaper.R2Fouvry.longScale
#print axioms WuPaper.R2Fouvry.physicalScale
#print axioms WuPaper.R2Fouvry.physicalScale_eq_four
#print axioms WuPaper.R2Fouvry.occupied_product_lower
#print axioms WuPaper.R2Fouvry.high_product_residue
#print axioms WuPaper.R2Fouvry.strict_nu
#print axioms WuPaper.R2Fouvry.original_parameters
