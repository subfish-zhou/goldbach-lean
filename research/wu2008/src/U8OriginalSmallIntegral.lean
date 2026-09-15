import U8FixedPrefixPayment
import OriginalBoundaryClosed

/-! The original small-first-prime count, with the fixed small-product prefix
paid, on its genuine Liu singular-series scale. -/
noncomputable section
open scoped Interval
namespace OriginalU8.Weighted
open MathlibNt.SieveTheory

/-- This is the actual original-alpha integral, including its ideal weight. -/
def originalSmallIntegral : ℝ := (9/10) *
  ∫ x in (100/1327 : ℝ)..(1/10), Real.log (2-3*x)/(x*(1-x)^2)

private theorem small_slack_bound {B s : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (1+s)^2*(B+s) ≤ B+4*s*(B+1) := by
  have hs2 : s^2 ≤ s := by nlinarith
  have hs3 : s^3 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)]
  have hBs := mul_le_mul_of_nonneg_left hs2 hB
  nlinarith

/-- No small-prefix or density premise remains. The final threshold is selected
only after all fixed auxiliary parameters, with the original prime labels intact. -/
theorem physicalSmall_original_integral (σ : ℝ) (hσ : 0 < σ) :
    ∃ N0 : ℕ, ∀ N ≥ N0, Even N →
      ((U8Literal.physicalSmall N).card : ℝ) ≤
        (8*originalSmallIntegral+σ)*SingularSeries.liuSingularSeries N*
          (N : ℝ)/(Real.log N)^2 := by
  let B : ℝ := (9/5)*low (100/1327)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (low_nonneg (by norm_num) (by norm_num))
  let s : ℝ := min 1 (σ/(32*(B+1)))
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hcoeff : 4*(1+s)^2*(B+s) ≤ 4*B+σ/2 := by
    have hb := small_slack_bound hB hs.le hs1
    have hp := (le_div_iff₀ (show 0 < 32*(B+1) by positivity)).mp
      (min_le_right (1 : ℝ) (σ/(32*(B+1))))
    change s*(32*(B+1)) ≤ σ at hp
    nlinarith
  obtain ⟨e,he,hehalf,Np,hprefix⟩ :=
    U8Literal.SmallProduct.smallPrefix_sigma_payment (σ/4) (by positivity)
  obtain ⟨η,hη,hηu,δ0,hδ0,hδ0u,ρ0,hρ0,hρ0u,hphysical⟩ :=
    physicalSmall_integral s s s hs hs hs
  let δ : ℝ := δ0/2
  let ε : ℝ := min ((100/1327 : ℝ)/2) (δ/2)
  let ρ : ℝ := (1+ρ0)/2
  have hε : 0 < ε := lt_min (by norm_num) (by dsimp [δ]; positivity)
  have hεa : ε < (100/1327 : ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε < δ := (min_le_right _ _).trans_lt (by dsimp [δ]; linarith)
  have hδ : δ ≤ δ0 := by dsimp [δ]; linarith
  have hρ : 1 < ρ := by dsimp [ρ]; linarith
  have hρu : ρ ≤ ρ0 := by dsimp [ρ]; linarith
  have hS0 := SingularSeries.liuUniversalProduct_pos
  obtain ⟨Nm,hmass⟩ := hphysical 2 δ ε e ρ ((σ/4)*SingularSeries.liuUniversalProduct)
    hε hεa hεδ hδ he (by linarith) hρ hρu (by positivity)
  refine ⟨max Np ⌈Nm⌉₊, ?_⟩
  intro N hN hEven
  have hNp : Np ≤ N := (le_max_left _ _).trans hN
  have hNm : Nm ≤ (N : ℝ) := (Nat.le_ceil Nm).trans
    (by exact_mod_cast ((le_max_right Np ⌈Nm⌉₊).trans hN))
  have hP := hprefix N hNp hEven
  have hM := hmass N hNm hEven
  let scale : ℝ := SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2
  have hS := SingularSeries.liuSingularSeries_pos N
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hmain : 4*(1+s)*(1+s)*SingularSeries.liuSingularSeries N*(B+s)*
      ((N : ℝ)/(Real.log N)^2) ≤ (4*B+σ/2)*scale := by
    calc
      _ = (4*(1+s)^2*(B+s))*scale := by dsimp [scale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hscale
  have herr : ((σ/4)*SingularSeries.liuUniversalProduct)*(N : ℝ)/(Real.log N)^2 ≤
      (σ/4)*scale := by
    calc
      _ = ((σ/4)*SingularSeries.liuUniversalProduct)*((N : ℝ)/(Real.log N)^2) := by ring
      _ ≤ ((σ/4)*SingularSeries.liuSingularSeries N)*((N : ℝ)/(Real.log N)^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by positivity)) (by positivity)
      _ = _ := by dsimp [scale]; ring
  have hpref : ((U8Literal.smallPrefix N e).card : ℝ) ≤ (σ/4)*scale := by
    calc
      _ ≤ _ := hP
      _ = _ := by dsimp [scale]; ring
  calc
    _ ≤ _ := hM
    _ ≤ (4*B+σ/2)*scale+(σ/4)*scale+(σ/4)*scale :=
      add_le_add (add_le_add hmain herr) hpref
    _ = _ := by
      dsimp [B,scale,originalSmallIntegral]
      rw [original_low_eq_single]
      ring

end OriginalU8.Weighted
