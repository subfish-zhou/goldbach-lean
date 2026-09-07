import MathlibNt.SieveTheory.LiLiuGoldbachG11ActualGrid

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The physical rectangle scale includes the existing two-thirds endpoint buffer. -/
def goldbachG11GridPhysicalScale (ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  4*ρ^k.2*((2/3 : ℝ)*ρ^k.1)

theorem goldbachG11GridLong_rectangle {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (k : ℕ × ℕ) {m : ℕ}
    (hm : m ∈ goldbachG11GridLong N ε ρ k) :
    ρ^k.2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*ρ^k.2 := by
  obtain ⟨_hm,hlo,hhi,_⟩ := mem_filter.mp hm
  rw [pow_succ] at hhi
  have hM : 0 ≤ ρ^k.2 := pow_nonneg (by linarith) _
  exact ⟨hlo,by nlinarith⟩

/-- The strict prefix and an occupied atom give the real physical x-window.
It is not legal to replace x by N inside the distribution theorem. -/
theorem goldbachG11GridPhysicalScale_window {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ}
    (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    ε*(N : ℝ) < goldbachG11GridPhysicalScale ρ k ∧
      goldbachG11GridPhysicalScale ρ k ≤ 4*(N : ℝ) := by
  obtain ⟨m,p,_hm,hpF,hplo,hphi,hmlo,hmhi⟩ := goldbachG11GridUsed_witness hρ hk
  obtain ⟨_hp,_hc,_hz,_hmin,hε,hprod,_hout⟩ :=
    mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF
  have hρ0 : 0 < ρ := by linarith
  have hM : 0 < ρ^k.2 := pow_pos hρ0 _
  have hT : 0 < ρ^k.1 := pow_pos hρ0 _
  have hlower : ε*(N : ℝ) < (p : ℝ)*m := by simpa only [Nat.cast_mul] using hε
  have hupper : (p : ℝ)*m < N := by exact_mod_cast hprod
  rw [pow_succ] at hphi hmhi
  have hpm := (mul_le_mul_of_nonneg_right hphi.le (Nat.cast_nonneg m)).trans_lt
    (mul_lt_mul_of_pos_left hmhi (mul_pos hT hρ0))
  have hρ2 : ρ^2 ≤ (8/3 : ℝ) := by nlinarith
  have hpay := mul_le_mul_of_nonneg_right hρ2 (mul_nonneg hM.le hT.le)
  have hMT := mul_le_mul hmlo hplo hT.le (Nat.cast_nonneg m)
  unfold goldbachG11GridPhysicalScale
  constructor <;> nlinarith [mul_nonneg hM.le hT.le]

/-- Fixed positive epsilon supplies the fixed shift multiplier for the physical scale. -/
theorem goldbachG11GridPhysicalScale_shift {N : ℕ} {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ}
    (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    (N : ℝ) ≤ (1/ε)*goldbachG11GridPhysicalScale ρ k := by
  have h := (goldbachG11GridPhysicalScale_window hρ hρu hk).1.le
  have hh : (N : ℝ) ≤ goldbachG11GridPhysicalScale ρ k / ε :=
    (le_div_iff₀ hε).2 (by simpa [mul_comm] using h)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh

/-- Before any later cell, the short distribution scale stays above a fixed power of N. -/
theorem goldbachG11Grid_short_scale_lower {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ}
    (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    (N : ℝ)^(4/53 : ℝ)/2 ≤ (2/3 : ℝ)*ρ^k.1 := by
  obtain ⟨_m,p,_hm,hpF,_hplo,hphi,_⟩ := goldbachG11GridUsed_witness hρ hk
  have hz := (mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF).2.2.1
  have hT : 0 ≤ ρ^k.1 := pow_nonneg (by linarith) _
  rw [pow_succ] at hphi
  nlinarith

/-- The actual occupied two-dimensional grid has quadratic logarithmic cost. -/
theorem goldbachG11GridUsed_card {N : ℕ} {ε ρ : ℝ} (hρ : 1 < ρ) :
    (goldbachG11GridUsed N ε ρ).card ≤ (fouvryG9GridIndex ρ N+1)^2 := by
  let B := fouvryG9GridIndex ρ N+1
  have hsub : goldbachG11GridUsed N ε ρ ⊆ range B ×ˢ range B := by
    intro k hk
    obtain ⟨⟨m,p⟩,hv,rfl⟩ := mem_image.mp hk
    obtain ⟨hmp,hpF⟩ := mem_filter.mp hv
    have hm := (mem_product.mp hmp).1
    obtain ⟨hm0,hmN,_⟩ := goldbachG11ProductSupport_data hm
    have hp := (mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF).1
    have hpN := mem_range.mp (mem_product.mp hmp).2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hmi := fouvryG9GridIndex_mono hρ hm1 (by exact_mod_cast hmN.le : (m : ℝ) ≤ N)
    have hpi := fouvryG9GridIndex_mono hρ hp1 (by exact_mod_cast hpN.le : (p : ℝ) ≤ N)
    apply mem_product.mpr
    constructor <;> apply mem_range.mpr
    · exact Nat.lt_succ_of_le hpi
    · exact Nat.lt_succ_of_le hmi
  exact (card_le_card hsub).trans_eq (by simp [B,pow_two])

/-- Any overhanging pair in an occupied rectangle remains below 4N. -/
theorem goldbachG11Grid_pair_product_bound {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ)
    {m p : ℕ} (hm : m ∈ goldbachG11GridLong N ε ρ k)
    (hp : p ∈ goldbachG11GridShort N ρ k) : m*p ≤ 4*N := by
  have hmhi := (goldbachG11GridLong_rectangle hρ hρu k hm).2
  have hphi := (goldbachG11GridShort_mem_iff hρ hρu hbig hk p).mp hp
  have hu := (goldbachG11GridUsed_short_gates hρ hρu hbig hk).2.2
  have hp2 : (p : ℝ) ≤ 2*((2/3 : ℝ)*ρ^k.1) := by linarith [hphi.2]
  have hpair := mul_le_mul hmhi hp2 (Nat.cast_nonneg p)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (by linarith : 0 ≤ ρ) _))
  have hwindow := (goldbachG11GridPhysicalScale_window hρ hρu hk).2
  have hreal : (m : ℝ)*p ≤ 4*N := by
    dsimp [goldbachG11GridPhysicalScale] at hwindow
    nlinarith
  exact_mod_cast hreal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig