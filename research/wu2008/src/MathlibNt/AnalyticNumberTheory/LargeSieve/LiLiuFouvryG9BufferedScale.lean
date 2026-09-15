import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridRectangle
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ScaleLevel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LevelTransport

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Buffer the short scale so integer closed/open endpoints can later be encoded
inside the prime interval family. The physical product scale changes with it. -/
theorem fouvryG9Grid_buffered_geometry {N : ℕ} {e ρ : ℝ}
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : ℕ × ℕ × ℕ} (hne : (fouvryG9GridCell N e ρ k).Nonempty) :
    let T := (2/3 : ℝ) * ρ ^ k.1
    let M := ρ ^ (k.2.1+k.2.2)
    1 ≤ M ∧ (N : ℝ)/(2/e) ≤ 4*M*T ∧ 4*M*T ≤ 4*N ∧
      (N : ℝ)^(4/53 : ℝ)/2 ≤ T ∧ T ≤ (N : ℝ)^(1/10 : ℝ) := by
  dsimp only
  obtain ⟨y,hy⟩ := hne
  have hg := fouvryG9Carrier_geometry (fouvryG9GridCell_mem_iff.mp hy).1
  obtain ⟨hnlo,hnhi,hmlo,hmhi⟩ := fouvryG9GridCell_rectangle hρ hy
  have hw := fouvryG9GridCell_scale_window hρ hρu ⟨y,hy⟩
  have hT0 : 0 < ρ ^ k.1 := pow_pos (by linarith) _
  have hM0 : 0 < ρ ^ (k.2.1+k.2.2) := pow_pos (by linarith) _
  have hNL : (N : ℝ)^(4/53 : ℝ) ≤ (y.2.2 : ℝ) := hg.2.2.2.2.2.1
  have hNU : (y.2.2 : ℝ) < (N : ℝ)^(1/10 : ℝ) := hg.2.2.2.2.2.2.1
  have hNT : (N : ℝ)^(4/53 : ℝ) < (5/4 : ℝ)*ρ^k.1 :=
    hNL.trans_lt (hnhi.trans_le (mul_le_mul_of_nonneg_right hρu hT0.le))
  have hquot : (N : ℝ)/(2/e) = e*N/2 := by field_simp
  refine ⟨one_le_pow₀ hρ.le, ?_, ?_, ?_, ?_⟩
  · rw [hquot]; nlinarith [hw.1]
  · nlinarith [hw.2]
  · nlinarith
  · nlinarith

/-- Every occupied actual G9 cell admits the expanded C2 parameters at a common
threshold, and the same global weight transports to the local full level. -/
theorem fouvryG9Grid_exists_buffered_C2_parameters {e ε δ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      (fouvryG9GridCell N e ρ k).Nonempty →
      let T := (2/3 : ℝ)*ρ^k.1
      let M := ρ^(k.2.1+k.2.2)
      let x := 4*M*T
      let ν := Real.log T / Real.log x
      1 ≤ M ∧ 1 < x ∧ 1 ≤ T ∧ T = x^ν ∧ ε ≤ ν ∧
        ν ≤ 1/10+ε/10 ∧ (N : ℝ) ≤ (2/e)*x ∧
        ∀ j : ℕ, ∀ c : ℕ → ℝ,
          SignedWellFactorable j ((N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)) c →
          SignedWellFactorable j (x^((5-5*ν)/9-ε)) c := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  obtain ⟨N₀,hscale⟩ := g9Scale_exists_threshold_local_global_and_level
    (2/e) ε (4/53) δ hK hε hεa (by norm_num) hεδ
  refine ⟨max N₀ 1, ?_⟩
  intro N hN ρ hρ hρu k hne
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
  let T := (2/3 : ℝ)*ρ^k.1
  let M := ρ^(k.2.1+k.2.2)
  let x := 4*M*T
  obtain ⟨hM,hNx,hxN,hNT,hTN⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
  obtain ⟨hx,hT,hid,hlo,hhi,hNK,hlevel⟩ :=
    hscale N ((le_max_left _ _).trans hN) x T hNx hxN hNT hTN
  refine ⟨hM,hx,hT,hid,hlo,hhi,hNK,?_⟩
  intro j c hc
  apply hc.level_mono _ hlevel
  have hden : T^(5/9 : ℝ) ≤ (N : ℝ)^(5/9-δ) := by
    calc
      T^(5/9 : ℝ) ≤ ((N : ℝ)^(1/10 : ℝ))^(5/9 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hTN (by norm_num)
      _ = (N : ℝ)^(1/18 : ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg N)]; norm_num
      _ ≤ (N : ℝ)^(5/9-δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < T) _)).2
    (by simpa using hden)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
