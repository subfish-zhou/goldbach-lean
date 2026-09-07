import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ShortInterval
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9BufferedScale
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ModulusSupport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKGoldbachRectangle

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The separated G9 rectangle error with the unchanged global weight and level.
The interval endpoints are data, independent of any nonemptiness witness. -/
def fouvryG9RectangleError (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ)
    (c : ℕ → ℝ) : ℝ :=
  signedError (fouvryG9LongProducts N ρ k)
    (primeSWInterval ((⌈max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ))⌉ : ℝ)-1)
      ((⌈min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))⌉ : ℝ)-1))
    (Ioc 0 ⌊(N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))⌋₊)
    (fouvryG9LongAlpha N ρ k) (fun n => if n.Coprime N then primeSWBeta n else 0) c N

/-- Expanded C2 now pays the actual separated G9 rectangle. The threshold
precedes the mesh ratio, occupied cell, and original global weight. -/
theorem fouvryG9RectangleError_uniform (j A : ℕ) {e ε δ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      (fouvryG9GridCell N e ρ k).Nonempty →
      ∀ c : ℕ → ℝ,
      SignedWellFactorable j ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) c →
      let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
      |fouvryG9RectangleError N ρ δ k c| ≤ x/Real.log x^A := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  have hK0 : 0 < 2/e := by positivity
  obtain ⟨N₁,hparams⟩ := fouvryG9Grid_exists_buffered_C2_parameters he he1 hε hεa hεδ hδ
  obtain ⟨N₂,hbigN⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  obtain ⟨x₀,hC2⟩ := eventually_atTop.mp (primeC2_goldbach_rectangle_kscale 2 j A hK hε)
  refine ⟨max (max N₁ N₂) (max ((2/e)*x₀) 1), ?_⟩
  intro N hN ρ hρ hρu k hne c hc
  have hNN₁ : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNN₂ : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNx₀ : (2/e)*x₀ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let T := (2/3 : ℝ)*ρ^k.1
  let M := ρ^(k.2.1+k.2.2)
  let x := 4*M*T
  let ν := Real.log T/Real.log x
  obtain ⟨hM,hx,hT,hid,hlo,hhi,hNK,hWF⟩ := hparams N hNN₁ ρ hρ hρu k hne
  obtain ⟨_,hNx,hxN,hNT,hTN⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
  have h6 : (6 : ℝ) ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hbigN N hNN₂
  have hbig : 3 ≤ ρ^k.1 := by nlinarith [hNT]
  let z := fouvryG9GridPrimeInterval hρ hρu k hbig hne
  have hx₀ : x₀ ≤ x := le_of_mul_le_mul_left (hNx₀.trans hNK) hK0
  have hlocal := hWF j c hc
  have hlocal1 : 1 ≤ x^((5-5*ν)/9-ε) := by
    apply Real.one_le_rpow hx.le
    dsimp only [ν]
    linarith
  have hglobal1 := g9Scale_global_level_ge_one hN1 hT hTN hδ
  have hbound := hC2 x hx₀ z M ν hM rfl hlo hhi hid
    N (by exact_mod_cast (show (0 : ℝ) < N by linarith)) hNK
    (fouvryG9LongProducts N ρ k)
    (fun m hm => ⟨(fouvryG9LongProducts_bounds hρ hm).1,
      fouvryG9LongProducts_le_two hρ hρu hm⟩)
    (fouvryG9LongAlpha N ρ k) c
    (fun m _ => by
      rw [abs_of_nonneg (fouvryG9LongAlpha_nonneg N ρ k m)]
      exact (fouvryG9LongAlpha_bounds N ρ k m).2.1.trans_eq
        (fouvryG9LongAlpha_bounds N ρ k m).2.2)
    hlocal
  have heq := signedError_levels_eq_of_support (fouvryG9LongProducts N ρ k)
    (primeSWInterval z.lower z.upper) (fouvryG9LongAlpha N ρ k)
    (fun n => if n.Coprime N then primeSWBeta n else 0) c N
    (hc.factorSupported hglobal1) (hlocal.factorSupported hlocal1)
  change |signedError (fouvryG9LongProducts N ρ k) (primeSWInterval z.lower z.upper)
    (Ioc 0 ⌊(N : ℝ)^(5/9-δ)/T^(5/9 : ℝ)⌋₊) (fouvryG9LongAlpha N ρ k)
    (fun n => if n.Coprime N then primeSWBeta n else 0) c N| ≤ x/Real.log x^A
  rw [heq]
  exact hbound

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
