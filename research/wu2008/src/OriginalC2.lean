import OriginalGeometry
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKGoldbachRectangle

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace OriginalU8

def primeSupport (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  primeSWInterval ((⌈shortLower N ρ k⌉ : ℝ)-1) ((⌈shortUpper N ρ k⌉ : ℝ)-1)
def beta (N n : ℕ) : ℝ := if n.Coprime N then primeSWBeta n else 0
def level (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ) : ℝ :=
  (N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))
def error (N : ℕ) (ρ δ : ℝ) (k : ℕ × ℕ × ℕ) (c : ℕ → ℝ) : ℝ :=
  signedError (products (labels N ρ k)) (primeSupport N ρ k)
    (Ioc 0 ⌊level N ρ δ k⌋₊) (alpha (labels N ρ k)) (beta N) c N

/-- Literal endpoint characterization of the actual unfiltered interval. -/
theorem primeSupport_mem {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1) (h : Occupied N e ρ k) (n : ℕ) :
    n ∈ primeSupport N ρ k ↔
      ρ^k.1 ≤ n ∧ (N : ℝ)^(100/1327 : ℝ) ≤ n ∧
        (n : ℝ) < ρ^(k.1+1) ∧ (n : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  have hm := interval_mem hρ hρu k hbig h n
  change n ∈ primeSupport N ρ k ↔ _ at hm
  rw [hm]
  simp only [shortLower,shortUpper,max_le_iff,lt_min_iff,and_assoc]

/-- Exact whole-interval transfer for arbitrary signed kernels. -/
theorem short_sum (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ (primeSupport N ρ k).filter (fun n => n.Prime ∧ n.Coprime N), F n) =
      ∑ n ∈ primeSupport N ρ k, beta N n*F n := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime <;> by_cases hc : n.Coprime N <;>
    simp [beta,primeSWBeta,hp,hc]

/-- The original 100/1327 window supplies nu and the genuine level inequality. -/
theorem parameters {e ε δ : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hε : 0 < ε) (hεa : ε < 100/1327) (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k →
      let T := (2/3 : ℝ)*ρ^k.1
      let M := ρ^(k.2.1+k.2.2)
      let x := 4*M*T
      let ν := Real.log T/Real.log x
      1 ≤ M ∧ 1 < x ∧ 1 ≤ T ∧ T = x^ν ∧ ε ≤ ν ∧
        ν ≤ 1/10+ε/10 ∧ (N : ℝ) ≤ (2/e)*x ∧
        level N ρ δ k ≤ x^((5-5*ν)/9-ε) ∧
        ∀ j : ℕ, ∀ c : ℕ → ℝ,
          SignedWellFactorable j (level N ρ δ k) c →
          SignedWellFactorable j (x^((5-5*ν)/9-ε)) c := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  obtain ⟨N₀,hscale⟩ := g9Scale_exists_threshold_local_global_and_level
    (2/e) ε (100/1327) δ hK hε hεa (by norm_num) hεδ
  refine ⟨max N₀ 1,?_⟩
  intro N hN ρ hρ hρu k hne
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hM,hNx,hxN,hNT,hTN⟩ := geometry he hρ hρu hne
  obtain ⟨hx,hT,hid,hlo,hhi,hNK,hlevel⟩ :=
    hscale N ((le_max_left _ _).trans hN) _ _ hNx hxN hNT hTN
  refine ⟨hM,hx,hT,hid,hlo,hhi,hNK,hlevel,?_⟩
  intro j c hc
  exact hc.level_mono (g9Scale_global_level_ge_one hN1 hT hTN hδ) hlevel

/-- Common cutoff BEFORE mesh, cell, whole prime interval, long labels and signed weight.
The residue is the varying Goldbach integer N, bounded by K*x, never fixed 4/7. -/
theorem error_uniform (j A : ℕ) {e ε δ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k → ∀ c : ℕ → ℝ,
      SignedWellFactorable j (level N ρ δ k) c →
      let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
      |error N ρ δ k c| ≤ x/Real.log x^A := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  have hK0 : 0 < 2/e := by positivity
  obtain ⟨N₁,hparams⟩ := parameters he he1 hε hεa hεδ hδ
  obtain ⟨N₂,hbigN⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (100/1327) (by norm_num))
  obtain ⟨x₀,hC2⟩ := eventually_atTop.mp (primeC2_goldbach_rectangle_kscale 2 j A hK hε)
  refine ⟨max (max N₁ N₂) (max ((2/e)*x₀) 1),?_⟩
  intro N hN ρ hρ hρu k hne c hc
  have hNN₁ : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNN₂ : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNx₀ : (2/e)*x₀ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let T := (2/3 : ℝ)*ρ^k.1
  let M := ρ^(k.2.1+k.2.2)
  let x := 4*M*T
  let ν := Real.log T/Real.log x
  obtain ⟨hM,hx,hT,hid,hlo,hhi,hNK,_,hWF⟩ := hparams N hNN₁ ρ hρ hρu k hne
  obtain ⟨_,_,_,hNT,hTN⟩ := geometry he hρ hρu hne
  have h6 : (6 : ℝ) ≤ (N : ℝ)^(100/1327 : ℝ) := by simpa using hbigN N hNN₂
  have hbig : 3 ≤ ρ^k.1 := by nlinarith
  let z := interval hρ hρu k hbig hne
  have hx₀ : x₀ ≤ x := le_of_mul_le_mul_left (hNx₀.trans hNK) hK0
  have hlocal := hWF j c hc
  have hlocal1 : 1 ≤ x^((5-5*ν)/9-ε) := by
    apply Real.one_le_rpow hx.le
    dsimp only [ν]
    linarith
  have hglobal1 := g9Scale_global_level_ge_one hN1 hT hTN hδ
  have hbound := hC2 x hx₀ z M ν hM rfl hlo hhi hid
    N (by exact_mod_cast (show (0 : ℝ) < N by linarith)) hNK
    (products (labels N ρ k)) (fun m hm => products_bounds hρ hρu hm)
    (alpha (labels N ρ k)) c
    (fun m _ => alpha_order_two _ (labels_positive N ρ k) m) hlocal
  have heq := signedError_levels_eq_of_support (products (labels N ρ k))
    (primeSWInterval z.lower z.upper) (alpha (labels N ρ k)) (beta N) c N
    (hc.factorSupported hglobal1) (hlocal.factorSupported hlocal1)
  change |signedError (products (labels N ρ k)) (primeSWInterval z.lower z.upper)
    (Ioc 0 ⌊level N ρ δ k⌋₊) (alpha (labels N ρ k)) (beta N) c N| ≤ x/Real.log x^A
  rw [heq]
  exact hbound

end OriginalU8
