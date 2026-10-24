import WR2XiSixthQuadrature
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Set QuarterTrim WuSource.SrcSixthGain

def grid (i : ℕ) : ℝ := 2+(41453/10300-2)*(i:ℝ)/1024

def panelBound (i : ℕ) : ℝ :=
  8*(grid (i+1)-grid i)*(densityLower (grid i) (grid (i+1))*pointLower (grid (i+1)))

theorem grid_zero : grid 0 = 2 := by norm_num [grid]
theorem grid_last : grid 1024 = endpoint := by norm_num [grid,endpoint,alpha,beta]

theorem grid_mem {i : ℕ} (hi : i ≤ 1024) : grid i ∈ Icc 2 endpoint := by
  have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have h1 : (i:ℝ) ≤ 1024 := by exact_mod_cast hi
  norm_num [grid,endpoint,alpha,beta,mem_Icc]
  constructor <;> linarith

theorem grid_step (i : ℕ) : grid i ≤ grid (i+1) := by
  norm_num [grid,Nat.cast_add]
  linarith

theorem uniform_certificate {q : ℕ → ℝ} {target : ℝ}
    (hq : ∀ i < 1024, q i ≤ panelBound i)
    (ht : target ≤ ∑ i ∈ Finset.range 1024, q i) : target ≤ SourceSixth.amount :=
  certificate grid_zero grid_last (fun _ hi => grid_mem hi) (fun i _ => grid_step i) hq ht

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.uniform_certificate
