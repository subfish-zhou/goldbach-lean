import MixedEtaUniform

namespace HighIncrement
open Finset Real Wu2008DoubleSieve MixedSixth MixedEta Filter
open scoped Classical Topology
noncomputable section

/-- Literal replaced high contribution, not an additional independent count. -/
def E (N n : ℕ) (δ : ℝ) : ℝ :=
  highMain N n δ - truncatedSixthLowerNormalizedMain N δ 0
    (selected N n (highCells δ n))

def mesh (n : ℕ) : ℝ := 1/(n+1:ℕ)
def source (δ : ℝ) (n i : ℕ) : ℝ := truncatedSixthLowerS δ (hiX n i) (hiY n i)
def reserve : ℝ := PositiveH.lowerCorrection (29/10)
def gainWeight (δ : ℝ) (n i : ℕ) : ℝ := (3/2)*PositiveH.lowerCorrection (source δ n i)

theorem reserve_pos : 0 < reserve :=
  PositiveH.lowerCorrection_pos (by norm_num) (by norm_num)

theorem mesh_pos (n : ℕ) : 0 < mesh n := by unfold mesh; positivity

theorem widths (n i : ℕ) : hiX n i-loX n i = mesh n ∧ hiY n i-loY n i = mesh n := by
  simp only [hiX,loX,hiY,loY,truncatedSixthClosureHi,truncatedSixthClosureLo,mesh,Nat.cast_add,Nat.cast_one]
  constructor <;> ring

theorem source_bounds {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ} (hi : i ∈ highCells δ n) :
    2 ≤ source δ n i ∧ source δ n i ≤ 29/10 := by
  have hg := high_geometry hi
  exact HighConsumer.high_source_bounds hδ hg.2.2
    (hg.2.1.trans_lt (truncatedSixthClosure_lo_lt_hi n (coarse i).2))

theorem reserve_le {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ} (hi : i ∈ highCells δ n) :
    reserve ≤ PositiveH.lowerCorrection (source δ n i) :=
  HighConsumer.correction_antitone (by linarith [(source_bounds hδ hi).1]) (source_bounds hδ hi).2

theorem gainWeight_pos {δ : ℝ} (hδ : 0 ≤ δ) {n i : ℕ} (hi : i ∈ highCells δ n) :
    0 < gainWeight δ n i := by
  unfold gainWeight
  exact mul_pos (by norm_num) (reserve_pos.trans_le (reserve_le hδ hi))

/-- Exact prime coordinates stay inside their original coarse cell. -/
theorem prime_source_bounds {N n k : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 ≤ δ) (hk : k ∈ packing N n (highCells δ n))
    (hp : p ∈ pairBox N n k) :
    source δ n (outer k) ≤ truncatedSixthLowerPrimeS N δ p ∧
    truncatedSixthLowerPrimeS N δ p-source δ n (outer k) ≤ 2*mesh n/truncatedSixthLowerAlpha ∧
    2 ≤ truncatedSixthLowerPrimeS N δ p ∧ truncatedSixthLowerPrimeS N δ p ≤ 4 := by
  have hg := high_geometry (packing_mem hk).1
  have hpall := (actual_selected_geometry hN hδ n).2.1
    (mem_biUnion.mpr ⟨k,hk,hp⟩)
  have hbox := physical_box_subset hN hk hp
  obtain ⟨hpx,hpy⟩ := mem_product.mp hbox
  have hx := truncatedSixthLower_coordinate_window hN hpx
  have hy := truncatedSixthLower_coordinate_window hN hpy
  have he := truncatedSixthLower_prime_s_eq hN hpall
  have hslo := (truncatedSixthLower_prime_s_bounds hN hδ hpall).1
  have horder := truncatedSixthClosure_s_order (δ := δ)
    (l := (log (p.1:ℝ)/log N,log (p.2:ℝ)/log N))
    (u := (hiX n (outer k),hiY n (outer k))) ⟨hx.2.le,hy.2.le⟩
  rw [← he] at horder
  refine ⟨horder,?_,hslo,?_⟩
  · rw [he]
    dsimp [source,truncatedSixthLowerS]
    rw [← sub_div,div_le_div_iff_of_pos_right truncatedSixthLower_parameters.1]
    linarith [(widths n (outer k)).1,(widths n (outer k)).2]
  · rw [he]
    apply (div_le_iff₀ truncatedSixthLower_parameters.1).mpr
    have hxlo := hg.1.trans hx.1
    have hylo := hg.2.1.trans hy.1
    norm_num [truncatedSixthLowerC,truncatedSixthLowerAlpha] at hxlo ⊢
    linarith

/-- The original positive correction pays the entire coarse logarithmic loss. -/
theorem classical_coefficient_upper {N n k : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 ≤ δ) (hk : k ∈ packing N n (highCells δ n))
    (hp : p ∈ pairBox N n k) (hm : 2*mesh n/truncatedSixthLowerAlpha ≤ reserve/2) :
    wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p) + gainWeight δ n (outer k) ≤
      highCoefficient δ n (outer k) := by
  obtain ⟨hsu,hloss,hs,hu⟩ := prime_source_bounds hN hδ hk hp
  have hlog := HighConsumer.logarithm_shift_loss (source_bounds hδ (packing_mem hk).1).1 hsu
  have he := ClassicalLossBottleneck.initial_exact hs hu
  have hr := reserve_le hδ (packing_mem hk).1
  unfold highCoefficient gainWeight source PositiveH.lowerCorrection at *
  dsimp at *
  linarith

end
end HighIncrement
