import Wu18938Campaign.M6.HighPrefixPayment
import OriginalBoundaryConsumer

noncomputable section
open Finset Filter
open scoped Interval
open MathlibNt.SieveTheory

namespace Wu18938Campaign.M6
open OriginalU8.Weighted

theorem high_prefix_original_integral {e σ : ℝ}
    (he : (3 / 4 : ℝ) ≤ e) (he1 : e ≤ 1) (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ((U8Literal.physicalPrefix N e).card : ℝ) ≤
        ((36 / 5 : ℝ) * (∫ t in (100 / 1327 : ℝ)..(1 / 10),
          Real.log (2 - 3 * t) / (t * (1 - t) ^ 2)) + σ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log N) ^ 2 := by
  let B : ℝ := (9 / 5) * low (100 / 1327)
  have hcont : ContinuousAt (fun s : ℝ => 4 * (1 + s) ^ 2 * (B + s)) 0 := by fun_prop
  have h0 : 4 * (1 + (0 : ℝ)) ^ 2 * (B + 0) < 4 * B + σ / 2 := by
    nlinarith
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (eventually_lt_nhds h0))
  let s : ℝ := r / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hdist : dist s (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    dsimp [s]
    linarith
  have hcoeff : 4 * (1 + s) ^ 2 * (B + s) ≤ 4 * B + σ / 2 :=
    (hbound hdist).le
  obtain ⟨_, _, _, hnormalized⟩ := high_prefix_normalized s hs
  obtain ⟨δ₀, hδ₀, hδ₀u, ρ₀, hρ₀, hρ₀u, hmass⟩ :=
    original_mass_integral s s hs hs
  let δ : ℝ := δ₀ / 2
  let ε : ℝ := min ((100 / 1327 : ℝ) / 2) (δ / 2)
  let ρ : ℝ := (1 + ρ₀) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ δ₀ := by dsimp [δ]; linarith
  have hδu : δ < 1 / 4 := hδle.trans_lt hδ₀u
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεa : ε < (100 / 1327 : ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε < δ := (min_le_right _ _).trans_lt (by linarith)
  have hρ : 1 < ρ := by dsimp [ρ]; linarith
  have hρle : ρ ≤ ρ₀ := by dsimp [ρ]; linarith
  have he0 : 0 < e := by linarith
  have hU := SingularSeries.liuUniversalProduct_pos
  obtain ⟨Tp, hp⟩ := hnormalized 2 e ε δ ρ
    ((σ / 2) * SingularSeries.liuUniversalProduct)
    he he1 hε hεa hεδ hδu hρ (hρle.trans hρ₀u) (by positivity)
  obtain ⟨Tm, hm⟩ := hmass δ hδ.le hδle ρ hρ hρle e he0
  refine ⟨max ⌈Tp⌉₊ ⌈Tm⌉₊, ?_⟩
  intro N hN hEven
  have hNp : Tp ≤ (N : ℝ) := (Nat.le_ceil Tp).trans
    (by exact_mod_cast (le_max_left ⌈Tp⌉₊ ⌈Tm⌉₊).trans hN)
  have hNm : Tm ≤ (N : ℝ) := (Nat.le_ceil Tm).trans
    (by exact_mod_cast (le_max_right ⌈Tp⌉₊ ⌈Tm⌉₊).trans hN)
  have hP := hp N hNp hEven
  have hM := hm N hNm
  have hS := SingularSeries.liuSingularSeries_pos N
  let scale : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log N) ^ 2
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hmain :
      4 * (1 + s) * SingularSeries.liuSingularSeries N *
        (∑ k ∈ U8Literal.occupied N e ρ,
          OriginalU8.rectangleMass N ρ k / Real.log (OriginalU8.level N ρ δ k)) ≤
        (4 * B + σ / 2) * scale := by
    calc
      _ ≤ 4 * (1 + s) * SingularSeries.liuSingularSeries N *
          ((1 + s) * (B + s) * ((N : ℝ) / (Real.log N) ^ 2)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = (4 * (1 + s) ^ 2 * (B + s)) * scale := by dsimp [scale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hscale
  have herr :
      ((σ / 2) * SingularSeries.liuUniversalProduct) * (N : ℝ) / (Real.log N) ^ 2 ≤
        (σ / 2) * scale := by
    calc
      _ = ((σ / 2) * SingularSeries.liuUniversalProduct) *
          ((N : ℝ) / (Real.log N) ^ 2) := by ring
      _ ≤ ((σ / 2) * SingularSeries.liuSingularSeries N) *
          ((N : ℝ) / (Real.log N) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by positivity))
          (by positivity)
      _ = _ := by dsimp [scale]; ring
  calc
    _ ≤ _ := hP
    _ ≤ (4 * B + σ / 2) * scale + (σ / 2) * scale := add_le_add hmain herr
    _ = _ := by
      dsimp [B, scale]
      rw [original_low_eq_single]
      ring

theorem paperSmallEighth_original_integral_add_low {e σ : ℝ}
    (he : (3 / 4 : ℝ) ≤ e) (he1 : e ≤ 1) (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ((paperSmallEighth N).card : ℝ) ≤
        ((36 / 5 : ℝ) * (∫ t in (100 / 1327 : ℝ)..(1 / 10),
          Real.log (2 - 3 * t) / (t * (1 - t) ^ 2)) + σ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log N) ^ 2 +
            (U8Literal.smallPrefix N e).card := by
  obtain ⟨N₀, hN₀⟩ := high_prefix_original_integral he he1 hσ
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  rw [paperSmallEighth_eq, U8Literal.physicalSmall_card_split N e, Nat.cast_add]
  exact add_le_add (hN₀ N hN hEven) le_rfl

end Wu18938Campaign.M6
