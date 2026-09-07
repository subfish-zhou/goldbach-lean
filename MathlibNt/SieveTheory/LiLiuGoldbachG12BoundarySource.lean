import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundary
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12FineGrid

def boundarySourceLo (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : ℕ → ℝ :=
  G12ClippedWindow.clampLower N ε (fun _ => shortLower ρ N k) (fun _ => shortUpper ρ N k)
def boundarySourceHi (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : ℕ → ℝ :=
  G12ClippedWindow.clampUpper N ε (fun _ => shortUpper ρ N k)
def boundarySourceWindow (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) : Finset ℕ :=
  G12ClippedWindow.window N (boundarySourceLo ρ N ε k) (boundarySourceHi ρ N ε k) m

/-- The physical coprimality gate is retained; the analytic source is ungated. -/
theorem boundaryWindow_eq_source_filter (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) :
    boundaryWindow ρ N ε k m = (boundarySourceWindow ρ N ε k m).filter (fun r => r.Coprime N) := by
  unfold boundarySourceWindow boundarySourceLo boundarySourceHi
  rw [G12ClippedWindow.clamp_window_eq_filter]
  ext r
  simp only [boundaryWindow, goldbachG11LinkedPrimeWindow, mem_filter, max_lt_iff, le_min_iff]
  tauto

theorem boundaryCoefficient_eq_longMask (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) :
    boundaryCoefficient ρ N ε k = G12ClippedWindow.longMask N
      (fun m => m ∈ Ioc (longLower ρ k) (longUpper ρ N k))
      (G12FlexibleRectangle.longOK N ε (shortLower ρ N k) (shortUpper ρ N k)) := by
  funext m
  unfold boundaryCoefficient G12ClippedWindow.longMask
  by_cases h : boundaryMask ρ N ε k m
  · have h' : m ∈ Ioc (longLower ρ k) (longUpper ρ N k) ∧
        ¬G12FlexibleRectangle.longOK N ε (shortLower ρ N k) (shortUpper ρ N k) m := h
    rw [if_pos h, if_pos h']
  · have h' : ¬(m ∈ Ioc (longLower ρ k) (longUpper ρ N k) ∧
        ¬G12FlexibleRectangle.longOK N ε (shortLower ρ N k) (shortUpper ρ N k) m) := h
    rw [if_neg h, if_neg h']

/-- The actual boundary long mask, with the normalized empty-window endpoints. -/
theorem boundarySource_admissible (ρ : ℝ) {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    G12ClippedWindow.Admissible N ε (boundaryCoefficient ρ N ε k)
      (boundarySourceLo ρ N ε k) (boundarySourceHi ρ N ε k) := by
  rw [boundaryCoefficient_eq_longMask]
  exact G12ClippedWindow.clamp_admissible hN ε _ _ _ _

/-- This is the real source residual of the boundary mask, not a claim that its
short coprimality filter inherits SW. Its common mass is still ungated. -/
theorem boundarySource_common_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ρ ε : ℝ) (k : ℕ × ℕ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      (∑ d ∈ goldbachG11LinkedModuli N Q,
        |G12ClippedWindow.commonResidual N (boundaryCoefficient ρ N ε k)
          (boundarySourceLo ρ N ε k) (boundarySourceHi ρ N ε k) d|) ≤
        C*N/Real.log (N : ℝ)^A := by
  obtain ⟨B,C,hB,hC,J,hJ,h⟩ := G12ClippedWindow.longMask_common_log_saving A hA
  refine ⟨B,C,hB,hC,J,hJ,?_⟩
  intro N hN ρ ε k Q hQ
  rw [boundaryCoefficient_eq_longMask]
  exact h N hN _ _ _ _ ε Q hQ

theorem boundary_sum_le_source (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (k : ℕ × ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ m r, 0 ≤ f m r) :
    (∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1*f p.1 p.2) ≤
      ∑ m ∈ goldbachG12ActiveProductSupport N, ∑ r ∈ boundarySourceWindow ρ N ε k m,
        boundaryCoefficient ρ N ε k m * f m r := by
  rw [boundaryCell_weighted_window ρ hN ε k f]
  apply sum_le_sum
  intro m _
  apply sum_le_sum_of_subset_of_nonneg
  · rw [boundaryWindow_eq_source_filter]
    exact filter_subset _ _
  · intro r _ _
    exact mul_nonneg (boundaryCoefficient_bounds ρ N ε k m).1 (hf m r)

theorem boundary_output_le_source (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    (400*∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1*
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
      400*∑ m ∈ goldbachG12ActiveProductSupport N, ∑ r ∈ boundarySourceWindow ρ N ε k m,
        boundaryCoefficient ρ N ε k m*(if (N-r*m).Prime then (1 : ℝ) else 0) := by
  exact mul_le_mul_of_nonneg_left (boundary_sum_le_source ρ hN ε k
    (fun m r => if (N-r*m).Prime then (1 : ℝ) else 0)
    (by intro m r; split_ifs <;> norm_num)) (by norm_num)

/-- The first-prime coprimality transport is an explicit nonnegative residual mass. -/
def boundarySourceBadMass (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    ∑ _r ∈ (boundarySourceWindow ρ N ε k m).filter (fun r => ¬r.Coprime N),
      boundaryCoefficient ρ N ε k m

theorem boundary_source_mass_split (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    G12ClippedWindow.mass N (boundaryCoefficient ρ N ε k)
      (boundarySourceLo ρ N ε k) (boundarySourceHi ρ N ε k) =
      (∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1) +
        boundarySourceBadMass ρ N ε k := by
  have h := boundaryCell_weighted_window ρ hN ε k (fun _ _ => 1)
  simp only [mul_one] at h
  rw [h]
  unfold G12ClippedWindow.mass boundarySourceBadMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  rw [boundaryWindow_eq_source_filter, sum_filter, sum_filter, ← sum_add_distrib]
  change boundaryCoefficient ρ N ε k m * (boundarySourceWindow ρ N ε k m).card = _
  calc
    _ = ∑ _r ∈ boundarySourceWindow ρ N ε k m, boundaryCoefficient ρ N ε k m := by simp [mul_comm]
    _ = _ := by
      apply sum_congr rfl
      intro r _
      by_cases hr : r.Coprime N <;> simp [hr]

/-- The discarded first-prime mass is dominated by the already paid original
bad-prime transport, uniformly over all clipped cells and long masks. -/
theorem boundarySourceBadMass_le (ρ : ℝ) {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    boundarySourceBadMass ρ N ε k ≤ 21*N/(N : ℝ)^(4/53 : ℝ) := by
  have had := boundarySource_admissible ρ (by omega : 2 ≤ N) ε k
  have h : boundarySourceBadMass ρ N ε k ≤ goldbachG12MainMassBad N ε := by
    unfold boundarySourceBadMass goldbachG12MainMassBad
    apply sum_le_sum
    intro m hm
    have hsub : (boundarySourceWindow ρ N ε k m).filter (fun r => ¬r.Coprime N) ⊆
        (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N) := by
      intro r hr
      obtain ⟨hr,hn⟩ := mem_filter.mp hr
      have hw := G12ClippedWindow.window_subset had hm hr
      have hp := (mem_filter.mp hw).2.1
      refine mem_filter.mpr ⟨hw,?_⟩
      by_contra hd
      exact hn (hp.coprime_iff_not_dvd.mpr hd)
    calc
      _ = boundaryCoefficient ρ N ε k m *
          (((boundarySourceWindow ρ N ε k m).filter (fun r => ¬r.Coprime N)).card : ℝ) := by
        simp [mul_comm]
      _ ≤ goldbachG12NormalizedCoefficient N m *
          (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N)).card : ℝ) :=
        mul_le_mul (had m hm).1.2 (by exact_mod_cast card_le_card hsub)
          (Nat.cast_nonneg _) (goldbachG12NormalizedCoefficient_bounds N m).1
  exact h.trans (goldbachG12MainMassBad_le hN ε)

theorem boundary_source_mass_le (ρ : ℝ) {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    G12ClippedWindow.mass N (boundaryCoefficient ρ N ε k)
      (boundarySourceLo ρ N ε k) (boundarySourceHi ρ N ε k) ≤
      (∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1) +
        21*N/(N : ℝ)^(4/53 : ℝ) := by
  rw [boundary_source_mass_split ρ (by omega : 1 ≤ N) ε k]
  exact add_le_add le_rfl (boundarySourceBadMass_le ρ hN ε k)

/-- This is payment of the physical/source coprimality transport, not payment
of the roughness boundary or of the ordinary output sieve. -/
theorem boundarySourceBadMass_log_saving (B : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ρ ε : ℝ) (k : ℕ × ℕ),
      400*boundarySourceBadMass ρ N ε k ≤ N/Real.log (N : ℝ)^B := by
  obtain ⟨J,hJ,hb⟩ := G12RectangleGate.numerical_log_saving B
  have hl : ∀ᶠ N : ℕ in Filter.atTop, (4 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 4)
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max J L,by omega,?_⟩
  intro N hN ρ ε k
  have hN4 : 4 ≤ N := by omega
  have hlog := hL N (by omega)
  have hfac : (400 : ℝ)*21 ≤ 800*(1+Real.log (N : ℝ))^2 := by nlinarith
  have hn : 0 ≤ (N : ℝ)/(N : ℝ)^(4/53 : ℝ) := by positivity
  calc
    _ ≤ 400*(21*N/(N : ℝ)^(4/53 : ℝ)) :=
      mul_le_mul_of_nonneg_left (boundarySourceBadMass_le ρ hN4 ε k) (by norm_num)
    _ ≤ (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 := by
      have h := mul_le_mul_of_nonneg_right hfac hn
      convert h using 1 <;> first | rfl | ring
    _ ≤ _ := hb N (by omega)

end G12FineGrid
