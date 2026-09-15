import Wu08SmallRoughFibres

noncomputable section
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

/-- Uniform physical size information for every relaxed labelled fibre. -/
theorem rough_geometry {N : ℕ} {e : Bool} {ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {q : Quad} (hq : q ∈ relaxedQuads N e ρ) :
    roughX N ρ q ≤ N ∧ (q.2.1 : ℝ) ≤ roughX N ρ q ∧
    (N : ℝ)^truncatedSixthLowerAlpha/2 ≤ (q.2.1 : ℝ) ∧
    q.2.1.Prime ∧ 0 < quadProduct q := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  obtain ⟨ha,hb,hc,hd,hn,hr,hD,hnF⟩ := relaxed_data hN hρ hp
  obtain ⟨_,hz,_,hab,_⟩ := mem_filter.mp hp
  have hρ0 : 0 < ρ := by linarith
  have hb0 : (0 : ℝ) ≤ p.1.1 := Nat.cast_nonneg _
  have hD8 : 8 ≤ quadProduct (quadOf p) := by
    change 8 ≤ p.2*p.1.1*p.1.2.1*p.1.2.2.1
    have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (show 1 ≤ p.2 by omega) hb.two_le) hc.two_le) hd.two_le
    exact hh
  have hD0 : (0 : ℝ) < quadProduct (quadOf p) := by exact_mod_cast hD
  have hDρ : ρ ≤ (quadProduct (quadOf p) : ℝ) := by
    have hh : (8 : ℝ) ≤ quadProduct (quadOf p) := by exact_mod_cast hD8
    linarith
  have hnx := (mem_roughNumbers.mp (mem_erase.mp hnF).2).2.1
  have hbn : (p.1.1 : ℝ) ≤ p.1.2.2.2 := by
    have hmin := (rough_iff_minFac (by omega : p.1.2.2.2 ≠ 1)).mp hr
    exact hmin.trans (by exact_mod_cast Nat.minFac_le_of_dvd (by omega : 2 ≤ p.1.2.2.2) (dvd_refl p.1.2.2.2))
  refine ⟨?_,hbn.trans hnx,?_,hb,hD⟩
  · unfold roughX
    apply (div_le_iff₀ hD0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hDρ (Nat.cast_nonneg N)]
  · have hz' := (div_le_iff₀ hρ0).mp hz
    have hh := mul_lt_mul_of_pos_right hab hρ0
    have hr2 : ρ*ρ ≤ (2 : ℝ) := by nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hr2 hb0
    change (N : ℝ)^truncatedSixthLowerAlpha ≤ (p.2 : ℝ)*ρ at hz'
    dsimp only [quadOf]
    nlinarith only [hz',hh,hh2]

/-- True four-prime labelled Buchstab main sum after uniform rough counting.
The extra logarithmic b factor is retained, before prime quadrature supplies
the second b-coordinate denominator. -/
def buchstabGrid (N : ℕ) (e : Bool) (ρ ε τ : ℝ) : ℝ :=
  ∑ q ∈ relaxedQuads N e ρ, quadWeight N ε q*
    (buchstab (log (roughX N ρ q)/log (q.2.1 : ℝ))+τ)/
      ((quadProduct q : ℝ)*(log (q.2.1 : ℝ)/log N))

theorem uniform_rough_fibres {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) →
    ∀ e : Bool, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
    ∀ q ∈ relaxedQuads N e ρ,
      ((roughFibre N ρ q).card : ℝ) ≤
        (buchstab (log (roughX N ρ q)/log (q.2.1 : ℝ))+τ)*roughX N ρ q/log (q.2.1 : ℝ) := by
  have hα : 0 < truncatedSixthLowerAlpha/2 := by norm_num [truncatedSixthLowerAlpha]
  obtain ⟨Tu,hTu,hu⟩ := NonunitRoughUniform.uniform_upper hα hτ
  obtain ⟨Tp,hp⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 2 0 (truncatedSixthLowerAlpha/2) hα)
  refine ⟨max 4 (max (Tu : ℝ) Tp),le_max_left _ _,?_⟩
  intro N hN e ρ hρ hρu q hq
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNu : Tu ≤ N := by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNp : Tp ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hxN,hyx,hy,_,_⟩ := rough_geometry hn4 hρ hρu hq
  have hroot : (2 : ℝ) ≤ (N : ℝ)^(truncatedSixthLowerAlpha/2) := by simpa using hp N hNp
  have hsquare : (N : ℝ)^truncatedSixthLowerAlpha =
      (N : ℝ)^(truncatedSixthLowerAlpha/2)*(N : ℝ)^(truncatedSixthLowerAlpha/2) := by
    rw [← rpow_add (by linarith : (0 : ℝ)<N)]
    congr 1
    ring
  have hy' : (N : ℝ)^(truncatedSixthLowerAlpha/2) ≤ (q.2.1 : ℝ) := by
    rw [hsquare] at hy
    nlinarith
  exact (hu N hNu _ _ hxN hy').2 hyx

/-- Both arithmetic losses epsilon and tau remain explicit. The threshold
is uniform in rho, e and every actual relaxed four-prime label. -/
theorem roughMass_buchstab {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) →
    ∀ e : Bool, ∀ ρ ε : ℝ, 1 < ρ → ρ ≤ 5/4 → 0 ≤ ε →
      roughMass N e ρ ε ≤ (ρ*(N : ℝ)/log N)*buchstabGrid N e ρ ε τ := by
  obtain ⟨T,hT,ht⟩ := uniform_rough_fibres hτ
  refine ⟨T,hT,?_⟩
  intro N hN e ρ ε hρ hρu hε
  have hn4 : (4 : ℝ) ≤ N := hT.trans hN
  have hln : 0 < log (N : ℝ) := log_pos (by linarith)
  unfold roughMass buchstabGrid
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  have hw : 0 ≤ quadWeight N ε q :=
    mul_nonneg (add_nonneg (atomWeight_nonneg N q.1) hε) (beta_nonneg N q.1)
  have hh := mul_le_mul_of_nonneg_left (ht N hN e ρ hρ hρu q hq) hw
  have hg := rough_geometry hn4 hρ hρu hq
  have hD : (quadProduct q : ℝ) ≠ 0 := by exact_mod_cast hg.2.2.2.2.ne'
  have hlb : log (q.2.1 : ℝ) ≠ 0 :=
    (log_pos (by exact_mod_cast hg.2.2.2.1.one_lt)).ne'
  exact hh.trans_eq (by unfold roughX; field_simp)

#print axioms uniform_rough_fibres
#print axioms roughMass_buchstab
end Wu08FirstPrimeFour.SmallGrid
