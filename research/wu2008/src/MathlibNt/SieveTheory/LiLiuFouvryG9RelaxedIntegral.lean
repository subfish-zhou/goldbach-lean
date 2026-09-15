import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedMass
import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGrid
import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction

noncomputable section
open scoped BigOperators Topology
open Filter Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniformly positive denominators on a slightly enlarged low strip. -/
theorem fouvryG9RelaxedIntegral_denominators {u v w δ : ℝ}
    (hu : u ≤ 1/10) (hv : u + 2*v ≤ 1 + 1/20)
    (hw : 1 ≤ w) (hδ : δ ≤ 1/4) :
    17/40 ≤ 1-u-v ∧ 17/40 ≤ w-u-v ∧
      1/4 ≤ (5/9 : ℝ)*(1-u)-δ := by
  constructor
  · linarith
  constructor <;> linarith

/-- The moving first denominator is safely replaced by the smaller static one. -/
theorem fouvryG9RelaxedIntegral_static_majorant {r s u v w δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hu : u ≤ 1/10)
    (hv : u + 2*v ≤ 1 + 1/20) (hw : 1 ≤ w) (hδ : δ ≤ 1/4) :
    1 / (r*s*(w-u-v)*((5/9 : ℝ)*(1-u)-δ)) ≤
      1 / (r*s*(1-u-v)*((5/9 : ℝ)*(1-u)-δ)) := by
  obtain ⟨hgap, _, hweight⟩ := fouvryG9RelaxedIntegral_denominators hu hv hw hδ
  have hg : 0 < 1-u-v := by linarith
  have ht : 0 < (5/9 : ℝ)*(1-u)-δ := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : 1-u-v ≤ w-u-v)
      (mul_pos hr hs).le) ht.le

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle PrimeReciprocalLogScale

/-- The literal production weighted low integral (the production API is a theorem,
not a constant named `goldbachB9WeightedSubintervalIntegral`). -/
def fouvryG9RelaxedIntegralLow : ℝ :=
  ∫ u in (4/53 : ℝ)..(1/10),
    ∫ v in (1/3 : ℝ)..((1-u)/2), 1/(u*v*(1-u-v)*(1-u))

theorem fouvryG9RelaxedIntegralLow_eq_single :
    fouvryG9RelaxedIntegralLow =
      ∫ u in (4/53 : ℝ)..(1/10), Real.log (2-3*u)/(u*(1-u)^2) := by
  exact goldbachB9WeightedSubintervalIntegral_eq_single (by norm_num)
    (by norm_num) (by norm_num)

/-- Exact logarithmic geometry of the actual relaxed carrier. -/
theorem fouvryG9RelaxedIntegral_geometry {N : ℕ} {ρ : ℝ}
    (hN : 2 ≤ N) (hρ : 1 < ρ) {rs : ℕ × ℕ}
    (hrs : rs ∈ fouvryG9RelaxedPairs N ρ) :
    (4/53 : ℝ) ≤ primeLogExponent N rs.1 ∧
    primeLogExponent N rs.1 < (1/10 : ℝ) ∧
    (1/3 : ℝ) ≤ primeLogExponent N rs.2 ∧
    primeLogExponent N rs.1 + 2*primeLogExponent N rs.2 ≤
      1+3*Real.log ρ/Real.log (N : ℝ) := by
  obtain ⟨_, hr, hs, hcut, hrupper, hslower, hprod⟩ := Finset.mem_filter.mp hrs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast hr.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hρp : 0 < ρ := by linarith
  have hcutlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hcut
  have hrlog := Real.log_lt_log hrp hrupper
  have hslog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hslower
  rw [Real.log_rpow hNp] at hcutlog hrlog hslog
  have hprodlog := Real.log_le_log (mul_pos hrp (pow_pos hsp 2)) hprod
  rw [Real.log_mul hrp.ne' (pow_ne_zero 2 hsp.ne'), Real.log_pow,
    Real.log_mul (pow_ne_zero 3 hρp.ne') hNp.ne', Real.log_pow] at hprodlog
  refine ⟨(le_div_iff₀ hln).mpr hcutlog, (div_lt_iff₀ hln).mpr hrlog,
    (le_div_iff₀ hln).mpr hslog, ?_⟩
  unfold primeLogExponent
  apply (le_of_mul_le_mul_right ?_ hln)
  field_simp
  norm_num at hprodlog
  linarith

/-- The grid is fixed before N; h is a fixed boundary-strip width. -/
def fouvryG9RelaxedIntegralCells (n : ℕ) (h : ℝ) : Finset (Fin n × Fin n) := by
  classical
  exact univ.filter fun q =>
    (4/53 : ℝ) ≤ goldbachB9AlphaGridPoint n (q.1+1) ∧
    goldbachB9AlphaGridPoint n q.1 < (1/10 : ℝ) ∧
    (1/3 : ℝ) ≤ goldbachB9BetaGridPoint n (q.2+1) ∧
    goldbachB9AlphaGridPoint n q.1 + 2*goldbachB9BetaGridPoint n q.2 < 1+h

def fouvryG9RelaxedIntegralCorner (n : ℕ) (δ : ℝ) (q : Fin n × Fin n) : ℝ :=
  1 / ((1-goldbachB9AlphaGridPoint n (q.1+1)-goldbachB9BetaGridPoint n (q.2+1))*
    ((5/9 : ℝ)*(1-goldbachB9AlphaGridPoint n (q.1+1))-δ))

def fouvryG9RelaxedIntegralGrid (n N : ℕ) (h δ : ℝ) : ℝ :=
  ∑ q ∈ fouvryG9RelaxedIntegralCells n h, fouvryG9RelaxedIntegralCorner n δ q *
    primeReciprocalLogRectangle N
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))

def fouvryG9RelaxedIntegralUpperSum (n : ℕ) (h δ : ℝ) : ℝ :=
  ∑ q ∈ fouvryG9RelaxedIntegralCells n h, fouvryG9RelaxedIntegralCorner n δ q *
    logarithmicRectangleMass
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))

theorem fouvryG9RelaxedIntegral_fixed_grid_tendsto (n : ℕ) (hn : 0 < n) (h δ : ℝ) :
    Tendsto (fun N => fouvryG9RelaxedIntegralGrid n N h δ) atTop
      (nhds (fouvryG9RelaxedIntegralUpperSum n h δ)) := by
  unfold fouvryG9RelaxedIntegralGrid fouvryG9RelaxedIntegralUpperSum
  apply tendsto_weighted_sum_primeReciprocalLogRectangle
  · intro q _; exact goldbachB9AlphaGridPoint_pos n q.1
  · intro q _; exact goldbachB9AlphaGridPoint_lt_succ hn
  · intro q _; exact goldbachB9BetaGridPoint_pos n q.2
  · intro q _; exact goldbachB9BetaGridPoint_lt_succ hn

/-- Every closed lower boundary is captured inside a left-open grid cell. -/
theorem fouvryG9RelaxedIntegral_cover (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N)
    {ρ h : ℝ} (hρ : 1 < ρ) (hh : h ≤ 1/20)
    (hw : 1+3*Real.log ρ/Real.log (N : ℝ) ≤ 1+h)
    {rs : ℕ × ℕ} (hrs : rs ∈ fouvryG9RelaxedPairs N ρ) :
    ∃ q ∈ fouvryG9RelaxedIntegralCells n h,
      LiuPairInLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1)) rs := by
  obtain ⟨hlow, hfirst, hsecond, htriangle⟩ := fouvryG9RelaxedIntegral_geometry hN hρ hrs
  have halow : (1/20 : ℝ) < primeLogExponent N rs.1 := by linarith
  have hblow : (1/4 : ℝ) < primeLogExponent N rs.2 := by linarith
  have haup : primeLogExponent N rs.1 ≤ 1/20+(n : ℝ)*goldbachB9AlphaGridStep n := by
    rw [← goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_end hn]
    linarith
  have hbup : primeLogExponent N rs.2 ≤ 1/4+(n : ℝ)*goldbachB9BetaGridStep n := by
    rw [← goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_end hn]
    linarith
  obtain ⟨i, hi, hail, haiu⟩ := exists_nat_cell n (goldbachB9AlphaGridStep_pos hn) halow haup
  obtain ⟨j, hj, hbjl, hbju⟩ := exists_nat_cell n (goldbachB9BetaGridStep_pos hn) hblow hbup
  have hal : goldbachB9AlphaGridPoint n i < primeLogExponent N rs.1 := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using hail
  have hau : primeLogExponent N rs.1 ≤ goldbachB9AlphaGridPoint n (i+1) := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using haiu
  have hbl : goldbachB9BetaGridPoint n j < primeLogExponent N rs.2 := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbjl
  have hbu : primeLogExponent N rs.2 ≤ goldbachB9BetaGridPoint n (j+1) := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbju
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_, ⟨hal, hau, hbl, hbu⟩⟩
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hlow.trans hau, hal.trans hfirst, hsecond.trans hbu, by dsimp; linarith⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
