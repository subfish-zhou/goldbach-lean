import MathlibNt.Wu2008DoubleSieve.FourRoughClosedMass

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Set Real LiLiuPrereqBuchstab TruncatedFourPhysical
open scoped Classical
noncomputable section

def coord (N p : ℕ) : ℝ := log (p : ℝ) / log (N : ℝ)
def parameter (x y z t : ℝ) : ℝ := (1-x-y-z-t)/y
def density (x y z t : ℝ) : ℝ := buchstab (parameter x y z t)/y
def clippedDensity (x y z t : ℝ) : ℝ := buchstab (max 2 (parameter x y z t))/y
def kernel (x y z t : ℝ) : ℝ := buchstab (parameter x y z t)/(x*y^2*z*t)

theorem fixed_geometry :
    (1/15 : ℝ) ≤ alpha ∧ 0 < alpha ∧ alpha ≤ beta ∧ beta ≤ 1/3 ∧
    6*beta < 1 ∧ 4*beta+lam < 1 ∧ 2*beta ≤ lam ∧ lam-alpha ≤ 1/3 := by
  norm_num [alpha, beta, lam, truncatedSixthLowerAlpha, truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem coord_bounds {N p : ℕ} (hN : 1 < N) (hp : 0 < p) {v w : ℝ}
    (hv : (N : ℝ)^v ≤ p) (hw : (p : ℝ) ≤ (N : ℝ)^w) :
    coord N p ∈ Icc v w := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hl := log_le_log (rpow_pos_of_pos hN0 v) hv
  have hu := log_le_log hp0 hw
  rw [log_rpow hN0] at hl hu
  exact ⟨(le_div_iff₀ hlog).mpr hl, (div_le_iff₀ hlog).mpr hu⟩

theorem coord_mono {N a b : ℕ} (hN : 1 < N) (ha : 0 < a) (hab : a ≤ b) :
    coord N a ≤ coord N b := by
  apply div_le_div_of_nonneg_right
  · exact log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  · exact (log_pos (by exact_mod_cast hN)).le

theorem ten_coordinates {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels10 N) :
    alpha ≤ coord N a ∧ coord N a ≤ coord N b ∧ coord N b ≤ coord N c ∧
    coord N c ≤ coord N d ∧ coord N d ≤ beta := by
  have hw : 0 ≤ (N : ℝ)^beta := rpow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨ha,hb,hc,hd⟩ := mem_labels.mp hq
  obtain ⟨hpa,hla,hua⟩ := (mem_primesIcc hw).mp ha
  obtain ⟨hpb,hlab,hub⟩ := (mem_primesIcc hw).mp hb
  obtain ⟨hpc,hlbc,huc⟩ := (mem_primesIcc hw).mp hc
  obtain ⟨hpd,hlcd,hud⟩ := (mem_primesIcc hw).mp hd
  have hld := hla.trans (hlab.trans (hlbc.trans hlcd))
  exact ⟨(coord_bounds hN hpa.pos hla hua).1,
    coord_mono hN hpa.pos (by exact_mod_cast hlab),
    coord_mono hN hpb.pos (by exact_mod_cast hlbc),
    coord_mono hN hpc.pos (by exact_mod_cast hlcd),
    (coord_bounds hN hpd.pos hld hud).2⟩

theorem eleven_coordinates {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels11 N) :
    alpha ≤ coord N a ∧ coord N a ≤ coord N b ∧ coord N b ≤ coord N c ∧
    coord N c ≤ beta ∧ beta ≤ coord N d ∧ coord N d ≤ lam-coord N c := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hw : 0 ≤ (N : ℝ)^beta := rpow_nonneg (Nat.cast_nonneg N) _
  have hv : 0 ≤ (N : ℝ)^lam / c := div_nonneg (rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg c)
  obtain ⟨ha,hb,hc,hd⟩ := mem_labels.mp hq
  obtain ⟨hpa,hla,hua⟩ := (mem_primesIcc hw).mp ha
  obtain ⟨hpb,hlab,hub⟩ := (mem_primesIcc hw).mp hb
  obtain ⟨hpc,hlbc,huc⟩ := (mem_primesIcc hw).mp hc
  obtain ⟨hpd,hld,hud⟩ := (mem_primesIcc hv).mp hd
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hpc.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hpd.pos
  have hlo := log_le_log (rpow_pos_of_pos hN0 beta) hld
  rw [log_rpow hN0] at hlo
  have hup := log_le_log hd0 hud
  rw [log_div (rpow_pos_of_pos hN0 lam).ne' hc0.ne', log_rpow hN0] at hup
  refine ⟨(coord_bounds hN hpa.pos hla hua).1,
    coord_mono hN hpa.pos (by exact_mod_cast hlab),
    coord_mono hN hpb.pos (by exact_mod_cast hlbc),
    (coord_bounds hN hpc.pos (hla.trans (hlab.trans hlbc)) huc).2,
    (le_div_iff₀ hlog).mpr hlo, ?_⟩
  dsimp [coord]
  apply (div_le_iff₀ hlog).mpr
  calc
    log (d : ℝ) ≤ lam*log N-log c := hup
    _ = (lam-log c/log N)*log N := by field_simp

theorem ten_parameter {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzt : z ≤ t) (ht : t ≤ beta) :
    2 ≤ parameter x y z t := by
  have hy : 0 < y := fixed_geometry.2.1.trans_le (hx.trans hxy)
  apply (le_div_iff₀ hy).mpr
  have hf := fixed_geometry.2.2.2.2.1
  linarith

theorem eleven_parameter {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (ht : t ≤ lam-z) : 2 ≤ parameter x y z t := by
  have hy : 0 < y := fixed_geometry.2.1.trans_le (hx.trans hxy)
  apply (le_div_iff₀ hy).mpr
  have hf := fixed_geometry.2.2.2.2.2.1
  linarith

theorem ten_clip_identity {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzt : z ≤ t) (ht : t ≤ beta) :
    clippedDensity x y z t = density x y z t := by
  simp only [clippedDensity, density, max_eq_right (ten_parameter hx hxy hyz hzt ht)]

theorem eleven_clip_identity {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (ht : t ≤ lam-z) : clippedDensity x y z t = density x y z t := by
  simp only [clippedDensity, density, max_eq_right (eleven_parameter hx hxy hyz hz ht)]

/-- Four prime densities and one additional rough density give y squared. -/
theorem kernel_identity (x y z t : ℝ) :
    density x y z t / (x*y*z*t) = kernel x y z t := by
  unfold density kernel
  rw [div_div]
  congr 1
  ring

theorem actual_parameters {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels10 N ∪ labels11 N) :
    alpha ≤ coord N b ∧
    2 ≤ parameter (coord N a) (coord N b) (coord N c) (coord N d) := by
  rcases mem_union.mp hq with ht | ht
  · obtain ⟨ha,hab,hbc,hcd,hd⟩ := ten_coordinates hN ht
    exact ⟨ha.trans hab, ten_parameter ha hab hbc hcd hd⟩
  · obtain ⟨ha,hab,hbc,hc,_,hd⟩ := eleven_coordinates hN ht
    exact ⟨ha.trans hab, eleven_parameter ha hab hbc hc hd⟩

theorem actual_low_window {N a b c d : ℕ} (hN : 1 < N)
    (hq : (a,b,c,d) ∈ labels10 N ∪ labels11 N) :
    coord N a ∈ Icc (1/15 : ℝ) (1/3) ∧ coord N b ∈ Icc (1/15 : ℝ) (1/3) ∧
    coord N c ∈ Icc (1/15 : ℝ) (1/3) ∧ coord N d ∈ Icc (1/15 : ℝ) (1/3) := by
  obtain ⟨hlo,_,_,hhi,_,_,_,hlam⟩ := fixed_geometry
  rcases mem_union.mp hq with ht | ht
  · obtain ⟨ha,hab,hbc,hcd,hd⟩ := ten_coordinates hN ht
    constructor
    · constructor <;> linarith
    constructor
    · constructor <;> linarith
    constructor <;> constructor <;> linarith
  · obtain ⟨ha,hab,hbc,hc,hbd,hd⟩ := eleven_coordinates hN ht
    constructor
    · constructor <;> linarith
    constructor
    · constructor <;> linarith
    constructor <;> constructor <;> linarith

end
end Wu2008DoubleSieve.FourRoughClosedMass
