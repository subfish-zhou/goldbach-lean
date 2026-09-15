import MathlibNt.Wu2008DoubleSieve.FourRoughNestedQuadrature

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Set Real MeasureTheory LiLiuPrereqBuchstab TruncatedFourPhysical
open scoped Classical
noncomputable section

def labelSet (N : ℕ) (e : Bool) : Finset Quad :=
  labels N (fun c => if e then (N : ℝ)^beta else c)
    (fun c => if e then (N : ℝ)^lam/c else (N : ℝ)^beta)

theorem labelSet_eq (N : ℕ) (e : Bool) :
    labelSet N e = if e then labels11 N else labels10 N := by
  cases e <;> rfl

theorem mainMass_nested (N : ℕ) (l u : ℕ → ℝ) :
    mainMass N (labels N l u) =
      ∑ a ∈ primesIcc ((N : ℝ)^alpha) ((N : ℝ)^beta),
      ∑ b ∈ primesIcc a ((N : ℝ)^beta),
      ∑ c ∈ primesIcc b ((N : ℝ)^beta),
      ∑ d ∈ primesIcc (l c) (u c),
        density (coord N a) (coord N b) (coord N c) (coord N d)/(a*b*c*d : ℝ) := by
  simp only [mainMass, labels, sum_map, sum_sigma, mainTerm, fourModulusProduct, Nat.cast_mul]
  rfl

theorem rpow_coord {N p : ℕ} (hN : 1 < N) (hp : 0 < p) :
    (N : ℝ)^(coord N p) = p := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  rw [rpow_def_of_pos hn]
  have he : log (N : ℝ)*coord N p = log p := by unfold coord; field_simp
  rw [he,exp_log hp']

theorem prime_row_coord {N p q : ℕ} (hN : 1 < N)
    (hp : coord N p ∈ Icc alpha beta) (hpp : 0 < p)
    (hq : q ∈ primesIcc p ((N : ℝ)^beta)) : coord N q ∈ Icc alpha beta := by
  rw [← rpow_coord hN hpp] at hq
  have hc := closed_coord hN hq
  exact ⟨hp.1.trans hc.1,hc.2⟩

theorem last_windows {N c : ℕ} (hN : 1 < N) (hc : 0 < c)
    (hcoord : coord N c ∈ Icc alpha beta) (e : Bool) :
    (N : ℝ)^(lower e (coord N c)) = (if e then (N : ℝ)^beta else c) ∧
    (N : ℝ)^(upper e (coord N c)) = (if e then (N : ℝ)^lam/c else (N : ℝ)^beta) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  cases e
  · simp only [lower,upper,Bool.false_eq_true,↓reduceIte,cap_eq hcoord]
    exact ⟨rpow_coord hN hc, trivial⟩
  · simp only [lower,upper,↓reduceIte,cap_eq hcoord]
    exact ⟨trivial, by rw [rpow_sub hn, rpow_coord hN hc]⟩

theorem F_actual {N a b c d : ℕ} (hN : 1 < N) (e : Bool)
    (hq : (a,b,c,d) ∈ labelSet N e) :
    F (coord N a) (coord N b) (coord N c) (coord N d) =
      density (coord N a) (coord N b) (coord N c) (coord N d) := by
  rw [labelSet_eq] at hq
  cases e
  · change (a,b,c,d) ∈ labels10 N at hq
    obtain ⟨ha,hab,hbc,hcd,hd⟩ := ten_coordinates hN hq
    rw [F,cap_eq ⟨ha,hab.trans (hbc.trans (hcd.trans hd))⟩,
      cap_eq ⟨ha.trans hab,hbc.trans (hcd.trans hd)⟩,
      cap_eq ⟨ha.trans (hab.trans hbc),hcd.trans hd⟩]
    exact ten_clip_identity ha hab hbc hcd hd
  · change (a,b,c,d) ∈ labels11 N at hq
    obtain ⟨ha,hab,hbc,hc,_,hd⟩ := eleven_coordinates hN hq
    rw [F,cap_eq ⟨ha,hab.trans (hbc.trans hc)⟩,
      cap_eq ⟨ha.trans hab,hbc.trans hc⟩,
      cap_eq ⟨ha.trans (hab.trans hbc),hc⟩]
    exact eleven_clip_identity ha hab hbc hc hd

theorem coord_eq_log (N p : ℕ) : coord N p = log (p : ℝ) / log (N : ℝ) := rfl

/-- Exact equality of the frozen arithmetic mass and the four closed sums. -/
theorem mainMass_eq_Q0 {N : ℕ} (hN : 1 < N) (e : Bool) :
    mainMass N (labelSet N e) = Q0 N e := by
  rw [labelSet, mainMass_nested]
  unfold Q0 primeOrderedClosedSum
  apply sum_congr rfl
  intro a ha
  have hca := closed_coord hN ha
  have hpa := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) beta)).mp ha).1
  unfold Q1 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hca,rpow_coord hN hpa.pos,sum_div]
  apply sum_congr rfl
  intro b hb
  have hcb := prime_row_coord hN hca hpa.pos hb
  have hpb := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) beta)).mp hb).1
  unfold Q2 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hcb,rpow_coord hN hpb.pos,sum_div,sum_div]
  apply sum_congr rfl
  intro c hc
  have hcc := prime_row_coord hN hcb hpb.pos hc
  have hpc := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) beta)).mp hc).1
  unfold Q3 primeOrderedClosedSum
  simp only [← coord_eq_log]
  obtain ⟨hl,hu⟩ := last_windows hN hpc.pos hcc e
  rw [hl,hu,sum_div,sum_div,sum_div]
  apply sum_congr rfl
  intro d hd
  have hq : (a,b,c,d) ∈ labelSet N e := mem_labels.mpr ⟨ha,hb,hc,hd⟩
  rw [F_actual hN e hq]
  ring

theorem J0_eq_I10 : J0 false = I10 := by
  unfold J0 J1 J2 J3 I10
  simp_rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  rw [cap_eq hx]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [uIcc_of_le hx.2] at hy
  have hy' : y ∈ Icc alpha beta := ⟨hx.1.trans hy.1,hy.2⟩
  rw [cap_eq hy']
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [uIcc_of_le hy.2] at hz
  have hz' : z ∈ Icc alpha beta := ⟨hy'.1.trans hz.1,hz.2⟩
  simp only [lower,upper,Bool.false_eq_true,↓reduceIte,cap_eq hz']
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [uIcc_of_le hz.2] at ht
  rw [F,cap_eq hx,cap_eq hy',cap_eq hz',ten_clip_identity hx.1 hy.1 hz.1 ht.1 ht.2]
  rw [← kernel_identity]
  ring

theorem J0_eq_I11 : J0 true = I11 := by
  unfold J0 J1 J2 J3 I11
  simp_rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  rw [cap_eq hx]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [uIcc_of_le hx.2] at hy
  have hy' : y ∈ Icc alpha beta := ⟨hx.1.trans hy.1,hy.2⟩
  rw [cap_eq hy']
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [uIcc_of_le hy.2] at hz
  have hz' : z ∈ Icc alpha beta := ⟨hy'.1.trans hz.1,hz.2⟩
  simp only [lower,upper,↓reduceIte,cap_eq hz']
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hb : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1,hz.2]
  rw [uIcc_of_le hb] at ht
  rw [F,cap_eq hx,cap_eq hy',cap_eq hz',eleven_clip_identity hx.1 hy.1 hz.1 hz.2 ht.2]
  rw [← kernel_identity]
  ring

end
end Wu2008DoubleSieve.FourRoughClosedMass
