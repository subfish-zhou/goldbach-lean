import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralEventual

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Quantitative oscillation of the continuous weighted kernel on the ambient
box. The bound is independent of N and therefore usable before selecting N₀. -/
theorem fouvryG9RelaxedIntegral_continuous_corner_error {u v x y m : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hux : u ≤ x) (hvy : v ≤ y)
    (hx : x ≤ 1/3) (hy : y ≤ 1/2) (hm : 0 ≤ m)
    (hdx : x-u ≤ m) (hdy : y-v ≤ m) :
    1/((1-x-y)*(1-x)) ≤ 1/((1-u-v)*(1-u)) + 243*m := by
  let A := (1-x-y)*(1-x)
  let B := (1-u-v)*(1-u)
  have hga : (1/6 : ℝ) ≤ 1-x-y := by linarith
  have hta : (2/3 : ℝ) ≤ 1-x := by linarith
  have ha : (1/9 : ℝ) ≤ A := by
    have := mul_le_mul hga hta (by norm_num) (by linarith : 0 ≤ 1-x-y)
    dsimp [A]; nlinarith
  have hgab : 1-x-y ≤ 1-u-v := by linarith
  have htab : 1-x ≤ 1-u := by linarith
  have hab : A ≤ B := mul_le_mul hgab htab (by linarith) (by linarith)
  have hb : (1/9 : ℝ) ≤ B := ha.trans hab
  have hap : 0 < A := by linarith
  have hbp : 0 < B := by linarith
  have habprod : (1/81 : ℝ) ≤ A*B := by
    have := mul_le_mul ha hb (by norm_num) hap.le
    nlinarith
  have hdiff : B-A ≤ 3*m := by
    have h1 := mul_nonneg (sub_nonneg.mpr hux) (show 0 ≤ u+x+v by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hvy) (show 0 ≤ x by linarith)
    dsimp [A, B]
    nlinarith
  have herror : (B-A)/(A*B) ≤ 243*m := by
    apply (div_le_iff₀ (mul_pos hap hbp)).mpr
    have := mul_le_mul_of_nonneg_left habprod (show 0 ≤ 243*m by positivity)
    nlinarith
  have heq : 1/A-1/B = (B-A)/(A*B) := by field_simp
  change 1/A ≤ 1/B+243*m
  rw [← heq] at herror
  linarith

/-- All cells selected by the finite cover lie in explicit thin enlargements
of the four source boundaries. This isolates the remaining measure estimate. -/
theorem fouvryG9RelaxedIntegral_selected_cell_geometry {n : ℕ} {h u v : ℝ}
    (q : Fin n × Fin n) (hq : q ∈ fouvryG9RelaxedIntegralCells n h)
    (hu : u ∈ Set.Ioc (goldbachB9AlphaGridPoint n q.1)
      (goldbachB9AlphaGridPoint n (q.1+1)))
    (hv : v ∈ Set.Ioc (goldbachB9BetaGridPoint n q.2)
      (goldbachB9BetaGridPoint n (q.2+1))) :
    4/53-goldbachB9AlphaGridStep n < u ∧
    u < 1/10+goldbachB9AlphaGridStep n ∧
    1/3-goldbachB9BetaGridStep n < v ∧
    u+2*v < 1+h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n := by
  classical
  obtain ⟨_, ha, hb, hc, hd⟩ := Finset.mem_filter.mp hq
  rw [goldbachB9AlphaGridPoint_succ] at ha
  rw [goldbachB9BetaGridPoint_succ] at hc
  have huu := hu.2
  have hvv := hv.2
  rw [goldbachB9AlphaGridPoint_succ] at huu
  rw [goldbachB9BetaGridPoint_succ] at hvv
  exact ⟨by linarith [hu.1], by linarith, by linarith [hv.1], by linarith⟩

#print axioms fouvryG9RelaxedIntegral_continuous_corner_error
#print axioms fouvryG9RelaxedIntegral_selected_cell_geometry
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
