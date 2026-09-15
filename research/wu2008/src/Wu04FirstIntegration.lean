import Wu04FirstClassical

namespace Wu04FirstIntegration
open Wu2008DoubleSieve Set MeasureTheory
noncomputable section

/-- Continuity for arbitrary continuous lower c-boundaries, including b and a fixed cut. -/
theorem inner_cont {F : ℝ→ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ×ℝ => F p.1 p.2.1 p.2.2))
    {v : ℝ×ℝ→ℝ} (hv : Continuous v) (h : ℝ) :
    Continuous (fun p : ℝ×ℝ => ∫ c in v p..h,F p.1 p.2 c) :=
  Omega3ElementaryRegularity.continuous_moving
    (hF.comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
    hv continuous_const

theorem outer_cont {F : ℝ→ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ×ℝ => F p.1 p.2.1 p.2.2))
    {v : ℝ×ℝ→ℝ} (hv : Continuous v) (r h : ℝ) :
    Continuous (fun a => ∫ b in a..r,∫ c in v (a,b)..h,F a b c) :=
  Omega3ElementaryRegularity.continuous_moving (inner_cont hF hv h) continuous_id continuous_const

/-- Triple integral linearity with genuinely moving ordered endpoints. -/
theorem ordered_sub {F G : ℝ→ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ×ℝ => F p.1 p.2.1 p.2.2))
    (hG : Continuous (fun p : ℝ×ℝ×ℝ => G p.1 p.2.1 p.2.2)) (l h : ℝ) :
    (∫ a in l..h,∫ b in a..h,∫ c in b..h,F a b c-G a b c)=
    (∫ a in l..h,∫ b in a..h,∫ c in b..h,F a b c)-
    (∫ a in l..h,∫ b in a..h,∫ c in b..h,G a b c) := by
  have hi (a b : ℝ) : (∫ c in b..h,F a b c-G a b c)=
      (∫ c in b..h,F a b c)-(∫ c in b..h,G a b c) :=
    intervalIntegral.integral_sub
      ((hF.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).intervalIntegrable _ _)
      ((hG.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).intervalIntegrable _ _)
  have hm (a : ℝ) : (∫ b in a..h,(∫ c in b..h,F a b c)-(∫ c in b..h,G a b c))=
      (∫ b in a..h,∫ c in b..h,F a b c)-(∫ b in a..h,∫ c in b..h,G a b c) :=
    intervalIntegral.integral_sub
      (((inner_cont hF continuous_snd h).comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).intervalIntegrable _ _)
      (((inner_cont hG continuous_snd h).comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).intervalIntegrable _ _)
  simp_rw [hi,hm]
  exact intervalIntegral.integral_sub
    ((outer_cont hF continuous_snd h h).intervalIntegrable _ _)
    ((outer_cont hG continuous_snd h h).intervalIntegrable _ _)

/-- Monotonicity on the retained actual triangular-times-interval subdomain. -/
theorem block_mono {F G : ℝ→ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ×ℝ => F p.1 p.2.1 p.2.2))
    (hG : Continuous (fun p : ℝ×ℝ×ℝ => G p.1 p.2.1 p.2.2))
    {l r h : ℝ} (hlr : l≤r) (hrh : r≤h)
    (hp : ∀ a∈Icc l r,∀ b∈Icc a r,∀ c∈Icc r h,F a b c≤G a b c) :
    (∫ a in l..r,∫ b in a..r,∫ c in r..h,F a b c)≤
      ∫ a in l..r,∫ b in a..r,∫ c in r..h,G a b c := by
  apply intervalIntegral.integral_mono_on hlr
    ((outer_cont hF (continuous_const (y:=r)) r h).intervalIntegrable _ _)
    ((outer_cont hG (continuous_const (y:=r)) r h).intervalIntegrable _ _)
  intro a ha
  apply intervalIntegral.integral_mono_on ha.2
    (((inner_cont hF (continuous_const (y:=r)) h).comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).intervalIntegrable _ _)
    (((inner_cont hG (continuous_const (y:=r)) h).comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).intervalIntegrable _ _)
  intro b hb
  exact intervalIntegral.integral_mono_on hrh
    ((hF.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).intervalIntegrable _ _)
    ((hG.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).intervalIntegrable _ _)
    (fun c hc => hp a ha b hb c hc)
end
end Wu04FirstIntegration
