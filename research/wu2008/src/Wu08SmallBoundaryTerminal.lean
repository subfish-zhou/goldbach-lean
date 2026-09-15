import Wu08SmallActualBuchstab
import Wu08LargeOriginalPairPort

noncomputable section
open Finset Real Filter Set MeasureTheory LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour.SmallBoundary
open FourRoughClosedMass SmallGrid

/-- Closed one-dimensional strips, including both integer endpoint atoms. -/
theorem closed_strip_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ a b : ℝ, a ∈ low → b ∈ low → a ≤ b →
        (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤
          15*(b-a)+ε := by
  obtain ⟨T,hT,h⟩ := SeventhEighth.classical_low_weighted_uniform 1 0 ε
    (by norm_num) (by norm_num) hε
  refine ⟨T,hT,?_⟩
  intro N hN a b ha hb hab
  have hq := h N hN (fun _ => 1) a b continuousOn_const
    (by intros; norm_num) (by intros; simp) ha.1 hab hb.2
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (15 : ℝ)) (a := a) (b := b) (f := fun t : ℝ => 1/t) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      have ht0 : 0 < t := by linarith [ha.1,ht.1]
      rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht0)]
      apply (div_le_iff₀ ht0).mpr
      linarith [ha.1,ht.1])
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  change |(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ))-
    ∫ t in a..b, (1 : ℝ)/t| < ε at hq
  linarith only [(abs_lt.mp hq).2,(le_abs_self (∫ t in a..b, (1 : ℝ)/t)).trans hi]

/-- All four-label reciprocal mass of a first-coordinate strip. -/
theorem first_strip_reciprocal {N : ℕ} {a b ε : ℝ}
    (hm : windowMass N ≤ 5) (hε : 0 ≤ ε) (hab : a ≤ b)
    (hs : (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 15*(b-a)+ε) :
    reciprocalMass (primesIcc ((N : ℝ)^a) ((N : ℝ)^b) ×ˢ
      window N ×ˢ window N ×ˢ window N) ≤ 125*(15*(b-a)+ε) := by
  have he : reciprocalMass (primesIcc ((N : ℝ)^a) ((N : ℝ)^b) ×ˢ
      window N ×ˢ window N ×ˢ window N) =
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ))*windowMass N^3 := by
    simp only [reciprocalMass,sum_product,fourModulusProduct,Nat.cast_mul,one_div,mul_inv_rev]
    simp only [← sum_mul,← mul_sum,windowMass,one_div]
    ring
  rw [he]
  have hm0 : 0 ≤ windowMass N := sum_nonneg (by intros; positivity)
  have hp : windowMass N^3 ≤ 125 := by
    exact (pow_le_pow_left₀ hm0 hm 3).trans_eq (by norm_num)
  have hpos : 0 ≤ 15*(b-a)+ε := by positivity
  nlinarith only [mul_le_mul hs hp (pow_nonneg hm0 3) hpos]

/-- The logarithmic displacement costs only the original second coordinate
squared. This statement keeps the unshifted Buchstab parameter explicit. -/
theorem shifted_density_payment {u y s τ : ℝ}
    (hu : 2 ≤ u) (hy : 1/15 ≤ y) (hs : 0 ≤ s) :
    (buchstab (u+s/y)+τ)/y ≤ buchstab u/y+225*s+15*|τ| := by
  have hy0 : 0 < y := by linarith
  have hsy : 0 ≤ s/y := div_nonneg hs hy0.le
  have hω := primeOrdered_buchstab_lipschitz (by linarith : 1 ≤ u+s/y)
    (by linarith : 1 ≤ u)
  have hd : |u+s/y-u| = s/y := by rw [show u+s/y-u=s/y by ring,abs_of_nonneg (div_nonneg hs hy0.le)]
  rw [hd] at hω
  have hω' : buchstab (u+s/y)-buchstab u ≤ s/y := (le_abs_self _).trans hω
  have hrec : 1/y ≤ 15 := (div_le_iff₀ hy0).mpr (by linarith)
  have hss : s/y/y ≤ 225*s := by
    have hh := mul_le_mul hrec hrec (by positivity : 0 ≤ 1/y) (by norm_num : (0 : ℝ) ≤ 15)
    have ht := mul_le_mul_of_nonneg_left hh hs
    calc
      _ = s*((1/y)*(1/y)) := by ring
      _ ≤ s*(15*15) := ht
      _ = _ := by ring
  have ht : τ/y ≤ 15*|τ| := by
    calc
      _ ≤ |τ|/y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ = |τ| *(1/y) := by ring
      _ ≤ |τ| *15 := mul_le_mul_of_nonneg_left hrec (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hdiv := div_le_div_of_nonneg_right hω' hy0.le
  calc
    _ = buchstab u/y+(buchstab (u+s/y)-buchstab u)/y+τ/y := by ring
    _ ≤ buchstab u/y+s/y/y+15*|τ| := add_le_add (add_le_add (le_refl _) hdiv) ht
    _ ≤ _ := by linarith only [hss]

/-- A symbolic threshold makes every permitted physical dilation logarithmically
small. No numerical logarithm or exponential is evaluated. -/
theorem log_shift_uniform {s : ℝ} (hs : 0 < s) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → 0 ≤ log ρ/log N ∧ log ρ/log N ≤ s := by
  refine ⟨max 4 (exp (log (5/4 : ℝ)/s)),le_max_left _ _,?_⟩
  intro N hN ρ hρ hρu
  have hn4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hl : 0 < log (N : ℝ) := log_pos (by linarith)
  have he : exp (log (5/4 : ℝ)/s) ≤ N := (le_max_right _ _).trans hN
  have hh := log_le_log (exp_pos (log (5/4 : ℝ)/s)) he
  rw [log_exp] at hh
  refine ⟨div_nonneg (log_nonneg hρ.le) hl.le,(div_le_iff₀ hl).mpr ?_⟩
  have hu : log ρ ≤ log (5/4 : ℝ) := log_le_log (by linarith) hρu
  have hmul := (div_le_iff₀ hs).mp hh
  nlinarith only [hu,hmul]

/-- Actual relaxed labels, with no replacement of the rough integer by a
prime. The short prime gate is read from its original beta coefficient. -/
theorem relaxed_coordinates {N : ℕ} {e : Bool} {ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) {q : SmallGrid.Quad}
    (hq : q ∈ relaxedQuads N e ρ) (hweight : Wu08FirstPrimeFour.beta N q.1 ≠ 0) :
    q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime ∧
    FourRoughClosedMass.alpha-log ρ/log N ≤ coord N q.1 ∧
    coord N q.1 ≤ 1/10+log ρ/log N ∧
    coord N q.1 ≤ coord N q.2.1+log ρ/log N ∧
    coord N q.2.1 ≤ coord N q.2.2.1 ∧ coord N q.2.2.1 ≤ FourRoughClosedMass.beta ∧
    coord N q.2.2.1 ≤ coord N q.2.2.2 ∧
    (if e then FourRoughClosedMass.beta ≤ coord N q.2.2.2 ∧
      coord N q.2.2.2 ≤ lam-coord N q.2.2.1 else coord N q.2.2.2 ≤ FourRoughClosedMass.beta) := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  obtain ⟨ha,hb,hc,hd,_,_,_,_⟩ := relaxed_data hN hρ hp
  obtain ⟨hmem,hlo,hhi,hab,_⟩ := mem_filter.mp hp
  obtain ⟨ht,_⟩ := mem_product.mp hmem
  obtain ⟨_,_,_,_,_,_,_,hbc,hcd,hcw,hwd,hcap,_,_⟩ := mem_filter.mp ht
  have hpa : p.2.Prime := by
    by_contra hh
    simp only [quadOf] at hweight
    simp [Wu08FirstPrimeFour.beta,primeSWBeta,hh] at hweight
  have hn : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hn0 : (0 : ℝ) < N := by linarith
  have hl : 0 < log (N : ℝ) := log_pos (by linarith)
  have hr0 : 0 < ρ := by linarith
  have ha0 : (0 : ℝ) < p.2 := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < p.1.1 := by exact_mod_cast hb.pos
  have hc0 : (0 : ℝ) < p.1.2.1 := by exact_mod_cast hc.pos
  have hd0 : (0 : ℝ) < p.1.2.2.1 := by exact_mod_cast hd.pos
  have hlo' := log_le_log (div_pos (rpow_pos_of_pos hn0 truncatedSixthLowerAlpha) hr0) hlo
  have hhi' := log_le_log ha0 hhi
  have hab' := log_le_log ha0 hab.le
  have hcw' := log_le_log hc0 hcw.le
  change log ((N : ℝ)^truncatedSixthLowerAlpha/ρ) ≤ _ at hlo'
  change log (p.1.2.1 : ℝ) ≤ log ((N : ℝ)^truncatedSixthLowerBeta) at hcw'
  rw [log_div (rpow_pos_of_pos hn0 _).ne' hr0.ne',log_rpow hn0] at hlo'
  rw [log_mul hr0.ne' (rpow_pos_of_pos hn0 _).ne',log_rpow hn0] at hhi'
  rw [log_mul hr0.ne' hb0.ne'] at hab'
  rw [log_rpow hn0] at hcw'
  refine ⟨hpa,hb,hc,hd,?_,?_,?_,coord_mono hn hb.pos hbc.le,?_,coord_mono hn hc.pos hcd.le,?_⟩
  · dsimp only [coord,quadOf,FourRoughClosedMass.alpha]
    apply (le_div_iff₀ hl).mpr
    calc
      _ = truncatedSixthLowerAlpha*log N-log ρ := by field_simp
      _ ≤ _ := hlo'
  · dsimp only [coord,quadOf]
    apply (div_le_iff₀ hl).mpr
    calc
      _ ≤ log ρ+(1/10 : ℝ)*log N := hhi'
      _ = _ := by field_simp; ring
  · dsimp only [coord,quadOf]
    apply (div_le_iff₀ hl).mpr
    calc
      _ ≤ log ρ+log (p.1.1 : ℝ) := hab'
      _ = _ := by field_simp; ring
  · exact (div_le_iff₀ hl).mpr hcw'
  · cases e
    · have hh := log_le_log hd0 hcap.le
      change log (p.1.2.2.1 : ℝ) ≤ log ((N : ℝ)^truncatedSixthLowerBeta) at hh
      rw [log_rpow hn0] at hh
      exact (div_le_iff₀ hl).mpr hh
    · have hloD := log_le_log (rpow_pos_of_pos hn0 truncatedSixthLowerBeta) (hwd rfl)
      change log ((N : ℝ)^truncatedSixthLowerBeta) ≤ _ at hloD
      rw [log_rpow hn0] at hloD
      refine ⟨(le_div_iff₀ hl).mpr hloD,?_⟩
      have hh := log_le_log hd0 hcap.le
      change log (p.1.2.2.1 : ℝ) ≤ log ((N : ℝ)^truncatedSixthLowerLambda/(p.1.2.1 : ℝ)) at hh
      rw [log_div (rpow_pos_of_pos hn0 _).ne' hc0.ne',log_rpow hn0] at hh
      dsimp only [coord,quadOf,lam]
      apply (div_le_iff₀ hl).mpr
      calc
        _ ≤ truncatedSixthLowerLambda*log N-log (p.1.2.1 : ℝ) := hh
        _ = _ := by field_simp

theorem relaxed_low {N : ℕ} {e : Bool} {ρ s : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ)
    (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3)
    {q : SmallGrid.Quad} (hq : q ∈ relaxedQuads N e ρ)
    (hw : Wu08FirstPrimeFour.beta N q.1 ≠ 0) :
    coord N q.1 ∈ low ∧ coord N q.2.1 ∈ low ∧ coord N q.2.2.1 ∈ low ∧
    coord N q.2.2.2 ∈ low ∧
    2 ≤ parameter (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2) := by
  obtain ⟨_,_,_,_,ha,ha',hab,hbc,hc,hcd,hd⟩ := relaxed_coordinates hN hρ hq hw
  have hs0 : 0 ≤ log ρ/log N := div_nonneg (log_nonneg hρ.le) (log_nonneg (by linarith))
  have hg := fixed_geometry
  have hx : coord N q.1 ∈ low := ⟨by linarith,by linarith [hg.2.2.2.1]⟩
  have hy : coord N q.2.1 ∈ low := ⟨by linarith,by linarith [hg.2.2.2.1]⟩
  have hz : coord N q.2.2.1 ∈ low := ⟨by linarith [hy.1],by linarith [hg.2.2.2.1]⟩
  have hy0 : 0 < coord N q.2.1 := by linarith [hy.1]
  refine ⟨hx,hy,hz,?_,?_⟩
  · cases e
    · have hd' : coord N q.2.2.2 ≤ FourRoughClosedMass.beta := hd
      exact ⟨by linarith [hz.1],by linarith [hg.2.2.2.1]⟩
    · exact ⟨by linarith [hz.1],by linarith [hd.2]⟩
  · apply (le_div_iff₀ hy0).mpr
    cases e
    · have hd' : coord N q.2.2.2 ≤ FourRoughClosedMass.beta := hd
      linarith [hg.2.2.2.2.1]
    · linarith [hd.2,hg.2.2.2.2.2.1]

/-- Original beta is at most one. This is used only for the nonnegative
Buchstab mass, not for a signed progression remainder. -/
theorem beta_le_one (N a : ℕ) : Wu08FirstPrimeFour.beta N a ≤ 1 := by
  unfold Wu08FirstPrimeFour.beta primeSWBeta
  split_ifs <;> norm_num

theorem atomWeight_le_eight (N a : ℕ) : atomWeight N a ≤ 8 := by
  unfold atomWeight
  have hh := min_le_right (log (a : ℝ)/log N) (1/10 : ℝ)
  apply (div_le_iff₀ (by linarith : 0 < 1-min (log (a : ℝ)/log N) (1/10 : ℝ))).mpr
  linarith

def effectiveQuads (N : ℕ) (e : Bool) (ρ : ℝ) : Finset SmallGrid.Quad :=
  (relaxedQuads N e ρ).filter fun q => Wu08FirstPrimeFour.beta N q.1 ≠ 0

def unshiftedTerm (N : ℕ) (q : SmallGrid.Quad) : ℝ :=
  atomWeight N q.1*density (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2)/
    (quadProduct q : ℝ)

def unshiftedMass (N : ℕ) (e : Bool) (ρ : ℝ) : ℝ :=
  ∑ q ∈ effectiveQuads N e ρ, unshiftedTerm N q

theorem effective_subset_box {N : ℕ} {e : Bool} {ρ s : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3) :
    effectiveQuads N e ρ ⊆ FourRoughClosedMass.box N := by
  intro q hq
  obtain ⟨hq,hw⟩ := mem_filter.mp hq
  obtain ⟨ha,hb,hc,hd,_⟩ := relaxed_coordinates hN hρ hq hw
  obtain ⟨hx,hy,hz,ht,_⟩ := relaxed_low hN hρ hs hlo hhi htop hq hw
  have hn : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  exact mem_product.mpr ⟨mem_window_of_coord hn ha hx,
    mem_product.mpr ⟨mem_window_of_coord hn hb hy,
      mem_product.mpr ⟨mem_window_of_coord hn hc hz,mem_window_of_coord hn hd ht⟩⟩⟩

theorem weighted_density_payment {w v ε τ u y s : ℝ}
    (hw : 0 ≤ w) (hw8 : w ≤ 8) (_hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ)
    (hu : 2 ≤ u) (hy : 1/15 ≤ y) (hs : 0 ≤ s) :
    (w+ε)*v*((buchstab (u+s/y)+τ)/y) ≤
      w*(buchstab u/y)+(2025*s+15*ε+135*τ) := by
  have hy0 : 0 < y := by linarith
  have hω := buchstab_nonneg (by linarith : 1 ≤ u)
  have hω1 := buchstab_le_one (by linarith : 1 ≤ u)
  have hsy : 0 ≤ s/y := div_nonneg hs hy0.le
  have hp : 0 ≤ (buchstab (u+s/y)+τ)/y :=
    div_nonneg (add_nonneg (buchstab_nonneg (by linarith)) hτ) hy0.le
  have hd : buchstab u/y ≤ 15 := by
    apply (div_le_iff₀ hy0).mpr
    linarith
  have hh := shifted_density_payment hu hy hs (τ := τ)
  rw [abs_of_nonneg hτ] at hh
  have hv' : (w+ε)*v ≤ w+ε := by nlinarith only [mul_le_mul_of_nonneg_left hv1 (add_nonneg hw hε)]
  have hcost : 0 ≤ 225*s+15*τ := by positivity
  calc
    _ ≤ (w+ε)*((buchstab (u+s/y)+τ)/y) := mul_le_mul_of_nonneg_right hv' hp
    _ ≤ (w+ε)*(buchstab u/y+225*s+15*τ) := mul_le_mul_of_nonneg_left hh (add_nonneg hw hε)
    _ = w*(buchstab u/y)+ε*(buchstab u/y)+(w+ε)*(225*s+15*τ) := by ring
    _ ≤ w*(buchstab u/y)+ε*15+9*(225*s+15*τ) :=
      add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hd hε))
        (mul_le_mul_of_nonneg_right (by linarith : w+ε ≤ 9) hcost)
    _ = _ := by ring

/-- All kernel and epsilon/tau losses are paid on the ACTUAL four-label
support. The remaining unshiftedMass has no shifted kernel or arithmetic
normalization loss; only its boundary enlargement remains. -/
theorem buchstabGrid_shift_paid {N : ℕ} {e : Bool} {ρ s ε τ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (_hρu : ρ ≤ 5/4)
    (hs : log ρ/log N ≤ s)
    (hlo : 2*s ≤ FourRoughClosedMass.alpha-1/15)
    (hhi : 1/10+s ≤ FourRoughClosedMass.beta)
    (htop : lam-FourRoughClosedMass.alpha+2*s ≤ 1/3)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ) (hm : windowMass N ≤ 5) :
    buchstabGrid N e ρ ε τ ≤ unshiftedMass N e ρ+625*(2025*s+15*ε+135*τ) := by
  have hs0 : 0 ≤ log ρ/log N := div_nonneg (log_nonneg hρ.le) (log_nonneg (by linarith))
  have hs' : 0 ≤ s := hs0.trans hs
  let E := 2025*s+15*ε+135*τ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsum : buchstabGrid N e ρ ε τ =
      ∑ q ∈ effectiveQuads N e ρ, quadWeight N ε q*
        (buchstab (log (roughX N ρ q)/log (q.2.1 : ℝ))+τ)/
          ((quadProduct q : ℝ)*(coord N q.2.1)) := by
    unfold buchstabGrid effectiveQuads
    rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hw : Wu08FirstPrimeFour.beta N q.1 = 0
    · simp [hw,quadWeight]
    · simp only [hw,ne_eq,not_false_eq_true,↓reduceIte,coord]
  rw [hsum]
  have hpoint : ∀ q ∈ effectiveQuads N e ρ,
      quadWeight N ε q*(buchstab (log (roughX N ρ q)/log (q.2.1 : ℝ))+τ)/
          ((quadProduct q : ℝ)*(coord N q.2.1)) ≤ unshiftedTerm N q+E/(quadProduct q : ℝ) := by
    intro q hq
    obtain ⟨hq,hw⟩ := mem_filter.mp hq
    obtain ⟨_,hy,_,_,hu⟩ := relaxed_low hN hρ hs hlo hhi htop hq hw
    have he : log (roughX N ρ q)/log (q.2.1 : ℝ) =
        parameter (coord N q.1) (coord N q.2.1) (coord N q.2.2.1) (coord N q.2.2.2)+
          (log ρ/log N)/coord N q.2.1 := by
      rw [roughX_log_identity hN hρ hq]
      unfold parameter coord
      ring
    have hh := weighted_density_payment (atomWeight_nonneg N q.1) (atomWeight_le_eight N q.1)
      (beta_nonneg N q.1) (beta_le_one N q.1) hε hε1 hτ hu hy.1 hs0
    rw [he]
    have hcomp : 2025*(log ρ/log N)+15*ε+135*τ ≤ E := by dsimp [E]; linarith
    have hp := div_le_div_of_nonneg_right (hh.trans (add_le_add (le_refl _) hcomp))
      (Nat.cast_nonneg (quadProduct q))
    dsimp only [quadWeight,unshiftedTerm,density]
    simp only [div_eq_mul_inv,mul_inv_rev,add_mul] at hp ⊢
    nlinarith only [hp]
  have hrec : reciprocalMass (effectiveQuads N e ρ) ≤ 625 := by
    calc
      _ ≤ reciprocalMass (FourRoughClosedMass.box N) := sum_le_sum_of_subset_of_nonneg
        (effective_subset_box hN hρ hs hlo hhi htop) (by intros; positivity)
      _ = windowMass N^4 := box_reciprocal N
      _ ≤ (5 : ℝ)^4 := pow_le_pow_left₀ (sum_nonneg (by intros; positivity)) hm 4
      _ = _ := by norm_num
  calc
    _ ≤ ∑ q ∈ effectiveQuads N e ρ, (unshiftedTerm N q+E/(quadProduct q : ℝ)) := sum_le_sum hpoint
    _ = unshiftedMass N e ρ+E*reciprocalMass (effectiveQuads N e ρ) := by
      simp only [unshiftedMass,reciprocalMass,sum_add_distrib,mul_sum,mul_one_div]
      rfl
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hrec hE]

#check effectiveQuads
#print axioms effectiveQuads
#check unshiftedTerm
#print axioms unshiftedTerm
#check unshiftedMass
#print axioms unshiftedMass
#check effective_subset_box
#print axioms effective_subset_box
#check weighted_density_payment
#print axioms weighted_density_payment
#check buchstabGrid_shift_paid
#print axioms buchstabGrid_shift_paid
#check log_shift_uniform
#print axioms log_shift_uniform
#check relaxed_coordinates
#print axioms relaxed_coordinates
#check relaxed_low
#print axioms relaxed_low
#check beta_le_one
#print axioms beta_le_one
#check atomWeight_le_eight
#print axioms atomWeight_le_eight
#check closed_strip_uniform
#print axioms closed_strip_uniform
#check first_strip_reciprocal
#print axioms first_strip_reciprocal
#check shifted_density_payment
#print axioms shifted_density_payment
end Wu08FirstPrimeFour.SmallBoundary
