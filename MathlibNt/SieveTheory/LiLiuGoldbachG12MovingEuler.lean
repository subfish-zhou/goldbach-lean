import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledC2Sieve
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct

noncomputable section
open Classical Finset Filter
open MathlibNt.SieveTheory
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12MovingEuler

/-- The genuine fixed-parameter JR error can be made small, before Q varies. -/
theorem error_eventually (K C t : ℝ) (hC : 0 < C) (ht : 0 < t) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∀ᶠ Q : ℝ in atTop,
      C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ))) ≤
        t*Real.exp Real.eulerMascheroniConstant := by
  let η := min (1/16 : ℝ) (t*Real.exp Real.eulerMascheroniConstant/(4*C))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηu : η < 1/8 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hsmall : C*η ≤ t*Real.exp Real.eulerMascheroniConstant/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (min_le_right (1/16 : ℝ) (t*Real.exp Real.eulerMascheroniConstant/(4*C)))
    change η*(4*C) ≤ _ at h
    linarith
  have hlim : Tendsto (fun Q : ℝ =>
      C*((η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/3)).comp
      Real.tendsto_log_atTop).const_mul ((η^8)⁻¹*Real.exp (6*K+2))).const_mul C
  refine ⟨η,hη,hηu,?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < t*Real.exp Real.eulerMascheroniConstant/2))] with Q hQ
  nlinarith only [hsmall,hQ,mul_pos ht (Real.exp_pos Real.eulerMascheroniConstant)]

/-- A single ambient threshold admits every moving Q in the stated range. -/
theorem geometry (L : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : ℝ,
      (N : ℝ)^(1/3 : ℝ) ≤ Q → Q ≤ N →
      L ≤ Q ∧ 4 ≤ Q ∧ 0 < Real.log (N : ℝ) ∧ 0 < Real.log Q ∧
      Real.log (N : ℝ)/3 ≤ Real.log Q ∧ 4*Real.log (N : ℝ)/Real.log Q ≤ 12 := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (max 4 L))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hg
  refine ⟨max 4 N₀,le_max_left _ _,?_⟩
  intro N hN Q hQl _hQu
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := (hN₀ N ((le_max_right _ _).trans hN)).trans hQl
  have hQ4 : 4 ≤ Q := (le_max_left _ _).trans hb
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hl : Real.log (N : ℝ)/3 ≤ Real.log Q := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNpos (1/3 : ℝ)) hQl
    rw [Real.log_rpow hNpos] at h
    linarith
  refine ⟨(le_max_right _ _).trans hb,hQ4,hlogN,hlogQ,hl,?_⟩
  apply (div_le_iff₀ hlogQ).mpr
  linarith

/-- Identify exactly the strict prime product used by the physical sieve. -/
theorem euler_eq (N : ℕ) (Z : ℝ) :
    (∏ p ∈ goldbachB10SiftingPrimes N Z, (1-AnalyticNumberTheory.Sieve.goldbachNu p)) =
      goldbachB10PrimeProduct N Z := by
  unfold goldbachB10PrimeProduct MathlibNt.SieveTheory.MertensTheorem.goldbachSieveProduct
  apply prod_congr rfl
  intro p hp
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (mem_filter.mp hp).2.1]

/-- Nonnegativity is proved on the actual prime carrier, including p=2. -/
theorem euler_nonneg (N : ℕ) (Z : ℝ) : 0 ≤ goldbachB10PrimeProduct N Z := by
  rw [← euler_eq]
  apply prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.1.two_le
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (mem_filter.mp hp).2.1]
  have h : 1 / ((p : ℝ)-1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  linarith

/-- Genuine moving-Q Euler/JR normalization. No error-smallness premise and no
geometric-scale choice is hidden in the interface. The cutoff precedes N and Q. -/
theorem normalized (K C τ : ℝ) (_hK : 1 < K) (hC : 0 < C) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, Even N → ∀ Q : ℝ,
      (N : ℝ)^(1/3 : ℝ) ≤ Q → Q ≤ N →
      let Z := Real.sqrt Q
      let Euler := ∏ p ∈ goldbachB10SiftingPrimes N Z,
        (1-AnalyticNumberTheory.Sieve.goldbachNu p)
      let E := C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))
      2 ≤ Z ∧ Euler*(jr1965F (Real.log Q/Real.log Z)+E) ≤
        (4*Real.log (N : ℝ)/Real.log Q+τ)*SingularSeries.liuSingularSeries N /
          Real.log (N : ℝ) := by
  let t := min (1 : ℝ) (τ/36)
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htτ : 36*t ≤ τ := by have h := min_le_right (1 : ℝ) (τ/36); dsimp [t]; linarith
  obtain ⟨η,hη,hηu,herr⟩ := error_eventually K C t hC ht
  obtain ⟨Q₀,hQ₀⟩ := eventually_atTop.mp herr
  obtain ⟨Z₀,hZ₀,hprod⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries t ht
  obtain ⟨N₀,hN₀,hgeom⟩ := geometry (max Q₀ (Z₀^2))
  refine ⟨η,hη,hηu,N₀,hN₀,?_⟩
  intro N hN hEven Q hQl hQu
  dsimp only
  obtain ⟨hbig,hQ4,hlogN,hlogQ,_hloglower,hratio⟩ := hgeom N hN Q hQl hQu
  have hQpos : 0 < Q := by linarith
  have hZbig : Z₀ ≤ Real.sqrt Q := (Real.le_sqrt (by linarith) hQpos.le).mpr
    ((le_max_right _ _).trans hbig)
  have hZ2 : 2 ≤ Real.sqrt Q := hZ₀.trans hZbig
  have hlogZ : 0 < Real.log (Real.sqrt Q) := Real.log_pos (by linarith)
  have hlogs := Real.log_sqrt hQpos.le
  have hs : Real.log Q/Real.log (Real.sqrt Q) = 2 := by
    rw [hlogs]; field_simp
  have hF : jr1965F (Real.log Q/Real.log (Real.sqrt Q)) =
      Real.exp Real.eulerMascheroniConstant := by
    rw [hs,jr1965F_initial le_rfl]; ring
  have hE := hQ₀ Q ((le_max_left _ _).trans hbig)
  have hV := (le_div_iff₀ hlogZ).mpr (hprod N (hN₀.trans hN) hEven _ hZbig)
  have hExp : Real.exp Real.eulerMascheroniConstant *
      Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]; norm_num
  have ht2 : (1+t)^2 ≤ 1+3*t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  have hcoef : (4*Real.log (N : ℝ)/Real.log Q)*(1+t)^2 ≤
      4*Real.log (N : ℝ)/Real.log Q+τ := by
    have ha : 0 ≤ 4*Real.log (N : ℝ)/Real.log Q := by positivity
    have hb := mul_le_mul_of_nonneg_left ht2 ha
    have hc := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 3*t)
    nlinarith only [hb,hc,htτ]
  refine ⟨hZ2,?_⟩
  rw [euler_eq,hF]
  calc
    _ ≤ goldbachB10PrimeProduct N (Real.sqrt Q)*
        (Real.exp Real.eulerMascheroniConstant*(1+t)) := by
      apply mul_le_mul_of_nonneg_left _ (euler_nonneg N _)
      nlinarith only [hE]
    _ ≤ (2*Real.exp (-Real.eulerMascheroniConstant)*(1+t)*
        SingularSeries.liuSingularSeries N/Real.log (Real.sqrt Q))*
        (Real.exp Real.eulerMascheroniConstant*(1+t)) :=
      mul_le_mul_of_nonneg_right hV (by positivity)
    _ = (Real.exp Real.eulerMascheroniConstant*Real.exp (-Real.eulerMascheroniConstant))*
        (4*(1+t)^2*SingularSeries.liuSingularSeries N/Real.log Q) := by rw [hlogs]; ring
    _ = (4*Real.log (N : ℝ)/Real.log Q)*(1+t)^2*
        (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) := by
      rw [hExp]; field_simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hcoef
        (div_nonneg (SingularSeries.liuSingularSeries_pos N).le hlogN.le)
      simpa only [div_eq_mul_inv,mul_assoc] using h

end G12MovingEuler
