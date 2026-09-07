import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorFinalScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralScalar

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual author-weight producer. Both distribution branches, sieve families,
Euler factors, original labels, expanded endpoints and all exceptional pieces
are discharged; only the fixed original parameters remain. -/
theorem goldbachWeightG11_le_authorIntegral_direct (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      ((561522/1000000 : ℝ)*goldbachG11PrimeIntegral goldbachG11AuthorWeight+δ)*
        (SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨C,hC,hmass⟩ := goldbachG11WeightedGridMass_le_paidKernel
  obtain ⟨t,ht,htu,hchoice⟩ := goldbachG11Author_choose_loss C δ hδ
  have hρ : 1 < 1+t := by linarith
  have hρu : 1+t ≤ (5/4 : ℝ) := by linarith
  obtain ⟨Mg,hMg,hg⟩ := goldbachG11GoodSwitchedTotal_le_authorGrid t ht 3 hε hεu hρ hρu
  obtain ⟨Mm,_hMm,hm⟩ := hmass t ht
  obtain ⟨Ka,_hKa,hka⟩ := goldbachG11PrimeKernel_author_le_integral_eventually t ht
  obtain ⟨K1,_hK1,hk1⟩ := goldbachG11PrimeKernel_one_le_integral_eventually 1 (by norm_num)
  obtain ⟨Mt,_hMt,htail⟩ := goldbachG11Author_divisor_tail_paid 9 t ht
  obtain ⟨Ml,hlog⟩ := Filter.eventually_atTop.mp (goldbachG11NormalizedIntegral_logError_paid 5 t ht)
  obtain ⟨Mo,_hMo,ho⟩ := goldbachWeightG11_le_goodSwitched_normalized t ht
  refine ⟨max Mg (max Mm (max Ka (max K1 (max Mt (max Ml Mo))))),hMg.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hn4 : 4 ≤ N := by omega
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let M : ℝ := SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2
  have hM : 0 ≤ M := div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le hn0.le) (sq_nonneg _)
  let h : ℝ → ℝ := fun r => goldbachG11AuthorWeight r+t
  have hh : ∀ r,0 ≤ h r := fun r => add_nonneg (goldbachG11AuthorWeight_nonneg r) ht.le
  have hh9 : ∀ r,h r ≤ 9 := by
    intro r
    have hw := goldbachG11AuthorWeight_global_upper r
    dsimp [h]
    linarith
  let E : ℝ := (1+t)^2*((561522/1000000 : ℝ)+t)*
    (goldbachG11PrimeIntegral goldbachG11AuthorWeight+(|goldbachG11PrimeIntegral (fun _ => 1)|+2)*t)+9*C*t+t
  have hK : goldbachG11PrimeKernel h N ≤ goldbachG11PrimeIntegral goldbachG11AuthorWeight+
      (|goldbachG11PrimeIntegral (fun _ => 1)|+2)*t := by
    calc
      _ = goldbachG11PrimeKernel goldbachG11AuthorWeight N+t*goldbachG11PrimeKernel (fun _ => 1) N :=
        goldbachG11PrimeKernel_author_add N t
      _ ≤ (goldbachG11PrimeIntegral goldbachG11AuthorWeight+t)+t*(|goldbachG11PrimeIntegral (fun _ => 1)|+1) :=
        add_le_add (hka N (by omega)) (mul_le_mul_of_nonneg_left
          ((hk1 N (by omega)).trans (add_le_add (le_abs_self _) le_rfl)) ht.le)
      _ = _ := by ring
  have hb := hm N (by omega) ε (1+t) hρ hρu h 9 (by norm_num) hh hh9
  have hb' : (Real.log (N : ℝ)/N)*goldbachG11WeightedGridMass N ε (1+t) h ≤ E := by
    calc
      _ ≤ (1+t)^2*((561522/1000000 : ℝ)+t)*goldbachG11PrimeKernel h N+
          C*9*((1+t)-1)+16800*9*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) := hb
      _ ≤ (1+t)^2*((561522/1000000 : ℝ)+t)*
          (goldbachG11PrimeIntegral goldbachG11AuthorWeight+(|goldbachG11PrimeIntegral (fun _ => 1)|+2)*t)+
          C*9*((1+t)-1)+t :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hK (by positivity)) le_rfl) (htail N (by omega))
      _ = E := by dsimp [E]; ring
  have hscaled : SingularSeries.liuSingularSeries N/Real.log (N : ℝ)*
      goldbachG11WeightedGridMass N ε (1+t) h ≤ E*M := by
    calc
      _ = ((Real.log (N : ℝ)/N)*goldbachG11WeightedGridMass N ε (1+t) h)*M := by
        dsimp only [M]
        field_simp
      _ ≤ E*M := mul_le_mul_of_nonneg_right hb' hM
  have hgN := hg N (by omega) hEven
  have hoN := ho N (by omega) ε hε.le
  have hlN : 5*(N : ℝ)/Real.log (N : ℝ)^3 ≤ t*M := by
    simpa only [Real.rpow_ofNat] using hlog N (by omega)
  have hcoef : E+2*t ≤ (561522/1000000 : ℝ)*goldbachG11PrimeIntegral goldbachG11AuthorWeight+δ := by
    dsimp [E]
    linarith only [hchoice]
  calc
    _ ≤ (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ)+t*M := hoN
    _ ≤ (SingularSeries.liuSingularSeries N/Real.log (N : ℝ)*goldbachG11WeightedGridMass N ε (1+t) h+
        5*N/Real.log (N : ℝ)^3)+t*M := add_le_add hgN le_rfl
    _ ≤ (E*M+t*M)+t*M := add_le_add (add_le_add hscaled hlN) le_rfl
    _ = (E+2*t)*M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hM

/-- The existing certified author integral is consumed, not recomputed. -/
theorem goldbachWeightG11_le_authorScalar_direct (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      ((10191/100000 : ℝ)+δ)*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀,hN₀,hb⟩ := goldbachWeightG11_le_authorIntegral_direct δ ε hδ hε hεu
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  exact (hb N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add goldbachG11PrimeIntegral_author_scalar_le_10191 (le_refl δ))
    (div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig