import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9OrderedSource
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem gamma9_eq_omega3_of_local_level {i N : ℕ} {δ : ℝ}
    (W : Fin i → Finset ℕ) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 ≤ (N : ℝ) ^ (1 / 2 - δ) / d) :
    secondFunctionalMotherGammaSum p N δ W 9 =
      wuOmega3Sum N δ p.kappa3 p.kappa1 W := by
  unfold secondFunctionalMotherGammaSum wuOmega3Sum
  apply sum_congr rfl
  intro d hdm
  have hs : 0 < p.s := lt_of_lt_of_le zero_lt_one hp.one_le_s
  have h3 := hp.s_le_kappa3
  have h2 := hp.kappa3_lt_kappa2.le
  have h1 := hp.kappa2_lt_kappa1.le
  have hcut {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      wuLocalCutoff N δ d b ≤ wuLocalCutoff N δ d a :=
    rpow_le_rpow_of_exponent_le (hR d hdm) (one_div_le_one_div_of_le ha hab)
  rw [secondFunctionalMother_gamma9_ordered_source N d N
    (hcut (hs.trans_le (h3.trans (h2.trans h1))) hp.kappa1_le_S)
    (hcut (hs.trans_le (h3.trans h2)) h1)
    (hcut (hs.trans_le h3) h2) (hcut hs h3)]
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa3)
      (fun t => (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℤ)))
  simpa only [Int.cast_sum, Int.cast_natCast, wuOmega3] using h

end Wu18938Campaign.M4
