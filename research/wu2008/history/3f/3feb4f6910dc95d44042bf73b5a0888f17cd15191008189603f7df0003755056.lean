import Wu04BypassMatrix
import NineLiteral

noncomputable section
namespace Wu04Bypass
open ActualNineFeedback NodeExtension Wu2008DoubleSieve FirstFeedbackIntegrals
open scoped BigOperators

def M : Fin 9 → Fin 9 → ℝ :=
  ![![(797/125000),(1897/1000000),(2009/1000000),(1051/500000),(2179/1000000),(1121/500000),(2293/1000000),(1167/500000),(1183/500000)],
    ![(6187/1000000),(187/100000),(397/200000),(13/6250),(1079/500000),(1111/500000),(1137/500000),(579/250000),(47/20000)],
    ![(5637/1000000),(1791/1000000),(1911/1000000),(2011/1000000),(1047/500000),(1081/500000),(1109/500000),(2263/1000000),(23/10000)],
    ![(2909/500000),(909/500000),(121/62500),(1017/500000),(423/200000),(1091/500000),(559/250000),(2281/1000000),(579/250000)],
    ![(27301/1000000),(8827/1000000),(2359/250000),(4971/500000),(10363/1000000),(1071/100000),(2749/250000),(11229/1000000),(1427/125000)],
    ![(4731/125000),(2569/250000),(337/31250),(7/625),(5769/500000),(11811/1000000),(1203/100000),(12201/1000000),(12333/1000000)],
    ![(3283/62500),(11989/1000000),(12377/1000000),(2537/200000),(12927/1000000),(13113/1000000),(13251/1000000),(13351/1000000),(1677/125000)],
    ![(1449/20000),(2793/200000),(2843/200000),(9/625),(14529/1000000),(7307/500000),(14661/1000000),(14677/1000000),(7333/500000)],
    ![(1598/15625),(16469/1000000),(517/31250),(16571/1000000),(16559/1000000),(4129/250000),(16447/1000000),(16357/1000000),(13/800)]]

def v0 : Fin 9 → ℝ := ![(15826357/1000000000),(15247971/1000000000),(13898757/1000000000),(11776059/1000000000),(9405211/1000000000),(131179/20000000),(3536751/1000000000),(1056651/1000000000),0]
def v1 : Fin 9 → ℝ := ![(8027321/500000000),(3094369/200000000),(220463/15625000),(299781/25000000),(5219287/500000000),(3918917/500000000),(5140851/1000000000),(192701/62500000),(526863/200000000)]
def v2 : Fin 9 → ℝ := ![(8038579/500000000),(7747073/500000000),(14131287/1000000000),(12013107/1000000000),(2109157/200000000),(7956999/1000000000),(5274649/1000000000),(3234577/1000000000),(175561/62500000)]
def v3 : Fin 9 → ℝ := ![(16079007/1000000000),(15495977/1000000000),(7066531/500000000),(12014901/1000000000),(10554571/1000000000),(3983407/500000000),(528573/100000000),(3247187/1000000000),(352953/125000000)]
def v4 : Fin 9 → ℝ := ![(16079161/1000000000),(15496129/1000000000),(14133209/1000000000),(240301/20000000),(10555299/1000000000),(7967627/1000000000),(660831/125000000),(3248231/1000000000),(2824837/1000000000)]
def v5 : Fin 9 → ℝ := ![(16079173/1000000000),(15496141/1000000000),(7066611/500000000),(6007531/500000000),(10555359/1000000000),(3983847/500000000),(1321681/250000000),(3248317/1000000000),(2824937/1000000000)]
def v6 : Fin 9 → ℝ := ![(8039587/500000000),(7748071/500000000),(14133223/1000000000),(12015063/1000000000),(2638841/250000000),(79677/10000000),(528673/100000000),(812081/250000000),(1412473/500000000)]
def v7 : Fin 9 → ℝ := ![(8039587/500000000),(7748071/500000000),(14133223/1000000000),(12015063/1000000000),(2111073/200000000),(79677/10000000),(5286731/1000000000),(129933/40000000),(1412473/500000000)]
def v8 : Fin 9 → ℝ := ![(8039587/500000000),(7748071/500000000),(14133223/1000000000),(12015063/1000000000),(2111073/200000000),(79677/10000000),(5286731/1000000000),(129933/40000000),(1412473/500000000)]

theorem v0_eq_publication : v0 = NineFeedbackStrength.publication := by
  funext i
  fin_cases i
  · change v0 ⟨0, by decide⟩ = Wu04CurvePaid.publication
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨1, by decide⟩ = Wu04RemainingCore.publication ⟨0, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨2, by decide⟩ = Wu04RemainingCore.publication ⟨1, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨3, by decide⟩ = Wu04RemainingCore.publication ⟨2, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨4, by decide⟩ = Wu04FirstCore.publication ⟨0, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨5, by decide⟩ = Wu04FirstCore.publication ⟨1, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨6, by decide⟩ = Wu04FirstCore.publication ⟨2, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨7, by decide⟩ = Wu04FirstCore.publication ⟨3, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]
  · change v0 ⟨8, by decide⟩ = Wu04FirstCore.publication ⟨4, by decide⟩
    norm_num [v0, Wu04CurvePaid.publication, Wu04RemainingCore.publication, Wu04FirstCore.publication]

theorem v0_nonneg : ∀ k, 0 ≤ v0 k := by
  intro k
  fin_cases k <;> norm_num [v0]

theorem v1_nonneg : ∀ k, 0 ≤ v1 k := by
  intro k
  fin_cases k <;> norm_num [v1]

theorem v2_nonneg : ∀ k, 0 ≤ v2 k := by
  intro k
  fin_cases k <;> norm_num [v2]

theorem v3_nonneg : ∀ k, 0 ≤ v3 k := by
  intro k
  fin_cases k <;> norm_num [v3]

theorem v4_nonneg : ∀ k, 0 ≤ v4 k := by
  intro k
  fin_cases k <;> norm_num [v4]

theorem v5_nonneg : ∀ k, 0 ≤ v5 k := by
  intro k
  fin_cases k <;> norm_num [v5]

theorem v6_nonneg : ∀ k, 0 ≤ v6 k := by
  intro k
  fin_cases k <;> norm_num [v6]

theorem v7_nonneg : ∀ k, 0 ≤ v7 k := by
  intro k
  fin_cases k <;> norm_num [v7]

theorem v8_nonneg : ∀ k, 0 ≤ v8 k := by
  intro k
  fin_cases k <;> norm_num [v8]

end Wu04Bypass
