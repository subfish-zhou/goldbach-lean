import WR2ClassicalCPayments
import WR2ClassicalCPoints120
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_120 (j : Fin 16) : cPayment (16*120+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*120+j.val)+point (1327/200) 4096 (16*120+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1920 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1920+point (1327/200) 4096 1921)/2)
    have hp : cPayment 1920 = (70985711034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1920+point (1327/200) 4096 1921)/2 = (5301007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1920
  · change cPayment 1921 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1921+point (1327/200) 4096 1922)/2)
    have hp : cPayment 1921 = (70959216916:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1921+point (1327/200) 4096 1922)/2 = (5302061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1921
  · change cPayment 1922 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1922+point (1327/200) 4096 1923)/2)
    have hp : cPayment 1922 = (70932704771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1922+point (1327/200) 4096 1923)/2 = (1060623:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1922
  · change cPayment 1923 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1923+point (1327/200) 4096 1924)/2)
    have hp : cPayment 1923 = (70906174631:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1923+point (1327/200) 4096 1924)/2 = (5304169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1923
  · change cPayment 1924 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1924+point (1327/200) 4096 1925)/2)
    have hp : cPayment 1924 = (70879626525:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1924+point (1327/200) 4096 1925)/2 = (5305223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1924
  · change cPayment 1925 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1925+point (1327/200) 4096 1926)/2)
    have hp : cPayment 1925 = (70853060485:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1925+point (1327/200) 4096 1926)/2 = (5306277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1925
  · change cPayment 1926 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1926+point (1327/200) 4096 1927)/2)
    have hp : cPayment 1926 = (70826476542:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1926+point (1327/200) 4096 1927)/2 = (5307331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1926
  · change cPayment 1927 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1927+point (1327/200) 4096 1928)/2)
    have hp : cPayment 1927 = (70799874726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1927+point (1327/200) 4096 1928)/2 = (1061677:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1927
  · change cPayment 1928 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1928+point (1327/200) 4096 1929)/2)
    have hp : cPayment 1928 = (70773255069:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1928+point (1327/200) 4096 1929)/2 = (5309439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1928
  · change cPayment 1929 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1929+point (1327/200) 4096 1930)/2)
    have hp : cPayment 1929 = (70746617601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1929+point (1327/200) 4096 1930)/2 = (5310493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1929
  · change cPayment 1930 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1930+point (1327/200) 4096 1931)/2)
    have hp : cPayment 1930 = (70719962352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1930+point (1327/200) 4096 1931)/2 = (5311547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1930
  · change cPayment 1931 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1931+point (1327/200) 4096 1932)/2)
    have hp : cPayment 1931 = (70693289354:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1931+point (1327/200) 4096 1932)/2 = (5312601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1931
  · change cPayment 1932 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1932+point (1327/200) 4096 1933)/2)
    have hp : cPayment 1932 = (70666598637:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1932+point (1327/200) 4096 1933)/2 = (1062731:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1932
  · change cPayment 1933 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1933+point (1327/200) 4096 1934)/2)
    have hp : cPayment 1933 = (70639890232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1933+point (1327/200) 4096 1934)/2 = (5314709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1933
  · change cPayment 1934 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1934+point (1327/200) 4096 1935)/2)
    have hp : cPayment 1934 = (70613164168:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1934+point (1327/200) 4096 1935)/2 = (5315763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1934
  · change cPayment 1935 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1935+point (1327/200) 4096 1936)/2)
    have hp : cPayment 1935 = (70586420478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1935+point (1327/200) 4096 1936)/2 = (5316817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1935
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_120
