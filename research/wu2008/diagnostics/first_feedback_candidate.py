"""Exact rational diagnostics for first-feedback entries; not a Lean proof.

Constants mirror W06SigmaV2 and WR2XiRationalCandidate. Printed decimals are
for readability; all comparisons use Fraction.
"""
from fractions import Fraction as F
C=lambda z:2*z+2*z**3/3
L=lambda x:C((x-1)/(x+1))
U=lambda x:(x-1)*(x*x+10*x+1)/(6*x*(x+1))
V=lambda x:(3*U(x)+2*L(x))/5
lo=lambda x:L((1+x)/2)+L(2*x/(1+x))
up=lambda x:V((1+x)/2)+V(2*x/(1+x))
low=lambda x:lo(x) if x>=1 else -up(1/x)
high=lambda x:up(x) if x>=1 else -lo(1/x)
signed=lambda c,x:c*(low(x) if c>=0 else high(x))
def ecell(S,a,b):
 q=2*(S-1)
 ea=F(8,3)-4*q/S+2*q*q/S**2-2*q**3/(3*S**3)
 eb=4*q/S-2*q*q/S**2+2*q**3/(3*S**3)
 ec=-2*q*q/S+2*q**3/(3*S**2)
 ed=2*q**3/(3*S)
 return signed(ea,b/a)+signed(eb,(b+S)/(a+S))-ec*(1/(b+S)-1/(a+S))-ed/2*(1/(b+S)**2-1/(a+S)**2)
def jc(s,S):
 l,r=1-1/s,1-1/S
 h,v=2*(S-2),S-3
 c,d=C(-1+h/v),C(-1+h/(S+v))
 h2=-2*h*h*(1/(S+v)-1/v)+2*h**3/3*(1/(S+v)**2-1/v**2)
 h3=2*h**3/3*(1/(S+v)-1/v)
 yl,yr=S*l+v,S*r+v
 return signed(c,r/l)+signed(-d,(1-r)/(1-l))+signed(d-c,yr/yl)-h2*(1/yr-1/yl)-h3/2*(1/yr**2-1/yl**2)
mass=list(map(F,['111258826147199/6000000000000000','11015108859877/3000000000000000','795917363183/200000000000000','400954892897/93750000000000','27380225768713/6000000000000000','75612009467/15625000000000','10208761954023/2000000000000000','267961103141/50000000000000','700494974059/125000000000000']))
rows=[[159,23,24,25,25,26,26,26,27],[160,23,24,24,25,25,26,26,26],[164,23,24,24,25,25,26,26,26],[173,23,24,24,25,25,26,26,26]]
if __name__ == '__main__':
 for i,S in enumerate(map(F,['3.58','3.47','3.34','3.19'])):
  s=F(26+i,10); w=low((S-1)/(s-1)); ac=low(4/(S-1))+w/2
  vals=[]
  for k in range(9):
   a=S-2 if k==0 else F(21+k,10); b=F(22+k,10)
   val=ac*mass[k]/(1-F(858467,5000000))+ecell(S,a,b)+(low(b/a)*w+(jc(s,S) if k==0 else 0))/2
   vals.append(val-F(rows[i][k],1000))
  assert all(v > 0 for v in vals)
  print(i+4,'entry margins',[round(float(v),9) for v in vals])
