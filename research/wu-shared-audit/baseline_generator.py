"""Reproducible exact-rational cubic certificates for the Hf4 compact kernel.

The 40 original cells and 1e-14 rounding scale are unchanged. Every generated
cell proves its original, literal mass_bounds statement, using stronger new
computed bounds. Fractions are exact; coefficient rounding is downwards and
error rounding is upwards. Lean's kernel checks all arithmetic conditions.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse

class Expr:
 def __init__(self,g,n):self.g,self.n=g,n
 def __add__(a,b):return a.g.make('add',a,a.g.coerce(b))
 def __radd__(a,b):return a.g.coerce(b)+a
 def __mul__(a,b):return a.g.make('mul',a,a.g.coerce(b))
 def __rmul__(a,b):return a.g.coerce(b)*a
 def __neg__(a):return a.g.make('neg',a)
 def __sub__(a,b):return a+-a.g.coerce(b)
 def __rsub__(a,b):return a.g.coerce(b)+-a
 def __truediv__(a,b):return a*a.g.make('inv',a.g.coerce(b))
 def __pow__(a,n):
  assert n>=1
  return a if n==1 else a**(n-1)*a
class Graph:
 def __init__(self):self.nodes=[];self.cache={}
 def coerce(self,a):return a if isinstance(a,Expr) else self.make('const',F(a))
 def make(self,op,*args):
  key=(op,*[x.n if isinstance(x,Expr) else x for x in args])
  if key not in self.cache:self.cache[key]=len(self.nodes);self.nodes.append(key)
  return Expr(self,self.cache[key])
def compact():
 g=Graph();t=g.make('var');r=g.make('rad')
 def lo(z):return 2*z*(525+z*(1050+z*(385+z*(-280+z*(-140+z**2*(12-2*z))))))/(105*(1+z)**2*(5-3*z**2))
 def up(z):return 2*z*(105+z*(105+z*(-70+z*(-70+z*(-14+z*(-14-6*z))))))/(105*(1-z)*(1+z)**2)
 def sl(x):return lo((x-1)/(x+3))+lo((x-1)/(3*x+1))
 def su(x):return up((x-1)/(x+3))+up((x-1)/(3*x+1))
 joint=F(32,35)-F(184,105)*t-F(1144,945)*t**2-F(5261,540)*t**3+F(176,63)*t**4+F(1759,270)*t**5+F(2122,945)*t**6+F(299,1260)*t**7
 final=(-(2145*t**2+4418*t+2280)/(210*(t+1)**2))*su((t+2)/3)/t+(64*(10*t**4+18*t**3-t**2-6*t+3)/(945*t**4))*sl((t+3)*(t+2)/(6*(t+1)))/t+(250*(-5*t**2+21*t+26)/(189*(-t**2+6*t+6)))*sl((t**2+18*t+21)*(t+2)**2/(90*(t+1)**2))/t+(250*(-11*t**2+97*t+108)/(189*r*(-t**2+6*t+6)))*sl((t+9-2*r)*(5+r)/((t+9+2*r)*(5-r)))/t+joint/(t**4*(t+1)*(t+3)**3)
 assert final.n==len(g.nodes)-1
 return g.nodes

D=10**14
def floor(x):return F(x.numerator*D//x.denominator,D)
def ceil(x):return -floor(-x)
def norm(p):return sum(map(abs,p))
def prod(p,q):return [sum((p[j]*q[i-j] for j in range(4) if 0<=i-j<4),F(0)) for i in range(7)]
def err(p,q,r):return sum(abs(a-b) for a,b in zip(prod(p,q),list(r)+[F(0)]*3))
def evaluate(nodes, i):
 a=[]
 for op,*args in nodes:
  if op=='var':p,e=[F(41+2*i,40),F(1,40),F(0),F(0)],F(0)
  elif op=='rad':p,e=[F(7745966692415,2000000000000),F(0),F(0),F(0)],F(1,2000000000000)
  elif op=='const':p,e=[args[0],F(0),F(0),F(0)],F(0)
  elif op=='neg':q,e=a[args[0]];p=[-v for v in q]
  elif op in ('add','mul'):
   q,d=a[args[0]];r,f=a[args[1]]
   if op=='add':p=[floor(x+y) for x,y in zip(q,r)];e=ceil(d+f+sum(abs(x+y-z) for x,y,z in zip(q,r,p)))
   else:p=[floor(x) for x in prod(q,r)[:4]];e=ceil(d*norm(r)+f*norm(q)+d*f+err(q,r,p))
  else:
   q,d=a[args[0]];L=abs(q[0])-sum(map(abs,q[1:]))-d
   assert L>0
   p=[1/q[0]]
   for k in range(1,4):p.append(-sum(q[j]*p[k-j] for j in range(1,k+1))/q[0])
   p=list(map(floor,p));e=ceil((err(q,p,[F(1),F(0),F(0),F(0)])+norm(p)*d)/L)
  a.append((p,e))
 return a

TARGETS = [
    ('17511388157/6000000000000000', '21990320141/6000000000000000'),
    ('42735154237/2000000000000000', '44167542079/2000000000000000'),
    ('54983970103/1000000000000000', '27828694777/500000000000000'),
    ('75615759727/750000000000000', '304339421431/3000000000000000'),
    ('234731806523/1500000000000000', '117798272821/750000000000000'),
    ('1320201268963/6000000000000000', '1323374584873/6000000000000000'),
    ('869573851603/3000000000000000', '435512932469/1500000000000000'),
    ('1093929758717/3000000000000000', '1095256637681/3000000000000000'),
    ('2659799257229/6000000000000000', '106488928679/240000000000000'),
    ('314954555417/600000000000000', '787939918763/1500000000000000'),
    ('1217530203413/2000000000000000', '1218204654199/2000000000000000'),
    ('4165178758679/6000000000000000', '4167029268029/6000000000000000'),
    ('4684176470717/6000000000000000', '937174127203/1200000000000000'),
    ('5206966839587/6000000000000000', '1041703925701/1200000000000000'),
    ('5731363703357/6000000000000000', '5732788793351/6000000000000000'),
    ('6255541384729/6000000000000000', '6256850842267/6000000000000000'),
    ('564831380779/500000000000000', '564931775211/500000000000000'),
    ('3648700217911/3000000000000000', '3649255214407/3000000000000000'),
    ('976594892569/750000000000000', '3906891603151/3000000000000000'),
    ('4161590251993/3000000000000000', '4162063361221/3000000000000000'),
    ('8827946374543/6000000000000000', '8828821822639/6000000000000000'),
    ('777205780931/500000000000000', '194318339979/125000000000000'),
    ('654551533467/400000000000000', '3273008426327/2000000000000000'),
    ('10302975706067/6000000000000000', '10303674263243/6000000000000000'),
    ('1796712675513/1000000000000000', '449205237451/250000000000000'),
    ('2812485416669/1500000000000000', '1125054642059/600000000000000'),
    ('2927949619921/1500000000000000', '5856181034321/3000000000000000'),
    ('6082861207903/3000000000000000', '6083124147787/3000000000000000'),
    ('4203877263587/2000000000000000', '4204041049541/2000000000000000'),
    ('13049481354647/6000000000000000', '13049941004429/6000000000000000'),
    ('2695851347101/1200000000000000', '13479686861231/6000000000000000'),
    ('1737621129151/750000000000000', '434417886841/187500000000000'),
    ('14314652431237/6000000000000000', '14315030850379/6000000000000000'),
    ('14720359204091/6000000000000000', '14720714488721/6000000000000000'),
    ('251969289693/100000000000000', '2519748599913/1000000000000000'),
    ('5169376160163/2000000000000000', '5169480988789/2000000000000000'),
    ('5296788265951/2000000000000000', '5296886951373/2000000000000000'),
    ('5421655859689/2000000000000000', '5421748836573/2000000000000000'),
    ('2772007574167/1000000000000000', '554410292433/200000000000000'),
    ('566390443661/200000000000000', '707998417403/250000000000000'),
]

def lean(q):
    q = F(q)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'

def dag_text(nodes):
    s = 'import Hf4QuadCompactIntegral\n\nnoncomputable section\nnamespace Hf4Quad.CompactDag\n'
    for i, (op, *args) in enumerate(nodes):
        if op == 'var': rhs = 't'
        elif op == 'rad': rhs = 'TerminalE.radical'
        elif op == 'const': rhs = lean(args[0])
        elif op == 'neg': rhs = f'-f{args[0]} t'
        elif op == 'inv': rhs = f'(f{args[0]} t)⁻¹'
        else: rhs = f'f{args[0]} t'+('+' if op == 'add' else '*')+f'f{args[1]} t'
        s += f'def f{i} ({"_" if op in ["rad","const"] else "t"} : ℝ) : ℝ := {rhs}\n'
    s += f'\ntheorem compact_kernel_dag (t : ℝ) : compactKernel t = f{len(nodes)-1} t := by\n'
    ds = ','.join(f'f{i}' for i in reversed(range(len(nodes))))
    s += '  simp only [compactKernel,slCompact,suCompact,lowZ,upZ,SigmaRationalOuterFTC.jointNum,SigmaRationalOuterFTC.jointDen,'+ds+',div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul]\n\nend Hf4Quad.CompactDag\n'
    return s

def panel_text(nodes, i):
    models = evaluate(nodes,i)
    m,h = F(41+2*i,40), F(1,40)
    last = len(nodes)-1
    p,e = models[-1]
    lo,up = (p[0]+p[2]/3-e)/20, (p[0]+p[2]/3+e)/20
    target_lo,target_up = map(F,TARGETS[i])
    assert target_lo <= lo <= up <= target_up, (i,lo,up,TARGETS[i])
    s = f'\nnamespace Hf4Quad.Panel{i}\nopen Hf4Quad.CompactDag Hf4Quad.RationalModel\n'
    for j, ((op,*args),(p,e)) in enumerate(zip(nodes,models)):
        s += f'\ndef c{j} : Certificate := ⟨'+','.join(lean(x) for x in [*p,e])+'⟩\n'
        s += f'theorem h{j} : c{j}.Valid (fun x => f{j} ({lean(m)}+{lean(h)}*x)) := '
        if op in ['var','rad','const']:
            base = f'variableModel {lean(m)} {lean(h)}' if op=='var' else 'radical' if op=='rad' else f'constant ({lean(args[0])})'
            s += (f'by\n  convert {base} using 1 <;> norm_num [Certificate.Valid,Certificate.cubic,c{j},f{j}]\n' if op == 'rad' else f'by\n  simpa [Certificate.Valid,Certificate.cubic,c{j},f{j}] using {base}\n')
        elif op == 'neg': s += f'h{args[0]}.negTo (by decide +kernel)\n'
        elif op == 'inv': s += f'h{args[0]}.inv (by decide +kernel)\n'
        else: s += f'h{args[0]}.{op} h{args[1]} (by decide +kernel)\n'
    s += f'''\ntheorem compact_model : c{last}.Valid (fun x => compactKernel ({lean(m)}+{lean(h)}*x)) := by
  simpa only [compact_kernel_dag] using h{last}

theorem mass_bounds : ({lean(target_lo)}:ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass {lean(m-h)} {lean(m+h)} ∧
    SigmaActualBlockSeparable.endpointCellMass {lean(m-h)} {lean(m+h)} ≤ {lean(target_up)} := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<{lean(h)}) (by norm_num : (1:ℝ)≤{lean(m)}-{lean(h)}) (by norm_num : ({lean(m)}:ℝ)+{lean(h)}≤3) compact_model
  norm_num [Certificate.cubic,c{last}] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel{i}
'''
    return s

def generate():
    nodes = compact()
    files = {'Hf4QuadCompactDag.lean':dag_text(nodes)}
    header = 'import Hf4QuadCompactDag\nimport Hf4QuadRationalModel\n\nnoncomputable section\n'
    files['Hf4QuadPanel0.lean'] = header+panel_text(nodes,0)
    for b in range(13):
        files[f'Hf4QuadBatch{b}.lean'] = header+''.join(panel_text(nodes,i) for i in range(1+3*b,4+3*b))
    return files

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--check',action='store_true')
    ap.add_argument('--panel',type=int,help='Generate only a single panel and the common DAG for testing.')
    args=ap.parse_args()
    if args.panel is None: files=generate()
    else:
        assert 0<=args.panel<40
        nodes=compact()
        files={'Hf4QuadCompactDag.lean':dag_text(nodes),f'Hf4QuadPanel{args.panel}.lean':
            'import Hf4QuadCompactDag\nimport Hf4QuadRationalModel\n\nnoncomputable section\n'+panel_text(nodes,args.panel)}
    if args.check:
        for n,s in files.items():assert (args.output_dir/n).read_text()==s,n
    else:
        args.output_dir.mkdir(parents=True,exist_ok=True)
        for n,s in files.items():(args.output_dir/n).write_text(s)
    print(('CHECK_PASS' if args.check else 'GENERATED'),len(files),'modules;',len(compact()),'DAG nodes')

if __name__=='__main__':main()
