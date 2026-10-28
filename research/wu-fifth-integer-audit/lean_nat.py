"""Restricted, fail-closed Lean Nat expression interpreter (not a Lean checker)."""
import re

def definition(source,name):
 m=re.findall(r'^def '+re.escape(name)+r'\b[^\n]*?:=(.*?)(?=\n(?:def |theorem |private theorem |end |@|/--)|\Z)',source,re.M|re.S)
 assert len(m)==1,('definition',name)
 return m[0].strip()

def expression(text,env,functions):
 text=text.strip();env=dict(env)
 while text.startswith('let '):
  m=re.match(r'let (\w+) := ([^\n]+)\n(.*)',text,re.S);assert m,('unsupported let',text)
  env[m[1]]=expression(m[2],env,functions);text=m[3].strip()
 tokens=re.findall(r'[A-Za-z_][\w.]*|\d+|[()+*/^\-]',text)
 assert re.sub(r'\s+','',text)==''.join(tokens),('unexpected expression',text)
 cursor=0
 def atom():
  nonlocal cursor
  assert cursor<len(tokens),'incomplete expression'
  token=tokens[cursor];cursor+=1
  if token=='(':
   value=parse(0);assert tokens[cursor]==')';cursor+=1;return value
  if token.isdigit():return int(token)
  if token in env:return env[token]
  assert token in functions,('unknown identifier',token)
  arity,fn=functions[token];return fn(*(atom() for _ in range(arity)))
 def parse(minimum):
  nonlocal cursor
  value=atom();prec={'+':1,'-':1,'*':2,'/':2,'^':3}
  while cursor<len(tokens) and tokens[cursor] in prec and prec[tokens[cursor]]>=minimum:
   op=tokens[cursor];cursor+=1
   right=parse(prec[op]+(0 if op=='^' else 1))
   if op=='+':value+=right
   elif op=='-':value=max(0,value-right)
   elif op=='*':value*=right
   elif op=='/':value=value//right if right else 0
   else:
    assert 0<=right<=23,('exponent',right);value=value**right
  return value
 value=parse(0);assert cursor==len(tokens),('unparsed tokens',tokens[cursor:]);return value

def evaluator(sources):
 data=sources['WR2ClassicalFifthIntegerData.lean'];poly=sources['WR2ClassicalFifthIntegerPolynomial.lean'];horner=sources['WR2IntegerLogHorner.lean'];functions={}
 def register(key,source,name,params):
  body=definition(source,name)
  def evaluate(*args):
   return expression(body,dict(zip(params,args)),functions)
  functions[key]=(len(params),evaluate)
 register('commonDen',horner,'commonDen',[])
 register('homogeneous',horner,'homogeneous',['p','q'])
 register('numerator',horner,'numerator',['p','q'])
 register('denominator',horner,'denominator',['q'])
 register('FifthIntegerPolynomial.commonDen',poly,'commonDen',[])
 register('FifthIntegerPolynomial.homogeneous',poly,'homogeneous',['Y','D'])
 register('scale',data,'scale',[])
 # The pattern-definition declarations lack :=, unlike ordinary definitions.
 def pattern(name):
  m=re.search(r'^def '+name+r'\b[^\n]*\n(.*?)(?=\ndef |\n\n)',data,re.M|re.S);assert m,name
  rows=re.findall(r'^  \| (.*?) => (.*)$',m[1],re.M);assert rows,name;return rows
 gridD=pattern('gridDenominator');gridN=pattern('gridNumerator')
 assert [a for a,b in gridD]==['.middle','_']
 assert [a for a,b in gridN]==['.initial, i','.middle, i','.terminal, i']
 functions['gridDenominator']=(1,lambda b:expression(next(v for p,v in gridD if p=='.'+b or p=='_'),{},functions))
 functions['gridNumerator']=(2,lambda b,i:expression(next(v for p,v in gridN if p=='.'+b+', i'),{'i':i},functions))
 for name,params in [('extraNumerator',['branch','i']),('extraDenominator',['branch']),('ratioNumerator',['branch','i']),('ratioDenominator',['branch','i'])]:
  body=definition(data,name);assert body.startswith('match branch with\n'),name
  rows=re.findall(r'\|\s*(\.\w+|_)\s*=>\s*(.*?)(?=\n\s*\||\Z)',body,re.S);assert len(rows)==2,name
  def match_eval(*args,rows=rows,params=params):
   env=dict(zip(params,args));branch=env['branch']
   term=next(t for label,t in rows if label=='.'+branch or label=='_')
   return expression(term,env,functions)
  functions[name]=(len(params),match_eval)
 for name in ['rawNumerator','rawDenominator']:register(name,data,name,['branch','i'])
 body=definition(data,'paymentNumerator')
 assert re.sub(r'\s+','',body)=='ifi<1024thenrawNumeratorbranchi/rawDenominatorbranchielse0','payment support/formula'
 def payment(branch,i):
  return expression('rawNumerator branch i/rawDenominator branch i',{'branch':branch,'i':i},functions) if i<1024 else 0
 return payment
