#!/usr/bin/env python3
"""Portable exact-deletion audit; static evidence only, never Lean acceptance."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
COMMIT = 'c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'
PREFIX = 'research/wu2008/src/'
def require(ok, message):
    if not ok: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def code_only(text: str, *, keep_strings: bool = False) -> str:
    """Mask nested comments and, by default, strings; preserve text offsets.

    This is a lexical check, not a Lean parser or a kernel verifier.
    """
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
                continue
        elif string:
            if text[i] == "\\":
                if not keep_strings:
                    out[i] = " "
                i += 1
                if i < len(text):
                    if not keep_strings:
                        out[i] = " "
                    i += 1
                continue
            if text[i] == '"':
                string = False
            if not keep_strings and text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
            continue
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out[i:j] = " " * (j - i)
            i = j
            continue
        elif text[i] == '"':
            string = True
            if keep_strings:
                i += 1
                continue
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def count_code_lines(text: str) -> int:
    return sum(bool(line.strip()) for line in code_only(text, keep_strings=True).splitlines())


def stats(text):
    return dict(effective_lines=count_code_lines(text), physical_lines=len(text.splitlines()), utf8_bytes=len(text.encode('utf-8')))
def qname(text, pos, name):
    stack=[]
    for m in re.finditer(r'^(namespace|section|end)\b([^\n]*)', code_only(text[:pos]), re.M):
        kind, rest=m.group(1),m.group(2).strip()
        if kind == 'end':
            require(bool(stack), 'unbalanced source contexts')
            stack.pop()
        else: stack.append((kind, rest))
    prefix='.'.join(v for k,v in stack if k=='namespace')
    return name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(x for x in [prefix,name] if x)
def audit(repo, candidate_root, manifest):
    require(manifest['baseline_commit']==COMMIT and manifest['baseline_prefix']==PREFIX, 'fixed baseline identity')
    require(len(manifest['files'])==9, 'expected nine files')
    require(len({r['file'] for r in manifest['files']})==9, 'duplicate files')
    results=[]; count=0
    for row in manifest['files']:
        rel=row['file']; require(not Path(rel).is_absolute() and '..' not in Path(rel).parts, 'unsafe path')
        blob=subprocess.run(['git','-C',str(repo),'show',COMMIT+':'+PREFIX+rel],check=True,stdout=subprocess.PIPE).stdout
        require(sha(blob)==row['before_sha256'], 'baseline blob SHA: '+rel)
        old=blob.decode('utf-8',errors='strict'); require(old.encode('utf-8')==blob, 'UTF8 roundtrip')
        candidate=(candidate_root/rel).read_bytes(); new=candidate.decode('utf-8',errors='strict')
        require(sha(candidate)==row['after_sha256'], 'candidate SHA: '+rel)
        last=0; pieces=[]
        for r in row['deletions']:
            start,end=r['start'],r['end']
            require(type(start) is int and type(end) is int and 0<=last<=start<end<=len(old), 'invalid/overlapping Unicode interval')
            fragment=old[start:end]
            require(sha(fragment.encode('utf-8'))==r['fragment_sha256'], 'fragment SHA: '+r['qname'])
            ds=r['declaration_start']; require(start<=ds<end, 'declaration offset')
            require(not code_only(old[start:ds]).strip(), 'prefix removes code')
            code=code_only(fragment)
            found=re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|structure|class)\s+(\S+)',code,re.M)
            require(found==[(r['kind'],r['name'])] and r['kind'] in ['theorem','lemma'], 'deletion declaration')
            require(qname(old,ds,r['name'])==r['qname'], 'source QName')
            require(not re.search(r'^(?:namespace|section|end|open|variable|set_option|attribute|local|scoped|notation|infix|prefix|postfix|syntax|macro|elab|import)\b',code,re.M), 'removed context command')
            pieces.append(old[last:start]); last=end; count+=1
        pieces.append(old[last:])
        require(''.join(pieces)==new, 'survivor/context reconstruction: '+rel)
        a,b=stats(old),stats(new)
        require(a==row['before'] and b==row['after'], 'file counts')
        results.append(dict(file=rel,before=a,after=b,before_sha256=sha(blob),after_sha256=sha(candidate)))
    require(count==383,'expected 383 deletions')
    delta={k:sum(r['before'][k]-r['after'][k] for r in results) for k in results[0]['before']}
    require(delta==dict(effective_lines=10924,physical_lines=11516,utf8_bytes=514688),'expected reductions')
    return dict(status='static_only',static_checks='PASS',lean_acceptance=False,baseline_commit=COMMIT,deleted_declarations=count,files=results,reduction=delta,all_surviving_text_character_identical=True,scope='nine listed files only; dependency/type/kernel validation is separate',qname_semantics='source-level namespace-qualified names; private elaborator-generated names are not claimed')
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path.cwd()); p.add_argument('--candidate-root',type=Path)
    p.add_argument('--manifest',type=Path,default=Path(__file__).with_name('manifest.json')); p.add_argument('--output',type=Path)
    a=p.parse_args(); raw=a.manifest.read_bytes()
    report=audit(a.repo,a.candidate_root or a.repo/PREFIX,json.loads(raw))
    report['manifest_sha256']=sha(raw);report['audit_sha256']=sha(Path(__file__).read_bytes())
    data=json.dumps(report,indent=2)+'\n'
    if a.output: a.output.write_text(data)
    print(data,end='')
if __name__=='__main__': main()
