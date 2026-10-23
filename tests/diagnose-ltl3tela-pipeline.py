#!/usr/bin/env python3
"""Audit LTL3TELA default selection against its isolated positive SLAA route."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tool', type=Path, default=Path('build-local/external/ltl3tela-master/ltl3tela'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/ltl3tela-pipeline'))
    ap.add_argument('--csv', type=Path, default=Path('tests/ltl3tela-pipeline.csv'))
    ap.add_argument('--timeout', type=float, default=30)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec); spec.loader.exec_module(comparison)
    cases = [r for r in csv.DictReader(open('tests/ltl-fragment-results.csv')) if r['tool'] == 'cola']
    variants = {'default': ['-D1', '-x1'], 'isolated_slaa': ['-D1', '-b0', '-n0', '-l0', '-x1']}
    fields = ['case', 'sources', 'formula', 'variant', 'status', 'states', 'edges', 'colours', 'elapsed_ms', 'winner', 'original_completed_states', 'detail']
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.tool, Path(__file__)]}
    def measure(case, variant, flags):
        row = dict.fromkeys(fields, ''); row.update({k: case[k] for k in ['case', 'sources', 'formula']})
        row.update(variant=variant, status='ok'); d=args.artifacts/case['case']/variant;d.mkdir(parents=True,exist_ok=True)
        def run(cmd,name):
            code,elapsed=comparison.execute(cmd,d/name,d/(name+'.stderr'),args.timeout,dict(os.environ))
            return code,d/name,elapsed
        code,source,elapsed=run([str(args.tool.resolve()),*flags,'-f',case['formula']],'input.hoa')
        row['winner']=(d/'input.hoa.stderr').read_text(errors='replace').strip()
        row['elapsed_ms']=round(elapsed,3)
        if code:
            row.update(status='frontend-timeout' if code=='timeout' else 'acceptance-capacity' if code==32 else 'frontend-crash' if isinstance(code,int) and code<0 else 'frontend-error',detail=str(code));return row
        code,original,_=run(['autfilt',str(source),'--complete','--remove-unreachable-states','--stats=%s'],'original.stats')
        if code:raise RuntimeError('original metrics failed')
        row['original_completed_states']=int(original.read_text().strip())
        code,final,_=run(['autfilt',str(source),'--simplify-acceptance','-D','-G','--low','--complete','--remove-unreachable-states'],'final.hoa')
        if code:raise RuntimeError('normalisation failed')
        code,stats,_=run(['autfilt',str(final),'--stats=%s,%e,%a,%d,%p'],'stats')
        if code:raise RuntimeError('metrics failed')
        s,e,a,det,total=map(int,stats.read_text().strip().split(','));assert det==total==1
        row.update(states=s,edges=e,colours=a)
        reference=Path('build-local/owl-comparison')/case['case']/(case['reference_tool']+'.hoa')
        code,_,_=run(['autfilt','-q',str(final),'--equivalent-to='+str(reference)],'equivalence')
        if code:row.update(status='equivalence-timeout' if code=='timeout' else 'inequivalent')
        return row
    rows=[]
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures=[pool.submit(measure,c,v,f) for c in cases for v,f in variants.items()]
        for future in as_completed(futures):
            r=future.result();rows.append(r)
            with args.csv.with_suffix('.tmp').open('w',newline='') as out:
                w=csv.DictWriter(out,fields,lineterminator='\n');w.writeheader();w.writerows(sorted(rows,key=lambda x:(x['case'],x['variant'])))
            args.csv.with_suffix('.tmp').replace(args.csv)
            print(len(rows),r['sources'],r['variant'],r['status'],r['states'],flush=True)
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in hashes.items())
    args.csv.with_suffix('.json').write_text(json.dumps({'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'sha256':hashes,'variants':variants,'timeout_seconds':args.timeout,'workers':2},indent=2)+'\n')
    assert len(rows)==454 and not any(r['status']=='inequivalent' for r in rows)


if __name__=='__main__':main()
