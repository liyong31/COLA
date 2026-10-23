#!/usr/bin/env python3
"""Isolate OWL polarity/fragment portfolios from its LDBA ranking algorithm."""
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
    ap.add_argument('--owl', type=Path, default=Path('build-local/external/owl-21.0/bin/owl'))
    ap.add_argument('--artifacts', type=Path, default=Path('build-local/owl-gap-controls'))
    ap.add_argument('--csv', type=Path, default=Path('tests/owl-gap-controls.csv'))
    ap.add_argument('--timeout', type=float, default=10)
    args = ap.parse_args()
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec); spec.loader.exec_module(comparison)
    cases = [r for r in csv.DictReader(open('tests/ltl-fragment-results.csv')) if r['tool'] == 'cola']
    variants = {
        'positive': ['--EKRS17-skip-complement'],
        'no_portfolio': ['--skip-translation-portfolio'],
        'positive_no_portfolio': ['--EKRS17-skip-complement', '--skip-translation-portfolio'],
        'eks20_positive_no_portfolio': ['--EKRS17-skip-complement', '--skip-translation-portfolio']}
    fields = ['case', 'sources', 'formula', 'variant', 'status', 'states', 'edges', 'colours', 'elapsed_ms', 'detail']
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.owl, Path(__file__)]}
    def measure(case, variant, flags):
        row = dict.fromkeys(fields, ''); row.update({k: case[k] for k in ['case', 'sources', 'formula']})
        row.update(variant=variant, status='ok'); d=args.artifacts/case['case']/variant;d.mkdir(parents=True,exist_ok=True)
        def run(cmd,name):
            code,elapsed=comparison.execute(cmd,d/name,d/(name+'.stderr'),args.timeout,dict(os.environ))
            return code,d/name,elapsed
        alg='EKS20_EKRS17' if variant.startswith('eks20') else 'SEJK16_EKRS17'
        code,source,elapsed=run([str(args.owl.resolve()),'ltl2dpa','-t',alg,*flags,'-f',case['formula']],'input.hoa')
        row['elapsed_ms']=round(elapsed,3)
        if code:
            row.update(status='frontend-timeout' if code=='timeout' else 'frontend-error',detail=str(code));return row
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
    assert len(rows)==908 and not any(r['status'] in ['frontend-error','inequivalent'] for r in rows)


if __name__=='__main__':main()
