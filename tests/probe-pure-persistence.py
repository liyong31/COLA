#!/usr/bin/env python3
"""Check pure-persistence certificates on actual SLAA and configuration graphs."""
import csv
import hashlib
import importlib.util
import json
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


def read(name):
    with open('tests/' + name) as source: return list(csv.DictReader(source))


def main():
    spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('compare-ltl-sizes.py'))
    comparison = importlib.util.module_from_spec(spec);spec.loader.exec_module(comparison)
    tool = Path('build-local/external/ltl3tela-master/ltl3tela').resolve()
    driver = Path('build-local/tests/.libs/pure-persistence-driver')
    env = dict(os.environ,DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    cases = []
    for r in read('ltl-fragment-results.csv'):
        if r['tool'] == 'cola': cases.append(dict(case=r['case'],family='literature',sources=r['sources'],formula=r['formula'],path=None))
    for r in read('ltl-slaa-shapes.csv'):
        cases.append(dict(case=r['case']+'_'+r['variant']+'_'+r['polarity'],family='shape',sources=r['sources'],
            formula=r['formula'] if r['polarity']=='positive' else '!('+r['formula']+')',
            path=Path('build-local/slaa-shapes')/r['case']/(r['variant']+'_'+r['polarity'])/'input.slaa.hoa'))
    preservation=[c for c in cases if c['family']=='literature' and c['sources'] in ['DwyerAC98.ltl:11','DwyerAC98.ltl:13']]
    preservation += [dict(case='nested-persistence',sources='F(Ga & X(Fb))',formula='F(Ga & X(Fb))'),
                     dict(case='recurring-spawn',sources='GF a',formula='GF a')]
    for c in preservation:
        for name,flags in [('baseline',[]),('no_simplification',['-s0']),
                           ('no_merging',['-F0','-G0','-c0']),('both_off',['-s0','-F0','-G0','-c0'])]:
            cases.append(dict(c,case=c['case']+'_'+name,family='preservation',path=None,flags=flags))
    rows = []; root = Path('build-local/pure-persistence');root.mkdir(exist_ok=True)
    fields = ['case','family','sources','formula','flags','status','syntactic','pure','reason','states','configurations','nonsingleton_sccs','enumeration_limit']

    def measure(c):
        row = dict.fromkeys(fields,'');row.update({k:c[k] for k in ['case','family','sources','formula']});row['status']='ok'
        row['flags']=' '.join(c.get('flags',[]))
        directory=root/c['case'];directory.mkdir(exist_ok=True)
        source=c['path']
        if source is None:
            source=directory/'input.slaa.hoa'
            rc,_=comparison.execute([str(tool),'-D0','-b0','-n0','-l0','-t0',*c.get('flags',[]),'-p1','-f',c['formula']],source,directory/'frontend.stderr',5,env)
            if rc:row['status']='frontend-unavailable';return row
        if not source.exists():row['status']='frontend-unavailable';return row
        output=directory/'certificate.json'
        rc,_=comparison.execute([str(driver),str(source),c['formula']],output,directory/'certificate.stderr',5,env)
        if rc:row['status']='certificate-timeout' if rc=='timeout' else 'certificate-error';return row
        data=json.loads(output.read_text())
        for k in fields:
            if k in data:row[k]=data[k]
        if data['pure'] and data.get('nonsingleton_sccs',0):raise AssertionError('pure configuration SCC counterexample')
        return row

    with ThreadPoolExecutor(max_workers=2) as pool:
        for future in as_completed([pool.submit(measure,c) for c in cases]):
            r=future.result();rows.append(r)
            with open('tests/pure-persistence-results.csv','w',newline='') as out:
                writer=csv.DictWriter(out,fields,lineterminator='\n');writer.writeheader();writer.writerows(sorted(rows,key=lambda r:(r['family'],r['case'])))
            print(len(rows),r['family'],r['sources'],r['status'],r['pure'],r['reason'],flush=True)
    paths=[driver,tool,Path(__file__),Path('tests/pure-persistence-driver.cpp')]
    Path('tests/pure-persistence-results.json').write_text(json.dumps({'sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'configuration_budget':4096,'work_budget':65536,'timeout_seconds_per_process':5,'workers':2,
        'scope':'Graph and syntax certificates only; no alternating acceptance lifting'},indent=2)+'\n')
    assert len(rows)==543 and not any(r['status']=='certificate-error' for r in rows)


if __name__=='__main__':main()
