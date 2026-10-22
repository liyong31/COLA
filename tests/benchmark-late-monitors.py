#!/usr/bin/env python3
"""Compare early and late products with deterministic global window monitors."""
import csv
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path


def main():
    root=Path('build-local/late-monitors');root.mkdir(exist_ok=True)
    # macOS /usr/bin/time strips DYLD_*; libtool's launcher sets the library
    # path again in its child before exec. Both routes use the same launcher.
    driver=Path('build-local/tests/late-monitor')
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(Path('build-local/src/.libs').resolve()))
    rows=[]
    for depth in range(7):
        kernel='y'
        for _ in range(depth):kernel='x & X('+kernel+')'
        formula='F(a & XG b) & GF('+kernel+')'
        reference=root/('reference-'+str(depth)+'.hoa')
        reference.write_bytes(subprocess.check_output(['ltl2tgba','-D','-G','-f',formula],timeout=30))
        for mode,minimised in [(m,v) for v in [False,True] for m in ['early','late']]:
            name=mode+('-minimised' if minimised else '')+'-'+str(depth)
            output=root/(name+'.hoa')
            command=['/usr/bin/time','-l',str(driver),mode,str(depth)]
            if minimised:command+=['minimised']
            with output.open('w') as out:
                result=subprocess.run(command,stdout=out,
                                      stderr=subprocess.PIPE,text=True,env=env,timeout=30,check=True)
            (root/(name+'.stderr')).write_text(result.stderr)
            subprocess.run(['autfilt','-q',str(output),'--is-deterministic',
                            '--equivalent-to='+str(reference)],timeout=30,check=True)
            values={}
            for line in result.stderr.splitlines():
                if ': ' in line:
                    key,value=line.split(': ',1)
                    if key in ['construction-ms','input-states','monitor-states','skeleton-deterministic-states','raw-states','raw-colours']:values[key]=value
            rss=re.search(r'(\d+)\s+maximum resident set size',result.stderr)
            metrics=subprocess.check_output(['autfilt',str(output),'--stats=%s,%e,%a'],text=True).strip().split(',')
            row=dict(depth=depth,mode=mode,monitor_mode='minimised' if minimised else 'full-history',formula=formula,status='ok',states=metrics[0],edges=metrics[1],colours=metrics[2],
                     peak_rss_bytes=rss.group(1) if rss else '',**values)
            rows.append(row);print(depth,mode,metrics,values,flush=True)
    with open('tests/late-monitor-results.csv','w',newline='') as out:
        writer=csv.DictWriter(out,list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
    paths=[driver,Path('build-local/tests/.libs/late-monitor'),Path('tests/late-monitor.cpp'),Path(__file__),Path('build-local/src/.libs/libcola.0.dylib')]
    Path('tests/late-monitor-results.json').write_text(json.dumps({'sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'method':'Fresh process per route/depth; construction timer excludes source oracle and equivalence; macOS time -l RSS',
        'scope':'Boolean conjunction with a deterministic global monitor, not arbitrary acceptance-parametric pruning'},indent=2)+'\n')


if __name__=='__main__':main()
