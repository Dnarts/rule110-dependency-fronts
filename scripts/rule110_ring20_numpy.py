#!/usr/bin/env python3
"""Exact simultaneous enumeration for Rule 110 rings of N=20, with NumPy."""
import json,time
import numpy as np
N=20; MASK=(1<<N)-1; n=1<<N
states=np.arange(n,dtype=np.uint32)
log=[]; start=time.monotonic()
for t in range(131):
    out=(states & 1).astype(np.uint8)
    d=[]
    for j in range(N):
        side=1<<j
        cells=out.reshape(-1,2*side)
        if np.any(cells[:,:side]!=cells[:,side:]): d.append(j)
    row={'t':t,'essential_count':len(d),'all_essential':len(d)==N}
    if t in (0,1,5,10,11,121,130):
        row['essential_positions']=d
        row['image_size']=int(np.unique(states).size)
        row['capacity_ceil_bits']=int(np.ceil(np.log2(row['image_size'])))
    log.append(row)
    l=((states<<1)|(states>>(N-1))) & MASK
    r=(states>>1)|((states&1)<<(N-1))
    states=((~l & (states | r)) | (l & (states ^ r))) & MASK
stats={
    'n':N,'horizon':130,
    'full_essential_range_11_through_130':all(x['all_essential'] for x in log[11:]),
    't121':log[121],
    't11':log[11],
    't10':log[10],
    'all_counts':[row['essential_count'] for row in log],
    'sampled_rows':[row for row in log if 'image_size' in row],
    'runtime_s':round(time.monotonic()-start,3)
}
print(json.dumps({k:v for k,v in stats.items() if k!='all_counts'},indent=2))
open('ring20_audit.json','w').write(json.dumps(stats,indent=2)+'\n')
