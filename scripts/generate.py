"""Generate independently checkable block certificates, run from lean/."""
from pathlib import Path
N = 5520
mask = 2**N-1

def step(u):
    left = ((u << 1) & mask) | (u >> (N-1))
    right = (u >> 1) | ((u & 1) << (N-1))
    return (u | right) ^ (left & u & right)

pairs = []
for n, w in [(8,244),(10,632),(10,976),(10,576),(4,13),(6,52),(6,48)]:
    b = mask//(2**n-1)*w
    for p in range(n):
        u = ((b >> p) | (b << (N-p))) & mask
        pairs.append((u,u^(1 << 2760)))
prefix = 'namespace Rails.Finite\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 8192\n'
blocks = []
for t in range(0,2485,25):
    length = min(25,2485-t)
    start = 'pairs' if t == 0 else f'snap{t}'
    data = ['import FiniteBase\n',prefix]
    if t:
        literal = ',\n'.join(f'(0x{x:x}#5520,0x{y:x}#5520)' for x,y in pairs)
        data.append(f'def {start} : List Pair := [{literal}]\n')
    Path(f'Snap{t}.lean').write_text(''.join(data)+'end Rails.Finite\n')
    for dt in range(length):
        time = t+dt
        coverage = 0
        for x,y in pairs:
            coverage |= x^y
        target = ((1<<(time+time-time//3+1))-1) << (2760-time)
        assert coverage & target == target, time
        pairs = [(step(x),step(y)) for x,y in pairs]
    blocks.append((t,length,start))
for t,length,start in blocks:
    nxt = t+length
    imports = f'import Snap{t}\n'
    if nxt<2485:
        imports += f'import Snap{nxt}\n'
    data = [imports,prefix,f'theorem check{t} : checkRows {length} {t} {start} = true := by decide +kernel\n']
    if nxt<2485:
        data.append(f'theorem link{t} : iterate {length} {start} = snap{nxt} := by decide +kernel\n')
    Path(f'Block{t}.lean').write_text(''.join(data)+'end Rails.Finite\n')
s = ''.join(f'import Block{t}\n' for t,_,_ in blocks)+prefix
for t,length,start in reversed(blocks):
    s += f'theorem tail{t} : checkRows {2485-t} {t} {start} = true := by\n'
    if t+length==2485:
        s += f'  exact check{t}\n'
    else:
        s += f'  apply concatenate {length} {2485-t-length} {t} {start} (check{t})\n  rw [link{t}]\n  exact tail{t+length}\n'
Path('CertFinal.lean').write_text(s+'theorem certificate := tail0\nend Rails.Finite\n'.replace('theorem certificate','abbrev certificate'))
print('All',sum(2*t-t//3+1 for t in range(2485)),'cells covered in',len(blocks),'blocks.')
