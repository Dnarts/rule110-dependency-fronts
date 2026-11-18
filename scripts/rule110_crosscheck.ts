/**
 * Independent Rule 110 checks in TypeScript, no runtime libraries.
 * Compile: tsc --strict --target ES2022 --module commonjs rule110_crosscheck.ts
 * Run:     node rule110_crosscheck.js
 *
 * Finite enumerations only; see rule110_certificate_proof_ru.md for induction.
 */

const must = (condition: boolean, msg: string): void => {
  if (!condition) throw new Error(msg);
};

function local(l: number, c: number, r: number, rule = 110): number {
  return (rule >> ((l << 2) | (c << 1) | r)) & 1;
}

function evolveWindow(data: number[], steps: number): number[] {
  let w = data.slice();
  for (let t = 0; t < steps; t++) {
    const out: number[] = [];
    for (let i = 0; i + 2 < w.length; i++) out.push(local(w[i], w[i + 1], w[i + 2]));
    w = out;
  }
  return w;
}

function checkLocal(): void {
  for (let l = 0; l <= 1; l++) {
    for (let c = 0; c <= 1; c++) {
      for (let r = 0; r <= 1; r++) {
        must(local(l,c,r) === (c ^ r ^ (c & r) ^ (l & c & r)), 'ANF');
      }
    }
  }
  for (let c=0;c<2;c++) for(let r=0;r<2;r++) {
    must((local(1,c,r)^local(0,c,r)) === (c&r), 'left derivative');
  }
  for (let m=0;m<128;m++) {
    const xs=Array.from({length:7},(_,i)=>(m>>i)&1);
    const ys=xs.slice(); ys[0]^=1;
    must(evolveWindow(xs,3)[0]===evolveWindow(ys,3)[0],`local 7-window mask ${m}`);
  }
}

type Defect = {bg: number[], S: Set<number>};
function signature(d: Defect): string {
  return JSON.stringify({bg:d.bg, S:[...d.S].sort((a,b)=>a-b)});
}
function stepDefect(d: Defect): Defect {
  const p=d.bg.length;
  const nb=Array.from({length:p},(_,i)=>local(d.bg[(i-1+p)%p],d.bg[i],d.bg[(i+1)%p]));
  const ns=new Set<number>();
  if (d.S.size) {
    const ss=[...d.S];
    const lo=Math.min(...ss)-1, hi=Math.max(...ss)+1;
    const at=(i:number)=>d.bg[((i%p)+p)%p]^(d.S.has(i)?1:0);
    for(let i=lo;i<=hi;i++) {
      const result=local(at(i-1),at(i),at(i+1));
      if(result!==nb[((i%p)+p)%p]) ns.add(i);
    }
  }
  return {bg:nb,S:ns};
}
function shifted(d: Defect, by: number): Defect {
  const p=d.bg.length;
  return {
    bg:Array.from({length:p},(_,i)=>d.bg[((i-by)%p+p)%p]),
    S:new Set([...d.S].map(x=>x+by))
  };
}
function front(t:number):number {return t-Math.floor(t/3);}
function checkDefect(): void {
  const hist:Defect[]=[{bg:[1,0,1,1],S:new Set([2])}];
  for(let t=1;t<=6;t++)hist.push(stepDefect(hist[t-1]));
  must(signature(hist[6])===signature(shifted(hist[3],2)), 'Y6 != shift2(Y3)');
  for(let t=0;t<=6;t++) {
    must(Math.max(...hist[t].S) === 2+front(t),`front t=${t}`);
  }
}
function stepRing(state:number,n:number,rule:number):number {
  let result=0;
  for(let i=0;i<n;i++) {
    result |= local((state>>>((i-1+n)%n))&1,(state>>>i)&1,
                    (state>>>((i+1)%n))&1,rule)<<i;
  }
  return result>>>0;
}
function ringResults(rule:number,n:number,t:number):{states:number,essential:number[]} {
  const count=1<<n;
  let trajectory=Array.from({length:count},(_,i)=>i);
  for(let k=0;k<t;k++)trajectory=trajectory.map(x=>stepRing(x,n,rule));
  const outputs=trajectory.map(x=>x&1);
  const essential:number[]=[];
  for(let j=0;j<n;j++) {
    if(outputs.some((x,u)=>x!==outputs[u^(1<<j)]))essential.push(j);
  }
  return {states:new Set(trajectory).size,essential};
}
function main(): void {
  checkLocal();
  checkDefect();
  const a4=ringResults(110,5,4), a5=ringResults(110,5,5);
  const b2=ringResults(90,4,2);
  must(a4.states===2 && a4.essential.length===5, 'Rule110 N=5 t=4');
  must(a5.states===1 && a5.essential.length===0, 'Rule110 N=5 t=5');
  must(b2.states===1 && b2.essential.length===0, 'Rule90 N=4 t=2');
  console.log('PASS [TypeScript]: 8 ANF cases, 4 derivatives, 128 windows');
  console.log('PASS [TypeScript]: Y6=shift2(Y3), phase front t=0..6');
  console.log('PASS [TypeScript]: Rule110 N=5 collapse; Rule90 N=4 cancellation');
}
main();
