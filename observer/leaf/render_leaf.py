"""Render canonical TSV and validate its hashes, symbol addresses and SVG readback."""
import argparse
import ast
import csv
import hashlib
import io
from pathlib import Path
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
TSV = HERE / 'leaf.tsv'
SVG = HERE / 'leaf.svg'
BONES = dict(S='SOURCE', I='IDENTITY', M='SEMANTICS', T='TRANSITION', A='ACTION', O='OBSERVATION')
SLOTS = ('ORIGIN', 'STATE', 'CARRIER', 'LEAF', 'WITNESS', 'FAILURE')
FIELDS = 'leaf law state origin witness value abi leaf_origin'.split()
NS = 'http://www.w3.org/2000/svg'
ET.register_namespace('', NS)


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def file_hash(path):
    return 'sha256:' + hashlib.sha256(path.read_bytes()).hexdigest()


def audit_rows(rows):
    expected = [code + str(i) for code in BONES for i in range(1, 7)]
    require([r['law'] for r in rows] == expected, 'Expected 36 unique slots in spine order')
    for key in ('leaf', 'abi', 'leaf_origin'):
        require(len({r[key] for r in rows}) == 1 and rows[0][key], key)
    require(rows[0]['leaf_origin'] == file_hash(ROOT / 'causal_line.py'), 'Head origin changed')
    for row in rows:
        code, status = row['law'], row['state']
        require(row['value'] and status in {'KNOWN', 'UNKNOWN'}, code)
        if status == 'UNKNOWN':
            require(not row['origin'] and not row['witness'], code + ' UNKNOWN carries a witness')
            continue
        path, sep, symbol = row['witness'].partition('#')
        source = (ROOT / path).resolve()
        require(sep and symbol and source.is_relative_to(ROOT), code + ' invalid witness')
        require(file_hash(source) == row['origin'], code + ' changed witness ' + path)
        contents = source.read_text(encoding='utf8')
        if source.suffix == '.py':
            require(symbol in {n.name for n in ast.parse(contents).body
                               if isinstance(n, (ast.FunctionDef, ast.ClassDef))}, code + ' missing symbol')
        else:
            require(any(line.startswith('## ' + symbol + '. ') for line in contents.splitlines()),
                    code + ' missing section')


def element(parent, tag, attrs=None, value=None):
    obj = ET.SubElement(parent, '{%s}%s' % (NS, tag),
                        {k: str(v) for k, v in (attrs or {}).items()})
    obj.text = value
    return obj


def segment(g, x1, y1, x2, y2, color='#7488a0', width=2):
    element(g, 'line', dict(x1=x1,y1=y1,x2=x2,y2=y2,stroke=color,**{'stroke-width':width}))


def label(g, x, y, value, size=14, color='#23334d', weight='normal'):
    return element(g, 'text', {'x':x,'y':y,'fill':color,'font-size':size,'font-weight':weight}, value)


def render(rows):
    h = rows[0]
    svg = ET.Element('{%s}svg' % NS, {'viewBox':'0 0 1460 760','width':'1460','height':'760',
                                        'font-family':'DejaVu Sans, sans-serif','role':'img',
                                        'aria-labelledby':'title description'})
    element(svg,'title',{'id':'title'},'Локальный причинный доступ к своему прошлому')
    element(svg,'desc',{'id':'description'},'Шесть доменов, шесть адресов в каждом. Наведите указатель на адрес для полного текста и ссылки на свидетельство.')
    element(svg,'rect',{'width':'1460','height':'760','fill':'#f7f9fc'})
    label(svg,44,51,'Локальный причинный доступ к своему прошлому',32,weight='bold')
    label(svg,46,82,'Rule 110   /   Наведите указатель на адрес, чтобы прочитать утверждение и найти проверку.',16)
    root = element(svg,'g',{'id':'leaf','data-leaf':h['leaf'],'data-abi':h['abi'],'data-origin':h['leaf_origin']})
    spine=element(root,'g',{'id':'spine'})
    segment(spine,48,370,1150,370,'#1d4369',5)
    for n,(code,name) in enumerate(BONES.items()):
        g=element(root,'g',{'data-bone':name})
        end_x=[280,430,610,760,940,1090][n]
        start_x=end_x-160
        start_y=135 if n%2==0 else 605
        segment(g,start_x,start_y,end_x,370,'#50667e',3)
        label(g,start_x-84,start_y-12 if n%2==0 else start_y+27,name,19,weight='bold')
        for k in range(6):
            r=rows[n*6+k]
            attrs={'data-'+key.replace('_','-'):v for key,v in r.items()}
            slot=element(g,'g',attrs)
            element(slot,'title',value=r['law']+' · '+r['state']+'\n'+r['value']+'\n'+r['witness'])
            t=(k+1)/7
            x=round(start_x+(end_x-start_x)*t)
            y=round(start_y+(370-start_y)*t)
            c='#166652' if r['state']=='KNOWN' else '#a44924'
            segment(slot,x-110,y,x,y,c,1)
            element(slot,'rect',{'x':x-130,'y':y-17,'width':132,'height':24,'fill':'#ffffff','fill-opacity':0,'pointer-events':'all'})
            element(slot,'circle',{'cx':x-110,'cy':y,'r':4,'fill':c})
            label(slot,x-106,y-4,r['law']+'  '+SLOTS[k],13,c,'bold')
    head=element(root,'g',{'id':'head'})
    element(head,'rect',{'x':1150,'y':316,'rx':14,'width':282,'height':112,'fill':'#1d4369'})
    label(head,1168,351,'СВОЁ ПРОШЛОЕ',20,'#ffffff','bold')
    label(head,1168,381,h['leaf'],15,'#ffffff')
    label(head,1168,405,h['abi'],13,'#dce9f7')
    label(svg,46,700,'●  KNOWN  ·  адрес ведёт к проверке',17,'#166652','bold')
    label(svg,490,700,'●  UNKNOWN  ·  свидетельство отсутствует',17,'#a44924','bold')
    label(svg,46,734,'Порядок по оси слева направо. Полный текст всех 36 адресов содержится в leaf.tsv.',15)
    ET.indent(svg,space='  ')
    return ET.tostring(svg,encoding='utf-8',xml_declaration=True)+b'\n'


def readback(data):
    svg=ET.fromstring(data)
    root=svg.find(".//*[@id='leaf']")
    require(root is not None, 'missing leaf head metadata')
    rows=[]
    for bone in root.findall('{%s}g' % NS):
        for slot in bone.findall('{%s}g' % NS):
            if 'data-law' not in slot.attrib:
                continue
            row={key:slot.attrib['data-'+key.replace('_','-')] for key in FIELDS}
            require(BONES[row['law'][0]]==bone.attrib.get('data-bone'), 'wrong parent')
            require((row['leaf'],row['abi'],row['leaf_origin']) == (
                root.attrib['data-leaf'],root.attrib['data-abi'],root.attrib['data-origin']), 'head mismatch')
            require(slot.find('{%s}title' % NS).text.split('\n')[1] == row['value'], 'tool tip changed')
            rows.append(row)
    return rows


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Regenerate leaf.svg after validating its TSV sources')
    args=parser.parse_args()
    with TSV.open(encoding='utf8',newline='') as f:
        table=csv.DictReader(f,delimiter='\t')
        require(table.fieldnames==FIELDS,'TSV header mismatch')
        rows=list(table)
    audit_rows(rows)
    data=render(rows)
    if args.write:
        SVG.write_bytes(data)
    require(SVG.read_bytes()==data,'SVG is stale; re-render with --write')
    recovered=readback(SVG.read_bytes())
    require(recovered==rows,'SVG/TSV semantic mismatch')
    mirror=io.StringIO()
    writer=csv.DictWriter(mirror,fieldnames=FIELDS,delimiter='\t',lineterminator='\n')
    writer.writeheader()
    writer.writerows(recovered)
    require(mirror.getvalue().encode('utf8')==TSV.read_bytes(),'TSV canonical byte readback failed')
    print(f"{len(rows)} slots; {sum(r['state']=='KNOWN' for r in rows)} KNOWN, "
          f"{sum(r['state']=='UNKNOWN' for r in rows)} UNKNOWN; witness SHA-256, symbols and byte-exact readback OK")
