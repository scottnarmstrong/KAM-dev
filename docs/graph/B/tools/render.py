import json,sys
nodes=json.load(open('nodes.json'))
rev=json.load(open(sys.argv[2])) if len(sys.argv)>2 and sys.argv[2]!='-' else {}
sync=json.load(open(sys.argv[3])) if len(sys.argv)>3 else {}
hdr=json.load(open('header.json'))
out=['# Proof dependency database — track B (program B: effective stability, B1-T / B1-E)','']
for k in ['GRAPH_VERSION','ROOTS','CORPUS','CONVENTIONS','STANDING_ASSUMPTIONS','EXTERNAL_POLICY','FROZEN_ANCHORS','FROZEN_MANIFEST','WRITER','GLOBAL_REVIEWER','GLOBAL_REVIEW_REF']:
    out.append(f'{k}: {hdr[k]}')
out+=['','The dependency direction is `NODE -> prerequisite`. `DEPS` is conjunctive. Node blocks are generated from the',
 'writer\'s node table; correct structure after publication only by append-only `AMEND` records.','','## Nodes','']
for n in nodes:
    f=n['frozen'] or ('-','-','-','-')
    st,ref,note=('NOT_STARTED','-','-') if n['kind']!='external' else ('EXTERNAL','-','-')
    if n['id'] in sync: st,ref,note=sync[n['id']]
    r=rev.get(n['id'],{})
    out+=[f"NODE: {n['id']}",f"KIND: {n['kind']}",f"TITLE: {n['title']}",f"STATEMENT_SOURCE: {n['ss']}",f"PROOF_SOURCE: {n['ps']}",
      f"CONTRACT_ID: {n['cid']}","CONTRACT_VERSION: 1",f"SOURCE_HYPOTHESES: {n['hyp']}",f"SOURCE_QUANTIFIERS: {n['quant']}",
      f"SOURCE_CONCLUSION: {n['concl']}",f"CONSTANT_SCOPE: {n['cscope']}",f"FROZEN_FILE: {f[0]}",f"FROZEN_DECL: {f[1]}",
      f"FROZEN_ANCHOR_ID: {f[2]}",f"FROZEN_ABI_SHA256: {f[3]}",f"DEPS: {', '.join(n['deps']) or '-'}","ROUTES: -","ROUTE_FOR: -"]
    out+=[f"EDGE: {a} | {b} | {c.replace('|','abs ')}" for a,b,c in n['edges']]
    out+=[f"TOPOLOGY_STATUS: {r.get('status','PROPOSED')}","EXTRACTOR: kam-b1",f"REVIEWER: {r.get('reviewer','-')}",
      f"LEAN_STATUS: {st}",f"LEAN_REF: {ref}",f"LEAN_NOTE: {note}",f"NOTE: {n['note']}",'']
out+=['## Append-only structural amendments','','(none)','','<!-- BEGIN PROOF DEPGRAPH GENERATED -->','<!-- END PROOF DEPGRAPH GENERATED -->','']
open(sys.argv[1],'w').write('\n'.join(out))
