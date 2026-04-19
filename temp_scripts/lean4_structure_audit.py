import os, re

results = []
lean_dir = 'G:/_src/FormalMath/docs/09-形式化证明/Lean4'
for f in sorted(os.listdir(lean_dir)):
    if not f.endswith('.lean'):
        continue
    path = os.path.join(lean_dir, f)
    try:
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
    except:
        continue
    sorry_count = len(re.findall(r'\bsorry\b', content))
    theorem_count = len(re.findall(r'\btheorem\b', content))
    lemma_count = len(re.findall(r'\blemma\b', content))
    def_count = len(re.findall(r'\bdef\b', content))
    import_count = len(re.findall(r'^import\s+', content, re.MULTILINE))
    has_by = ' by ' in content or '\nby\n' in content
    has_begin = 'begin' in content  # Lean3 style
    has_proof = has_by or has_begin
    # Determine status
    if sorry_count == 0 and theorem_count > 0:
        status = 'COMPLETE'
    elif sorry_count > 0 and theorem_count > 0:
        status = 'PARTIAL'
    elif theorem_count == 0 and (def_count > 0 or len(content) > 1000):
        status = 'FRAMEWORK'
    else:
        status = 'EMPTY'
    results.append({
        'file': f,
        'size': len(content),
        'theorems': theorem_count,
        'lemmas': lemma_count,
        'defs': def_count,
        'imports': import_count,
        'sorrys': sorry_count,
        'has_proof': has_proof,
        'status': status
    })

print(f"{'File':<40} {'Size':>8} {'Th':>4} {'Lm':>4} {'Df':>4} {'Im':>4} {'Sorry':>6} {'Status':>10}")
print("="*90)
complete = partial = framework = empty = 0
for r in results:
    print(f"{r['file']:<40} {r['size']:>8} {r['theorems']:>4} {r['lemmas']:>4} {r['defs']:>4} {r['imports']:>4} {r['sorrys']:>6} {r['status']:>10}")
    if r['status'] == 'COMPLETE': complete += 1
    elif r['status'] == 'PARTIAL': partial += 1
    elif r['status'] == 'FRAMEWORK': framework += 1
    else: empty += 1

print(f"\nSummary: COMPLETE={complete}, PARTIAL={partial}, FRAMEWORK={framework}, EMPTY={empty}")
print(f"Total files: {len(results)}")

# Write CSV
import csv
with open('G:/_src/FormalMath/temp_scripts/lean4_structure_audit_20260420.csv', 'w', newline='', encoding='utf-8') as f:
    writer = csv.DictWriter(f, fieldnames=['file','size','theorems','lemmas','defs','imports','sorrys','has_proof','status'])
    writer.writeheader()
    writer.writerows(results)
