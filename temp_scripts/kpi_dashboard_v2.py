import os, re
from collections import defaultdict, Counter

silver_paths = [
    'G:/_src/FormalMath/docs/00-银层核心课程',
    'G:/_src/FormalMath/docs/03-分析学/01-实分析/定理证明',
]

kpi = {
    'total_silver_docs': 0,
    'total_theorems': 0,
    'total_exercises': 0,
    'total_lean4_refs': 0,
    'courses': defaultdict(lambda: {'docs':0, 'theorems':0, 'exercises':0, 'lean4_refs':0, 'refs_density':0}),
    'review_status': Counter(),
    'msc_coverage': {'with_primary':0, 'with_secondary':0, 'total':0},
}

# Broader theorem patterns (Chinese and English)
theorem_patterns = [
    re.compile(r'##?\s*(?:核心)?定理\s*[\d]*\s*[（(]?', re.IGNORECASE),
    re.compile(r'##?\s*Theorem\s*[\d]*\s*[\(（]?', re.IGNORECASE),
    re.compile(r'\*\*定理\s*[（(]?', re.IGNORECASE),
]
exercise_pattern = re.compile(r'###?\s*习题\s*\d+', re.IGNORECASE)
lean4_pattern = re.compile(r'```lean4', re.IGNORECASE)
proof_pattern = re.compile(r'(?:详细证明|证明[:：]|Proof[:：])', re.IGNORECASE)

for base_path in silver_paths:
    if not os.path.exists(base_path):
        continue
    for root, dirs, files in os.walk(base_path):
        for f in files:
            if not f.endswith('.md'):
                continue
            path = os.path.join(root, f)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                    content = fh.read()
            except:
                continue
            
            fm_match = re.match(r'---\s*\n(.*?)\n---', content, re.DOTALL)
            if not fm_match:
                continue
            block = fm_match.group(1)
            
            level = None
            lm = re.search(r'level:\s*["\']?(copper|silver|gold)["\']?', block, re.IGNORECASE)
            if lm:
                level = lm.group(1).lower()
            
            if level != 'silver':
                continue
            
            kpi['total_silver_docs'] += 1
            kpi['msc_coverage']['total'] += 1
            
            if 'msc_primary:' in block:
                kpi['msc_coverage']['with_primary'] += 1
            if 'msc_secondary:' in block:
                kpi['msc_coverage']['with_secondary'] += 1
            
            rs = re.search(r'review_status:\s*["\']?([^"\'\s\r\n]+)["\']?', block)
            if rs:
                kpi['review_status'][rs.group(1)] += 1
            
            course = 'general'
            cm = re.search(r'course:\s*["\']?([^"\'\r\n]+)["\']?', block)
            if cm:
                course = cm.group(1).strip()
            
            theorems = 0
            for tp in theorem_patterns:
                theorems = max(theorems, len(tp.findall(content)))
            
            # Count proof sections
            proofs = len(proof_pattern.findall(content))
            
            exercises = len(exercise_pattern.findall(content))
            lean4 = len(lean4_pattern.findall(content))
            
            kpi['total_theorems'] += theorems
            kpi['total_exercises'] += exercises
            kpi['total_lean4_refs'] += lean4
            
            kpi['courses'][course]['docs'] += 1
            kpi['courses'][course]['theorems'] += theorems
            kpi['courses'][course]['exercises'] += exercises
            kpi['courses'][course]['lean4_refs'] += lean4
            
            ref_count = len(re.findall(r'- (title|author|url|doi):', content))
            kpi['courses'][course]['refs_density'] += ref_count

print("=" * 65)
print("FormalMath 银层 KPI 月度统计报告 v2")
print("=" * 65)
print(f"\n📊 总体指标")
print(f"  银层文档总数: {kpi['total_silver_docs']}")
print(f"  定理总数: {kpi['total_theorems']}")
print(f"  习题总数: {kpi['total_exercises']}")
print(f"  Lean4引用数: {kpi['total_lean4_refs']}")
print(f"  每文档平均定理数: {kpi['total_theorems']/max(kpi['total_silver_docs'],1):.1f}")
print(f"  每文档平均习题数: {kpi['total_exercises']/max(kpi['total_silver_docs'],1):.1f}")

print(f"\n📋 MSC编码覆盖")
mp = kpi['msc_coverage']['with_primary']
ms = kpi['msc_coverage']['with_secondary']
mt = kpi['msc_coverage']['total']
print(f"  含主编码: {mp}/{mt} ({mp/max(mt,1)*100:.1f}%)")
print(f"  含次编码: {ms}/{mt} ({ms/max(mt,1)*100:.1f}%)")

print(f"\n🔍 审稿状态分布")
for status, count in kpi['review_status'].most_common():
    pct = count / max(kpi['total_silver_docs'], 1) * 100
    print(f"  {status}: {count} ({pct:.1f}%)")

print(f"\n📚 按课程统计")
for course, data in sorted(kpi['courses'].items(), key=lambda x: -x[1]['docs']):
    docs = data['docs']
    th = data['theorems']
    ex = data['exercises']
    l4 = data['lean4_refs']
    rd = data['refs_density'] / max(docs, 1)
    print(f"\n  {course}")
    print(f"    文档: {docs}, 定理: {th}, 习题: {ex}, Lean4: {l4}")
    print(f"    每文档平均引用: {rd:.1f}")
    ex_target = docs * 10
    print(f"    习题-解答对: {ex}/{ex_target} ({ex/max(ex_target,1)*100:.0f}%)")

print("\n" + "=" * 65)
