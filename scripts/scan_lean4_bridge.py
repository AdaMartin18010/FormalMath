import os
import re
from collections import defaultdict

LEAN_DIR = 'docs/09-形式化证明/Lean4/'
DOC_DIRS = ['docs/', 'concept/', '数学家理念体系/']
OUTPUT_PATH = 'output/00-形式化与自然语言断裂点地图.md'

def list_lean_files():
    files = []
    for root, dirs, filenames in os.walk(LEAN_DIR):
        for f in filenames:
            if f.endswith('.lean'):
                files.append(os.path.join(root, f))
    files.sort()
    return files

def extract_info(lean_path):
    basename = os.path.basename(lean_path)
    name_no_ext = os.path.splitext(basename)[0]
    size = os.path.getsize(lean_path)
    info = {
        'path': lean_path,
        'basename': basename,
        'name_no_ext': name_no_ext,
        'size': size,
        'search_terms': set(),
        'theorem_names': [],
        'chinese_name': None,
        'is_batch': False,
    }
    
    if re.match(r'^\d+-定理-\d+$', name_no_ext) or name_no_ext.startswith('定理-'):
        info['is_batch'] = True
    
    info['search_terms'].add(name_no_ext)
    
    m = re.match(r'^(\d+)-(.+)$', name_no_ext)
    if m and not info['is_batch']:
        info['search_terms'].add(m.group(2))
    
    if size == 0:
        return info
    
    with open(lean_path, 'r', encoding='utf-8') as f:
        content = f.read()
        lines = content.splitlines()
    
    header = content[:800]
    chinese = None
    m = re.search(r'#\s*([^/\n]+)', header)
    if m:
        chinese = m.group(1).strip()
        for suffix in ['的形式化证明', '的形式化框架', '与微分中值定理', '的形式化', '的形式化目标', '的形式化概述']:
            if suffix in chinese:
                chinese = chinese.split(suffix)[0]
    if not chinese:
        m2 = re.search(r'\*\*定理名称\*\*[:：]\s*([^\n]+)', header)
        if m2:
            chinese = m2.group(1).strip()
    if chinese:
        info['chinese_name'] = chinese
        info['search_terms'].add(chinese)
    
    for line in lines:
        tm = re.match(r'^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_]*)', line.strip())
        if tm:
            info['theorem_names'].append(tm.group(2))
    info['search_terms'].update(info['theorem_names'])
    
    m3 = re.search(r'\*\*核心定理\*\*[:：]\s*`?([A-Za-z_.][A-Za-z0-9_.]*)`?', header)
    if m3:
        info['search_terms'].add(m3.group(1))
    
    return info

def index_markdown_files():
    md_files = []
    md_contents = {}
    md_has_lean = {}
    for doc_dir in DOC_DIRS:
        if not os.path.exists(doc_dir):
            continue
        for root, dirs, filenames in os.walk(doc_dir):
            for f in filenames:
                if f.endswith('.md'):
                    path = os.path.join(root, f)
                    try:
                        with open(path, 'r', encoding='utf-8') as file:
                            content = file.read()
                        md_files.append(path)
                        md_contents[path] = content
                        md_has_lean[path] = '```lean' in content or '```lean4' in content
                    except Exception:
                        pass
    return md_files, md_contents, md_has_lean

def term_near_lean_block(content, term, window=600):
    markers = ['```lean', '```lean4']
    for marker in markers:
        idx = 0
        while True:
            block_start = content.find(marker, idx)
            if block_start == -1:
                break
            start = max(0, block_start - window)
            if term in content[start:block_start]:
                return True
            block_end = content.find('\n```', block_start + len(marker))
            if block_end == -1:
                block_end = content.find('```', block_start + len(marker))
            if block_end == -1:
                block_end = len(content)
            else:
                block_end += 4
            after_end = min(len(content), block_end + window)
            if term in content[block_end:after_end]:
                return True
            idx = block_end
    return False

def classify(info, md_files, md_contents, md_has_lean):
    refs = set()
    has_lean_near = False
    for term in info['search_terms']:
        if not term or len(term) < 2:
            continue
        for path in md_files:
            if term in md_contents[path]:
                refs.add(path)
                if md_has_lean[path] and term_near_lean_block(md_contents[path], term):
                    has_lean_near = True
    if not refs:
        return 'island', refs
    if has_lean_near:
        return 'full', refs
    return 'simple', refs

def main():
    lean_files = list_lean_files()
    md_files, md_contents, md_has_lean = index_markdown_files()
    print(f'Indexed {len(md_files)} markdown files')
    
    results = []
    for lf in lean_files:
        info = extract_info(lf)
        cat, refs = classify(info, md_files, md_contents, md_has_lean)
        results.append({
            'basename': info['basename'],
            'name_no_ext': info['name_no_ext'],
            'chinese_name': info['chinese_name'],
            'is_batch': info['is_batch'],
            'category': cat,
            'ref_count': len(refs),
            'size': info['size'],
        })
    
    total = len(results)
    full_count = sum(1 for r in results if r['category'] == 'full')
    simple_count = sum(1 for r in results if r['category'] == 'simple')
    island_count = sum(1 for r in results if r['category'] == 'island')
    batch_count = sum(1 for r in results if r['is_batch'])
    batch_island = sum(1 for r in results if r['is_batch'] and r['category'] == 'island')
    
    lines = []
    lines.append('# 形式化-自然语言断裂点地图')
    lines.append('')
    lines.append('> 生成日期：2026-04-17')
    lines.append('> 扫描范围：`docs/09-形式化证明/Lean4/` 下所有 `.lean` 文件')
    lines.append('> 对照文档范围：`docs/`、`concept/`、`数学家理念体系/` 下的所有 `.md` 文件')
    lines.append('')
    lines.append('## 一、统计数据')
    lines.append('')
    lines.append('| 分类 | 数量 | 占比 | 说明 |')
    lines.append('|------|------|------|------|')
    lines.append(f'| 有完整双语教学文档 | {full_count} | {full_count/total*100:.1f}% | 被 `.md` 文档引用，且引用文档中包含 Lean4 代码块 |')
    lines.append(f'| 有简单引用但无深度讲解 | {simple_count} | {simple_count/total*100:.1f}% | 被 `.md` 文档引用，但引用文档中无 Lean4 代码块 |')
    lines.append(f'| 完全未被引用（孤岛） | {island_count} | {island_count/total*100:.1f}% | 在 `.md` 文档中无任何引用 |')
    lines.append(f'| **合计** | **{total}** | **100%** | — |')
    lines.append('')
    lines.append('### 断裂率计算')
    lines.append('')
    lines.append('$$')
    lines.append(r'\text{断裂率} = \frac{\text{孤岛数量} + \text{仅简单引用数量}}{\text{定理总数}} \times 100\%')
    lines.append('$$')
    lines.append('')
    lines.append(f'$$\\text{{断裂率}} = \\frac{{{island_count} + {simple_count}}}{{{total}}} \\times 100\\% = {(island_count + simple_count)/total*100:.1f}\\%$$')
    lines.append('')
    lines.append('### 批量命名文件特别关注')
    lines.append('')
    lines.append(f'- 批量命名文件（`定理-XX.lean`）总数：**{batch_count}**')
    lines.append(f'- 其中为「孤岛」的数量：**{batch_island}**')
    lines.append(f'- 占比：**{batch_island/batch_count*100 if batch_count else 0:.1f}%**')
    lines.append('')
    lines.append('## 二、「孤岛」定理清单')
    lines.append('')
    lines.append('以下定理在 `docs/`、`concept/`、`数学家理念体系/` 的自然语言文档中**完全未被引用**：')
    lines.append('')
    lines.append('| 序号 | 文件名 | 中文名/说明 | 文件大小(字节) |')
    lines.append('|------|--------|-------------|----------------|')
    idx = 1
    for r in results:
        if r['category'] == 'island':
            name = r['chinese_name'] or '-'
            lines.append(f'| {idx} | `{r["basename"]}` | {name} | {r["size"]} |')
            idx += 1
    lines.append('')
    lines.append('## 三、已有良好桥接的定理清单（最佳实践示例）')
    lines.append('')
    lines.append('以下定理在自然语言文档中被引用，且引用文档包含 Lean4 代码块，形成了「自然语言证明 + Lean4 代码对照」的完整双语教学文档：')
    lines.append('')
    lines.append('| 序号 | 文件名 | 中文名 | 引用文档数 |')
    lines.append('|------|--------|--------|------------|')
    idx = 1
    for r in results:
        if r['category'] == 'full':
            name = r['chinese_name'] or r['name_no_ext']
            lines.append(f'| {idx} | `{r["basename"]}` | {name} | {r["ref_count"]} |')
            idx += 1
    lines.append('')
    lines.append('## 四、仅有简单引用的定理清单')
    lines.append('')
    lines.append('以下定理在自然语言文档中被引用，但引用文档中**不含 Lean4 代码块**，属于概念提及或索引式引用：')
    lines.append('')
    lines.append('| 序号 | 文件名 | 中文名 | 引用文档数 |')
    lines.append('|------|--------|--------|------------|')
    idx = 1
    for r in results:
        if r['category'] == 'simple':
            name = r['chinese_name'] or r['name_no_ext']
            lines.append(f'| {idx} | `{r["basename"]}` | {name} | {r["ref_count"]} |')
            idx += 1
    lines.append('')
    lines.append('## 五、建议与后续行动')
    lines.append('')
    lines.append('1. **优先填补「孤岛」**：建议对「孤岛」定理（尤其是有实际内容的非空文件）优先撰写对应的双语教学 Markdown 文档，或在现有定理证明文档中嵌入对应的 Lean4 代码引用。')
    lines.append('2. **批量命名文件整改**：所有 `定理-XX.lean` 文件目前均为空文件（0 字节）且无任何文档引用。建议：')
    lines.append('   - 立即为这些占位文件赋予明确的数学名称（如 `SylowSecondTheorem.lean`）。')
    lines.append('   - 删除长期无内容的空文件，或补充形式化代码与双语注释。')
    lines.append('   - 在 `docs/09-形式化证明/` 目录下建立对应的 `-完整证明.md` 文档，形成命名与内容的一致性。')
    lines.append('3. **提升「简单引用」为「完整双语」**：对仅有简单引用的定理，建议在已有的自然语言证明文档（如 `docs/XX/定理证明/XXX-完整证明.md`）中补充 ````lean4` 代码块，实现真正的「纸笔证明 ↔ 形式化证明」对照。')
    lines.append('4. **建立自动化监控**：建议将此扫描脚本纳入 CI，定期生成断裂点地图，防止新的「孤岛」定理持续积累。')
    lines.append('')
    
    os.makedirs(os.path.dirname(OUTPUT_PATH), exist_ok=True)
    with open(OUTPUT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f'Report written to {OUTPUT_PATH}')

if __name__ == '__main__':
    main()
