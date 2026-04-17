#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
数学家理念体系空壳文档审计与归档清理脚本
处理除格洛腾迪克外的61位数学家目录
"""

import os
import re
import shutil
from pathlib import Path
from collections import defaultdict
from datetime import datetime

BASE_DIR = Path("e:/_src/FormalMath/数学家理念体系")
OUTPUT_DIR = Path("e:/_src/FormalMath/output")
ARCHIVE_BASE = BASE_DIR / "00-归档-2026年4月"

# 排除的目录
EXCLUDE_DIRS = {"格洛腾迪克数学理念", "00-归档", "00-归档-2026年4月"}

# 保护文件（根目录导航文件）
PROTECTED_FILES = {"README.md", "START-HERE.md", "00-文档索引.md", "00-项目状态.md"}


def get_chinese_char_count(text):
    """统计纯中文字符数"""
    return len(re.findall(r'[\u4e00-\u9fff]', text))


def count_latex_formulas(text):
    """统计LaTeX公式数量（行内+行间）"""
    inline = len(re.findall(r'(?<!\$)\$[^$\n]+?\$(?!\$)', text))
    display = len(re.findall(r'\$\$[\s\S]*?\$\$', text))
    return inline + display


def has_rich_references(text):
    """检查是否有丰富的参考文献"""
    if 'references:' not in text:
        return False
    try:
        ref_section = text.split('references:')[1].split('---')[0]
        return len(ref_section.strip()) > 150
    except IndexError:
        return False


def count_math_keywords(text):
    """统计数学关键词密度指标"""
    keywords = [
        '定理', '定义', '证明', '命题', '引理', '推论', '公理', 
        'formula', 'theorem', 'definition', 'proof', 'lemma', 'proposition',
        '推导', '计算', '方程', '函数', '映射', '空间', '群', '环', '域'
    ]
    count = sum(text.count(k) for k in keywords)
    return count


def classify_document(filepath, content):
    """
    文档分类
    返回: (category, reason)
    category: 'A', 'B', 'C'
    """
    basename = os.path.basename(filepath)
    size = len(content.encode('utf-8'))
    chinese_chars = get_chinese_char_count(content)
    latex_count = count_latex_formulas(content)
    math_keywords = count_math_keywords(content)
    
    # === A类：直接归档 ===
    if size < 500:
        return 'A', f'文件小于500字节（{size}字节）'
    
    if chinese_chars < 200:
        return 'A', f'正文中文字数小于200字（{chinese_chars}字）'
    
    # 纯占位符检测：frontmatter之后几乎没有内容
    body = re.sub(r'^---\n[\s\S]*?\n---\n', '', content)
    body_lines = [l for l in body.split('\n') if l.strip()]
    if len(body_lines) < 5:
        return 'A', f'正文有效行数少于5行（{len(body_lines)}行）'
    
    # === 保护特定高价值文件 ===
    if basename in PROTECTED_FILES:
        return 'C', '根目录导航文件，保留'
    
    # 金层文档直接保留
    if 'level: "gold"' in content or 'level: gold' in content:
        return 'C', '金层文档（level: gold），保留'
    
    # 原始文献深度解读保留
    if has_rich_references(content) and latex_count > 8:
        return 'C', '有丰富参考文献和较多数学公式，保留'
    
    # === B类：模板化注水检测 ===
    reasons = []
    
    # 1. 固定模板结尾标记（强信号）
    has_doc_status = '文档状态: ✅ 完成' in content or ('文档状态' in content and '完成' in content)
    has_word_count = '字数: 约2,000字' in content or '约2,000字' in content
    has_update = re.search(r'最后更新\s*[:：]\s*2025年12月', content) is not None
    
    template_markers = sum([has_doc_status, has_word_count, has_update])
    if template_markers >= 2:
        reasons.append(f'含{template_markers}个固定模板标记')
    
    # 2. 固定模板章节结构
    has_relation = re.search(r'与[^#\n]{2,8}的关系', content) is not None
    has_historical = '历史地位' in content or '历史联系' in content
    has_influence = '影响' in content
    has_modern = '现代发展' in content
    has_summary = re.search(r'的历史地位', content) is not None
    
    section_markers = sum([has_relation, has_historical, has_influence, has_modern, has_summary])
    if section_markers >= 4:
        reasons.append(f'含{section_markers}个典型模板章节')
    elif section_markers >= 3 and template_markers >= 1:
        reasons.append(f'含{section_markers}个模板章节+{template_markers}个模板标记')
    
    # 3. 数学内容稀少检测
    # 对于大于3000字节的文件，如果数学关键词极少
    if size > 3000 and math_keywords < 8 and latex_count < 3:
        reasons.append(f'数学内容极度稀薄（关键词{math_keywords}个，公式{latex_count}个）')
    
    # 判定B类：有足够强的模板化信号
    is_template = False
    if template_markers >= 2 and section_markers >= 3:
        is_template = True
    elif template_markers >= 3:
        is_template = True
    elif section_markers >= 4 and math_keywords < 15 and latex_count < 5:
        is_template = True
    elif len(reasons) >= 2:
        is_template = True
    
    if is_template:
        # 例外：虽然模板化但规模大、内容充实
        if size > 12000 and (math_keywords > 20 or latex_count > 10 or chinese_chars > 2500):
            return 'C', '文档规模大且数学/分析内容充实，虽有模板结构仍保留'
        
        return 'B', '严重模板化注水：' + '、'.join(reasons)
    
    # === C类：默认保留 ===
    return 'C', '非模板化或有实质内容，保留'


def get_all_mathematicians():
    """获取所有需要处理的数学家目录"""
    dirs = []
    for d in sorted(BASE_DIR.iterdir()):
        if d.is_dir() and d.name not in EXCLUDE_DIRS:
            dirs.append(d)
    return dirs


def process_mathematician(math_dir, dry_run=True):
    """处理单个数学家目录"""
    results = {
        'name': math_dir.name,
        'total': 0,
        'A': [],
        'B': [],
        'C': [],
        'moved': 0
    }
    
    md_files = list(math_dir.rglob("*.md"))
    
    for f in md_files:
        try:
            content = f.read_text(encoding='utf-8')
        except Exception as e:
            print(f"  读取失败: {f} - {e}")
            continue
        
        cat, reason = classify_document(str(f), content)
        results[cat].append({
            'path': str(f),
            'rel_path': str(f.relative_to(math_dir)),
            'size': len(content.encode('utf-8')),
            'chinese': get_chinese_char_count(content),
            'latex': count_latex_formulas(content),
            'reason': reason
        })
        results['total'] += 1
    
    # 移动A类和B类文件
    if not dry_run:
        archive_dir = ARCHIVE_BASE / math_dir.name
        archive_dir.mkdir(parents=True, exist_ok=True)
        
        for cat in ['A', 'B']:
            for item in results[cat]:
                src = Path(item['path'])
                # 保持相对目录结构
                rel_path = src.relative_to(math_dir)
                dst = archive_dir / rel_path
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(dst))
                results['moved'] += 1
    
    return results


def generate_report(all_results, dry_run=True):
    """生成清理报告"""
    total_docs = sum(r['total'] for r in all_results)
    total_a = sum(len(r['A']) for r in all_results)
    total_b = sum(len(r['B']) for r in all_results)
    total_c = sum(len(r['C']) for r in all_results)
    total_moved = sum(r['moved'] for r in all_results)
    
    lines = []
    lines.append("# 数学家理念体系空壳清理报告")
    lines.append("")
    lines.append(f"> **生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}")
    lines.append(f"> **清理范围**: 61位数学家（排除已完成清理的格洛腾迪克）")
    lines.append(f"> **操作模式**: {'模拟审计（未实际移动）' if dry_run else '实际归档清理'}")
    lines.append("")
    
    lines.append("## 一、总体统计")
    lines.append("")
    lines.append(f"| 指标 | 数量 | 占比 |")
    lines.append(f"|------|------|------|")
    lines.append(f"| 总文档数 | {total_docs} | 100% |")
    lines.append(f"| A类（直接归档） | {total_a} | {total_a/total_docs*100:.1f}% |")
    lines.append(f"| B类（模板化归档） | {total_b} | {total_b/total_docs*100:.1f}% |")
    lines.append(f"| C类（保留） | {total_c} | {total_c/total_docs*100:.1f}% |")
    lines.append(f"| **归档总数** | **{total_a + total_b}** | **{(total_a + total_b)/total_docs*100:.1f}%** |")
    if not dry_run:
        lines.append(f"| 实际移动文件数 | {total_moved} | - |")
    lines.append("")
    
    lines.append("## 二、61位数学家文档统计总表")
    lines.append("")
    lines.append("| 排名 | 数学家 | 总文档 | A类 | B类 | C类 | 归档数 | 保留率 |")
    lines.append("|------|--------|--------|-----|-----|-----|--------|--------|")
    
    sorted_results = sorted(all_results, key=lambda x: x['total'], reverse=True)
    for i, r in enumerate(sorted_results, 1):
        archive_count = len(r['A']) + len(r['B'])
        keep_rate = len(r['C']) / r['total'] * 100 if r['total'] > 0 else 0
        lines.append(f"| {i} | {r['name']} | {r['total']} | {len(r['A'])} | {len(r['B'])} | {len(r['C'])} | {archive_count} | {keep_rate:.1f}% |")
    
    lines.append("")
    lines.append("## 三、重点数学家详细分析")
    lines.append("")
    
    # 重点分析文档数量前10的数学家
    for r in sorted_results[:10]:
        lines.append(f"### {r['name']}")
        lines.append("")
        lines.append(f"- **总文档**: {r['total']} 篇")
        lines.append(f"- **A类（直接归档）**: {len(r['A'])} 篇")
        lines.append(f"- **B类（模板化归档）**: {len(r['B'])} 篇")
        lines.append(f"- **C类（保留）**: {len(r['C'])} 篇")
        lines.append(f"- **归档率**: {(len(r['A'])+len(r['B']))/r['total']*100:.1f}%")
        lines.append("")
        
        if r['A']:
            lines.append("**A类典型案例**:")
            for item in r['A'][:3]:
                lines.append(f"- `{item['rel_path']}` ({item['size']}字节) — {item['reason']}")
            lines.append("")
        
        if r['B']:
            lines.append("**B类典型案例**:")
            for item in r['B'][:5]:
                lines.append(f"- `{item['rel_path']}` ({item['size']}字节, {item['chinese']}中文字, {item['latex']}公式) — {item['reason']}")
            lines.append("")
        
        if r['C']:
            lines.append("**C类保留案例**:")
            # 按大小排序，展示较大的保留文档
            c_sorted = sorted(r['C'], key=lambda x: x['size'], reverse=True)
            for item in c_sorted[:5]:
                lines.append(f"- `{item['rel_path']}` ({item['size']}字节, {item['chinese']}中文字, {item['latex']}公式) — {item['reason']}")
            lines.append("")
    
    lines.append("## 四、最水文档示例")
    lines.append("")
    # 找出所有A类中最小的几个
    all_a = []
    for r in all_results:
        all_a.extend(r['A'])
    all_a_sorted = sorted(all_a, key=lambda x: x['size'])
    lines.append("以下是最典型的空壳/占位符文档（按文件大小排序）:")
    lines.append("")
    for item in all_a_sorted[:10]:
        rel = item['path'].replace(str(BASE_DIR), "数学家理念体系")
        lines.append(f"### {rel}")
        lines.append(f"- **大小**: {item['size']} 字节")
        lines.append(f"- **中文字**: {item['chinese']} 字")
        lines.append(f"- **归档原因**: {item['reason']}")
        lines.append("")
    
    lines.append("## 五、保留的优秀示例")
    lines.append("")
    all_c = []
    for r in all_results:
        all_c.extend(r['C'])
    # 优先展示金层文档和有大文献引用的
    gold_docs = [x for x in all_c if '金层' in x['reason'] or 'gold' in x['reason'].lower()]
    ref_docs = [x for x in all_c if '参考文献' in x['reason']]
    other_c = [x for x in all_c if x not in gold_docs and x not in ref_docs]
    
    showcase = (gold_docs + ref_docs + sorted(other_c, key=lambda x: x['size'], reverse=True))[:15]
    for item in showcase:
        rel = item['path'].replace(str(BASE_DIR), "数学家理念体系")
        lines.append(f"- **`{rel}`** ({item['size']}字节, {item['chinese']}中文字, {item['latex']}公式) — {item['reason']}")
    lines.append("")
    
    lines.append("## 六、归档目录结构")
    lines.append("")
    lines.append("归档文件已移动至:")
    lines.append("```")
    lines.append("数学家理念体系/00-归档-2026年4月/")
    lines.append("├── [数学家姓名1]/")
    lines.append("│   └── [保持原相对目录结构]")
    lines.append("├── [数学家姓名2]/")
    lines.append("│   └── ...")
    lines.append("└── ...")
    lines.append("```")
    lines.append("")
    
    lines.append("## 七、分类规则说明")
    lines.append("")
    lines.append("### A类（直接归档）")
    lines.append("- 文件大小 < 500字节")
    lines.append("- 正文纯中文字数 < 200字")
    lines.append("- 正文有效行数 < 5行（纯占位符）")
    lines.append("")
    lines.append("### B类（评估后归档）")
    lines.append("满足以下任一组合:")
    lines.append("1. 含2个以上固定模板标记（'文档状态: ✅ 完成'、'字数: 约2,000字'、'最后更新: 2025年12月'）")
    lines.append("2. 含4个以上典型模板章节（'与XX的关系'、'历史地位'、'历史联系'、'影响'、'现代发展'）")
    lines.append("3. 文件>3000字节但数学关键词<8个且LaTeX公式<3个")
    lines.append("例外：文件>12000字节且数学关键词>20个或LaTeX公式>10个或中文字>2500字，保留为C类")
    lines.append("")
    lines.append("### C类（保留）")
    lines.append("- 根目录导航文件（README.md等）")
    lines.append("- 金层文档（level: gold）")
    lines.append("- 有丰富参考文献和较多数学公式")
    lines.append("- 非模板化的深入研究或传记分析")
    lines.append("")
    
    lines.append("## 八、后续建议")
    lines.append("")
    lines.append("1. **金层重构推广**: 参考格洛腾迪克'金层重构'模式，对重点数学家（庞加莱、黎曼、希尔伯特等）的核心理论进行高质量重写。")
    lines.append("2. **模板批量清理**: 本次清理后，B类模板化文档已全部归档。建议制定新文档标准，禁止'约2,000字'等虚假字数标注和固定章节注水。")
    lines.append("3. **索引更新**: 各数学家根目录的 `00-文档索引.md` 和 `README.md` 需要更新，以反映归档后的文档结构变化。")
    lines.append("4. **跨数学家整合**: 保留的C类文档中，历史与传记类文档仍有价值，但建议进一步按主题整合，避免重复。")
    lines.append("5. **质量门控**: 建议在新文档创建时引入自动质量检查，对中文字数<500、数学公式<3、模板章节>4的文档进行拦截。")
    lines.append("")
    
    report_path = OUTPUT_DIR / "00-数学家理念体系空壳清理报告.md"
    report_path.write_text('\n'.join(lines), encoding='utf-8')
    return report_path


def main(dry_run=True):
    print(f"=== 数学家理念体系空壳文档审计 {'[模拟运行]' if dry_run else '[实际执行]'} ===")
    print(f"时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    mathematicians = get_all_mathematicians()
    print(f"发现 {len(mathematicians)} 位数学家目录待处理")
    print()
    
    all_results = []
    for i, math_dir in enumerate(mathematicians, 1):
        print(f"[{i}/{len(mathematicians)}] 处理: {math_dir.name} ...")
        result = process_mathematician(math_dir, dry_run=dry_run)
        all_results.append(result)
        a_count = len(result['A'])
        b_count = len(result['B'])
        c_count = len(result['C'])
        print(f"    总计: {result['total']} | A: {a_count} | B: {b_count} | C: {c_count} | 归档率: {(a_count+b_count)/result['total']*100:.1f}%")
    
    print()
    print("=== 生成报告 ===")
    report_path = generate_report(all_results, dry_run=dry_run)
    print(f"报告已保存: {report_path}")
    
    # 打印总体统计
    total_docs = sum(r['total'] for r in all_results)
    total_archive = sum(len(r['A']) + len(r['B']) for r in all_results)
    print()
    print(f"总体统计: 总文档 {total_docs} | 归档 {total_archive} ({total_archive/total_docs*100:.1f}%) | 保留 {total_docs - total_archive} ({(total_docs-total_archive)/total_docs*100:.1f}%)")
    
    return all_results


if __name__ == "__main__":
    import sys
    # 默认先运行模拟审计
    dry_run = True
    if len(sys.argv) > 1 and sys.argv[1] == '--execute':
        dry_run = False
    
    main(dry_run=dry_run)
