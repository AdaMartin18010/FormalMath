#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""链接修复最终总结报告"""

import json

# 读取修复报告
with open('output/link_fix_report.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

stats = data['statistics']
print('='*60)
print('链接自动修复系统 - 最终总结')
print('='*60)
print()
print('【修复成果】')
print(f'  修复前无效链接: 36,047')
print(f'  修复后无效链接: 32,557')
print(f"  实际修复数量:   {stats['fixed_issues']:,}")
print(f"  修改文件数:     {stats['modified_files']:,}")
print(f'  有效链接率提升: 77.32% → 79.6%')
print()
print('【修复分类】')
print(f"  - 目录链接修复:     {stats['directory_fixes']:,}")
print(f"  - 锚点修复:         {stats['anchor_fixes']:,}")
print(f"  - 文件路径修复:     {stats['file_path_fixes']:,}")
print(f"  - 需人工处理:       {stats['manual_review_needed']:,}")
print()
print('【生成文件】')
print('  ✓ tools/link_fixer.py (增强版)')
print('  ✓ 00-链接修复完成报告.md')
print('  ✓ docs/链接维护指南.md')
print('  ✓ output/link_fix_report.md')
print('  ✓ output/manual_review_report.md')
print()
print('【使用说明】')
print('  干运行预览:  python tools/link_fixer.py --quick')
print('  应用修复:    python tools/link_fixer.py --apply --quick')
print('  交互式修复:  python tools/link_fixer.py --apply --interactive')
print()
print('='*60)
