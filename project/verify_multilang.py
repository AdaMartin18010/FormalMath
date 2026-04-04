#!/usr/bin/env python3
import json
import yaml

# Load data
with open('multilang_terminology_table.json', encoding='utf-8') as f:
    json_data = json.load(f)

with open('concept_prerequisites_multilang_extended.yaml', encoding='utf-8') as f:
    yaml_data = yaml.safe_load(f)

print("=" * 60)
print("多语言扩展验证报告")
print("=" * 60)

# Statistics
print("\n【JSON术语对照表统计】")
print(f"  总概念数: {len(json_data['terminology'])}")
print(f"  支持语言: {', '.join(json_data['metadata']['languages'])}")

print("\n【YAML扩展图谱统计】")
print(f"  总概念数: {yaml_data['metadata']['statistics']['total_concepts']}")
print(f"  多语言概念数: {yaml_data['metadata']['statistics']['concepts_with_multilang']}")
print(f"  支持语言: {', '.join(yaml_data['metadata']['statistics']['languages_supported'])}")

# Sample concepts verification
print("\n【核心概念多语言验证】")
key_concepts = ['limit', 'derivative', 'vector_space', 'group', 'manifold', 'probability']

for cid in key_concepts:
    if cid in json_data['terminology']:
        t = json_data['terminology'][cid]
        trans = t['translations']
        print(f"\n  {cid} ({t['name_zh']}):")
        print(f"    分类: {t['category']}")
        print(f"    RU: {trans.get('ru', {}).get('title', 'N/A')}")
        print(f"    IT: {trans.get('it', {}).get('title', 'N/A')}")
        print(f"    ES: {trans.get('es', {}).get('title', 'N/A')}")
        print(f"    PT: {trans.get('pt', {}).get('title', 'N/A')}")

# Language coverage analysis
print("\n【各语言覆盖率】")
lang_coverage = {'ru': 0, 'it': 0, 'es': 0, 'pt': 0}
for concept in json_data['terminology'].values():
    for lang in lang_coverage:
        if lang in concept['translations']:
            lang_coverage[lang] += 1

for lang, count in lang_coverage.items():
    pct = count / len(json_data['terminology']) * 100
    print(f"  {lang}: {count}/{len(json_data['terminology'])} ({pct:.1f}%)")

# Category analysis
print("\n【按学科分类统计】")
categories = {}
for concept in json_data['terminology'].values():
    cat = concept['category']
    categories[cat] = categories.get(cat, 0) + 1

for cat, count in sorted(categories.items(), key=lambda x: -x[1]):
    print(f"  {cat}: {count}个概念")

print("\n" + "=" * 60)
print("验证完成 - 所有文件生成成功")
print("=" * 60)
