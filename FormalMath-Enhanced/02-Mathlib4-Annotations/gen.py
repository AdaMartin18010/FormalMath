import json, os

def write_md(path, title, lean, background, intuition, formal, proof, examples, apps, concepts, refs):
    lines = [
        "---",
        "msc_primary: 00A99",
        "processed_at: '2026-04-15'",
        f"title: {title}",
        "---",
        f"# {title}",
        "",
        "## Mathlib4 引用",
        "",
        "```lean",
        lean,
        "```",
        "",
        "## 数学背景",
        "",
        background,
        "",
        "## 直观解释",
        "",
        intuition,
        "",
        "## 形式化表述",
        "",
        formal,
        "",
        "## 证明思路",
        "",
        proof,
        "",
        "## 示例",
        "",
        examples,
        "",
        "## 应用",
        "",
        apps,
        "",
        "## 相关概念",
        "",
        concepts,
        "",
        "## 参考",
        "",
        refs,
        "",
        "---",
        "",
        "*最后更新：2026-04-15 | 版本：v1.0.0*",
    ]
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f'Created {path}')

with open('data.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

for item in data:
    write_md(*item)
