import os, re
from pathlib import Path

base = Path(r'e:\_src\FormalMath\数学家理念体系\庞加莱数学理念')

math_keywords_list = ['定理', '定义', '证明', '命题', '引理', '推论', '公理', 
    'formula', 'theorem', 'definition', 'proof', 'lemma', 'proposition',
    '推导', '计算', '方程', '函数', '映射', '空间', '群', '环', '域']

def analyze(f):
    text = open(f, 'r', encoding='utf-8').read()
    size = len(text.encode('utf-8'))
    chinese = len(re.findall(r'[\u4e00-\u9fff]', text))
    latex = len(re.findall(r'(?<!\$)\$[^$\n]+?\$(?!\$)', text)) + len(re.findall(r'\$\$[\s\S]*?\$\$', text))
    math_kw = sum(text.count(k) for k in math_keywords_list)
    has_historical = '历史地位' in text
    has_modern = '现代发展' in text
    has_doc_info = '文档信息' in text and '完成度' in text
    has_template_ending = '文档状态: ✅ 完成' in text and '字数: 约2,000字' in text
    rel = str(f.relative_to(base))
    in_math = '02-数学内容深度分析' in rel
    return {
        'rel': rel, 'size': size, 'chinese': chinese, 'latex': latex, 
        'math_kw': math_kw, 'hist': has_historical, 'modern': has_modern,
        'doc_info': has_doc_info, 'template_end': has_template_ending, 'in_math': in_math
    }

files = list(base.rglob('*.md'))
data = [analyze(f) for f in files]

# 按目录分组统计
print('=== 02-数学内容深度分析 下的文档 ===')
math_docs = [d for d in data if d['in_math']]
print(f'数量: {len(math_docs)}')
print(f'平均大小: {sum(d["size"] for d in math_docs)/len(math_docs):.0f}')
print(f'平均中文字: {sum(d["chinese"] for d in math_docs)/len(math_docs):.0f}')
print(f'平均latex: {sum(d["latex"] for d in math_docs)/len(math_docs):.1f}')
print(f'平均math_kw: {sum(d["math_kw"] for d in math_docs)/len(math_docs):.1f}')
print(f'含历史地位: {sum(d["hist"] for d in math_docs)}')
print(f'含现代发展: {sum(d["modern"] for d in math_docs)}')
print(f'含文档信息: {sum(d["doc_info"] for d in math_docs)}')
print(f'含模板结尾: {sum(d["template_end"] for d in math_docs)}')

print()
print('=== 01-核心理论 下的文档 ===')
core_docs = [d for d in data if '01-核心理论' in d['rel']]
print(f'数量: {len(core_docs)}')
if core_docs:
    print(f'平均大小: {sum(d["size"] for d in core_docs)/len(core_docs):.0f}')
    print(f'平均latex: {sum(d["latex"] for d in core_docs)/len(core_docs):.1f}')
    print(f'平均math_kw: {sum(d["math_kw"] for d in core_docs)/len(core_docs):.1f}')

print()
print('=== 其他目录 下的文档 ===')
other_docs = [d for d in data if not d['in_math'] and '01-核心理论' not in d['rel'] and d['rel'] not in ['README.md', 'START-HERE.md', '00-文档索引.md', '00-项目状态.md']]
print(f'数量: {len(other_docs)}')
if other_docs:
    print(f'平均大小: {sum(d["size"] for d in other_docs)/len(other_docs):.0f}')
    print(f'平均latex: {sum(d["latex"] for d in other_docs)/len(other_docs):.1f}')
    print(f'平均math_kw: {sum(d["math_kw"] for d in other_docs)/len(other_docs):.1f}')

# 找出math_docs中math_kw最低的10个
print()
print('=== 02-数学内容深度分析 中数学关键词最少的文档 ===')
math_docs_sorted = sorted(math_docs, key=lambda x: x['math_kw'])
for d in math_docs_sorted[:15]:
    print(f'{d["rel"]}: size={d["size"]}, chinese={d["chinese"]}, latex={d["latex"]}, math_kw={d["math_kw"]}, hist={d["hist"]}, modern={d["modern"]}')
