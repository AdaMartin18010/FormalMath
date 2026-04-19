import os, re

base = r'G:\_src\FormalMath\docs'
files_to_fix = [
    r'G:\_src\FormalMath\docs\00-银层核心课程\Harvard-232br-代数几何\II.2-概形的基本性质.md',
    r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.100A-实分析\介值定理.md',
    r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.100A-实分析\比较判别法.md',
    r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数\群第一同构定理.md',
    r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数\轨道稳定子定理.md',
    r'G:\_src\FormalMath\docs\02-代数结构\02-核心理论\MIT-18.701\01-拉格朗日定理.md',
]

for path in files_to_fix:
    if not os.path.exists(path):
        print(f'MISSING: {path}')
        continue
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    new_content = re.sub(r'(?<!\*\*)(?<!# )(命题\s+\d+(?:\.\d+)+)', r'**\1**', content)
    new_content = re.sub(r'(?<!\*\*)(?<!# )(引理\s+\d+(?:\.\d+)+)', r'**\1**', new_content)
    new_content = re.sub(r'(?<!\*\*)(?<!# )(推论\s+\d+(?:\.\d+)+)', r'**\1**', new_content)
    if new_content != content:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        print(f'Fixed: {os.path.basename(path)}')
    else:
        print(f'No change: {os.path.basename(path)}')
