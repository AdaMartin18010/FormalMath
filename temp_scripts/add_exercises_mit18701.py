import os

docs_dir = r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数'

exercises = {
    'Ch01-群论基础.md': r'''
## 习题

**习题 1.1**。证明：群 $G$ 中单位元唯一，且每个元素的逆元唯一。

*解答*：设 $e, e'$ 都是单位元，则 $e = ee' = e'$。设 $b, c$ 都是 $a$ 的逆元，则 $b = be = b(ac) = (ba)c = ec = c$。$\square$

---

**习题 1.2**。判断下列集合在给定运算下是否构成群：$\mathbb{Z}$ 在加法下；$\mathbb{Z}$ 在乘法下；$\mathbb{Q}\\setminus\\{0\\}$ 在乘法下。

*解答*：$\mathbb{Z}$ 在加法下是群（单位元0，逆元$-n$）。$\mathbb{Z}$ 在乘法下不是群（2没有乘法逆元）。$\mathbb{Q}\\setminus\\{0\\}$ 在乘法下是群。$\square$
''',
    'Ch02-子群与Lagrange定理.md': r'''
## 习题

**习题 1.1**。求 $S_3$ 的所有子群。

*解答*：$|S_3|=6$。由Lagrange定理，子群阶数只能是1,2,3,6。阶2子群：$\\{e,(12)\\}, \\{e,(13)\\}, \\{e,(23)\\}$；阶3子群：$\\{e,(123),(132)\\}$；阶1和6为平凡子群。$\square$

---

**习题 1.2**。设 $H$ 是群 $G$ 的子群，$a\\in G$。证明 $|aH| = |H|$。

*解答*：映射 $f: H \\to aH$，$f(h)=ah$ 是双射（逆映射 $f^{-1}(x)=a^{-1}x$）。故 $|aH|=|H|$。$\square$
''',
    'Ch03-同态与同构.md': r'''
## 习题

**习题 1.1**。定义 $\\phi: \\mathbb{Z} \\to \\mathbb{Z}_n$ 为 $\\phi(k) = k \\bmod n$。证明 $\\phi$ 是满同态，并求 $\\ker \\phi$。

*解答*：$\\phi(a+b) = (a+b) \\bmod n = \\phi(a) + \\phi(b)$，故为同态。显然满射。$\\ker \\phi = \\{kn : k \\in \\mathbb{Z}\\} = n\\mathbb{Z}$。$\square$

---

**习题 1.2**。证明第一同构定理：若 $\\phi: G \\to G'$ 是满同态，则 $G/\\ker\\phi \\cong G'$。

*解答*：定义 $\\bar{\\phi}(g\\ker\\phi) = \\phi(g)$。良定性：若 $g_1^{-1}g_2 \\in \\ker\\phi$，则 $\\phi(g_1)=\\phi(g_2)$。同态、满射显然。单射：若 $\\bar{\\phi}(g\\ker\\phi)=e'$，则 $\\phi(g)=e'$，$g\\in\\ker\\phi$。$\square$
''',
    'Ch04-环与理想.md': r'''
## 习题

**习题 1.1**。证明 $\\mathbb{Z}[i] = \\{a+bi : a,b\\in\\mathbb{Z}\\}$ 是环，并求其单位群。

*解答*：对加减乘封闭，是子环。单位：若 $(a+bi)(c+di)=1$，取范数 $(a^2+b^2)(c^2+d^2)=1$，故 $a^2+b^2=1$，即 $a+bi \\in \\{\\pm 1, \\pm i\\}$。$\square$

---

**习题 1.2**。证明 $I = \\{2a : a\\in\\mathbb{Z}\\}$ 是 $\\mathbb{Z}$ 的理想，且 $\\mathbb{Z}/I \\cong \\mathbb{Z}_2$。

*解答*：对减法和乘法吸收封闭。定义 $\\phi(n)=n\\bmod 2$，核为 $I$，由第一同构定理即得。$\square$
''',
    'Ch05-唯一分解整环.md': r'''
## 习题

**习题 1.1**。在 $\\mathbb{Z}[\\sqrt{-5}]$ 中，证明 $6 = 2\\cdot 3 = (1+\\sqrt{-5})(1-\\sqrt{-5})$ 给出两种不同的不可约元分解，故 $\\mathbb{Z}[\\sqrt{-5}]$ 不是UFD。

*解答*：验证 $2,3,1\\pm\\sqrt{-5}$ 均不可约（范数分别为4,9,6，若可约则因子范数更小，但无合适因子）。$2$ 与 $1\\pm\\sqrt{-5}$ 不相伴。$\square$

---

**习题 1.2**。证明 $\\mathbb{Z}[i]$ 是欧几里得整环（从而也是UFD）。

*解答*：范数 $N(a+bi)=a^2+b^2$ 作为欧几里得函数。对任意 $\\alpha,\\beta\\neq 0$，在 $\\mathbb{C}$ 中 $\\alpha/\\beta = q+r$ 其中 $q\\in\\mathbb{Z}[i]$，$|r|<1$，故 $N(\\alpha-q\\beta)<N(\\beta)$。$\square$
''',
    'Ch06-域扩张.md': r'''
## 习题

**习题 1.1**。求 $[\\mathbb{Q}(\\sqrt{2},\\sqrt{3}):\\mathbb{Q}]$ 并给出 $\\mathbb{Q}(\\sqrt{2},\\sqrt{3})$ 在 $\\mathbb{Q}$ 上的一组基。

*解答*：$[\\mathbb{Q}(\\sqrt{2}):\\mathbb{Q}]=2$，$\\sqrt{3}\\notin\\mathbb{Q}(\\sqrt{2})$（否则 $\\sqrt{3}=a+b\\sqrt{2}$，平方后矛盾），故 $[\\mathbb{Q}(\\sqrt{2},\\sqrt{3}):\\mathbb{Q}(\\sqrt{2})]=2$。总次数为4。基：$\\{1,\\sqrt{2},\\sqrt{3},\\sqrt{6}\\}$。$\square$

---

**习题 1.2**。证明 $\\sqrt{2}+\\sqrt{3}$ 在 $\\mathbb{Q}$ 上的极小多项式为 $x^4-10x^2+1$。

*解答*：令 $\\alpha=\\sqrt{2}+\\sqrt{3}$，则 $\\alpha^2=5+2\\sqrt{6}$，$\\alpha^4=49+20\\sqrt{6}=10\\alpha^2-1$。故 $\\alpha^4-10\\alpha^2+1=0$。验证不可约（无有理根，不能分解为两个二次式）。$\square$
''',
    'Ch07-Galois理论.md': r'''
## 习题

**习题 1.1**。求 $x^3-2$ 在 $\\mathbb{Q}$ 上的分裂域 $K$ 的Galois群 $\\operatorname{Gal}(K/\\mathbb{Q})$。

*解答*：根为 $\\sqrt[3]{2}, \\omega\\sqrt[3]{2}, \\omega^2\\sqrt[3]{2}$，其中 $\\omega=e^{2\\pi i/3}$。分裂域 $K=\\mathbb{Q}(\\sqrt[3]{2},\\omega)$，$[K:\\mathbb{Q}]=6$。Galois群同构于 $S_3$（6个自同构，对应根的置换）。$\square$

---

**习题 1.2**。用Galois理论证明：一般五次方程没有根式解。

*解答*： Abel-Ruffini定理：$S_5$ 不是可解群（因其单因子 $A_5$ 非交换单群）。一般五次方程的Galois群为 $S_5$，故分裂域不可根式扩张。$\square$
'''
}

for fname, ex_content in exercises.items():
    fpath = os.path.join(docs_dir, fname)
    if not os.path.exists(fpath):
        print(f'MISSING: {fname}')
        continue
    with open(fpath, 'r', encoding='utf-8') as f:
        content = f.read()
    marker = '**参考文献**'
    if marker in content:
        new_content = content.replace(marker, ex_content + '\n\n' + marker)
    else:
        new_content = content + '\n' + ex_content
    with open(fpath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    print(f'UPDATED: {fname}')

print('Done.')
