import os

docs_dir = r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数'

exercises = {
    'Cauchy定理.md': r'''
## 习题

**习题 1.1**。设 $G$ 是有限群，$p$ 是素数且 $p \\mid |G|$。用 Cauchy 定理证明 $G$ 中存在阶为 $p$ 的元素。

*解答*：Cauchy 定理直接给出存在 $g\\in G$ 使 $|g|=p$。$\square$

---

**习题 1.2**。证明：$p$-群（阶为 $p^n$ 的群）的中心非平凡。

*解答*：由类方程，$|G| = |Z(G)| + \\sum [G:C_G(x_i)]$。每个 $[G:C_G(x_i)]$ 是 $p$ 的幂且大于1，故 $p \\mid |Z(G)|$，$Z(G)\\neq\\{e\\}$。$\square$
''',
    'Sylow第一定理.md': r'''
## 习题

**习题 1.1**。求 $S_4$ 的一个 Sylow 2-子群和一个 Sylow 3-子群。

*解答*：$|S_4|=24=2^3\\cdot 3$。Sylow 2-子群阶为8：可取 $D_8$（正方形对称群）嵌入 $S_4$。Sylow 3-子群阶为3：$\\{e,(123),(132)\\}$。$\square$

---

**习题 1.2**。设 $P$ 是 $G$ 的 Sylow $p$-子群，$H$ 是 $G$ 的子群且 $N_G(P)\\subseteq H$。证明 $H = N_G(H)$。

*解答*：显然 $H\\subseteq N_G(H)$。设 $g\\in N_G(H)$，则 $gPg^{-1}\\subseteq H$ 也是 $H$ 的 Sylow $p$-子群。由 Sylow 定理，存在 $h\\in H$ 使 $gPg^{-1}=hPh^{-1}$，故 $h^{-1}g\\in N_G(P)\\subseteq H$，$g\\in H$。$\square$
''',
    '多项式环唯一分解定理.md': r'''
## 习题

**习题 1.1**。证明 $\\mathbb{Z}[x]$ 是UFD但不是PID。

*解答*：$\\mathbb{Z}$ 是UFD，故 $\\mathbb{Z}[x]$ 是UFD（Gauss引理）。理想 $(2,x)$ 不是主理想（若 $(2,x)=(f)$，则 $f\\mid 2$ 且 $f\\mid x$，故 $f=\\pm 1$，但 $1\\notin(2,x)$）。$\square$

---

**习题 1.2**。在 $\\mathbb{Z}[x]$ 中分解 $x^4+4$。

*解答*：$x^4+4 = (x^2+2x+2)(x^2-2x+2)$（Sophie Germain恒等式）。$\square$
''',
    '轨道稳定子定理.md': r'''
## 习题

**习题 1.1**。设群 $G$ 作用于集合 $X$，$x\\in X$。证明 $|Gx| = [G:G_x]$。

*解答*：定义 $\\phi: G/G_x \\to Gx$，$\\phi(gG_x)=gx$。良定：若 $g_1^{-1}g_2\\in G_x$，则 $g_1x=g_2x$。满射显然。单射：若 $g_1x=g_2x$，则 $g_1^{-1}g_2\\in G_x$。$\square$

---

**习题 1.2**。设 $p$-群 $G$ 作用于有限集 $X$，且 $|X|$ 不被 $p$ 整除。证明 $G$ 有不动点。

*解答*：由轨道分解 $|X| = \\sum |Gx_i| = \\sum [G:G_{x_i}]$。非单点轨道的阶被 $p$ 整除。因 $p\\nmid |X|$，必有单点轨道，即不动点。$\square$
''',
    '环第一同构定理.md': r'''
## 习题

**习题 1.1**。设 $\\phi: R \\to R'$ 是环的满同态。证明 $R/\\ker\\phi \\cong R'$。

*解答*：定义 $\\bar{\\phi}(a+\\ker\\phi)=\\phi(a)$。验证良定性、同态、满射、单射（同群第一同构定理）。$\square$

---

**习题 1.2**。证明 $\\mathbb{R}[x]/(x^2+1) \\cong \\mathbb{C}$。

*解答*：定义 $\\phi(f)=f(i)$，满射，核为 $(x^2+1)$（因 $x^2+1$ 在 $\\mathbb{R}[x]$ 中不可约）。由第一同构定理即得。$\square$
''',
    '拉格朗日定理.md': r'''
## 习题

**习题 1.1**。证明：任何群 $G$ 中，元素 $a$ 的阶整除 $|G|$。

*解答*：$|a| = |\\langle a \\rangle|$，而 $\\langle a \\rangle$ 是 $G$ 的子群。由 Lagrange 定理，$|\\langle a \\rangle| \\mid |G|$。$\square$

---

**习题 1.2**。设 $H,K$ 是有限群 $G$ 的子群。证明 $|HK| = \\frac{|H||K|}{|H\\cap K|}$。

*解答*：$HK = \\bigcup_{k\\in K} Hk$。每个陪集 $Hk$ 的大小为 $|H|$。$Hk_1 = Hk_2 \\Leftrightarrow k_1k_2^{-1}\\in H\\cap K$。故不同陪集数 = $[K:H\\cap K] = |K|/|H\\cap K|$。$\square$
''',
    '群第一同构定理.md': r'''
## 习题

**习题 1.1**。设 $\\phi: G \\to H$ 是群同态，$K\\trianglelefteq G$ 且 $K\\subseteq \\ker\\phi$。证明存在唯一的同态 $\\bar{\\phi}: G/K \\to H$ 使 $\\phi = \\bar{\\phi}\\circ\\pi$。

*解答*：定义 $\\bar{\\phi}(gK)=\\phi(g)$。良定：若 $g_1^{-1}g_2\\in K\\subseteq\\ker\\phi$，则 $\\phi(g_1)=\\phi(g_2)$。同态验证直接。唯一性由交换图决定。$\square$

---

**习题 1.2**。用第一同构定理证明 $SL_n(\\mathbb{R}) \\trianglelefteq GL_n(\\mathbb{R})$ 且 $GL_n(\\mathbb{R})/SL_n(\\mathbb{R}) \\cong \\mathbb{R}^\\times$。

*解答*：行列式映射 $\\det: GL_n(\\mathbb{R}) \\to \\mathbb{R}^\\times$ 是满同态，核为 $SL_n(\\mathbb{R})$。由第一同构定理即得。$\square$
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
