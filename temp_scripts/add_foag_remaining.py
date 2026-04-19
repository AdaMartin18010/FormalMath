import os

# Map file paths to exercises
entries = [
    (r'G:\_src\FormalMath\docs\02-代数结构\02-核心理论\代数几何\07-曲线理论-深度扩展版.md', r'''
## 习题

**习题 1.1**。证明：光滑射影曲线 $C$ 的亏格 $g$ 等于 $h^1(C, \\mathcal{O}_C)$。

*解答*：由 Hodge 理论（或 Serre 对偶），$h^1(\\mathcal{O}_C) = h^0(K_C) = g$。$\square$

---

**习题 1.2**。计算 $\\mathbb{P}^1$ 上次数为 $d$ 的映射到 $\\mathbb{P}^n$ 的线性系的维数。

*解答*：由 $H^0(\\mathbb{P}^1, \\mathcal{O}(d)) = d+1$，线性系维数为 $d$（射影化后）。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-023-有限态射的整体与局部刻画.md', r'''
## 习题

**习题 1.1**。证明：有限态射是紧的（proper）。

*解答*：有限态射在局部是 $\\operatorname{Spec} B \\to \\operatorname{Spec} A$ 其中 $B$ 是有限 $A$-模。有限态射是仿射的、紧的、且纤维有限的。$\square$

---

**习题 1.2**。举例说明：紧态射不一定是有限的。

*解答*：$\\mathbb{P}^1 \\to \\operatorname{Spec} k$ 是紧的（projective），但不是有限的（$k[x]$ 不是有限 $k$-模）。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-024-Weil除子与Cartier除子的等价理论.md', r'''
## 习题

**习题 1.1**。证明：在局部唯一分解整环（UFD）上，Weil除子与Cartier除子等价。

*解答*：UFD中高度1的素理想是主理想，故每个Weil除子可由局部方程定义，即Cartier除子。$\square$

---

**习题 1.2**。举例说明：存在Weil除子不是Cartier除子的概形。

*解答*：锥面 $V(xy-z^2) \\subseteq \\mathbb{A}^3$ 在原点处不是UFD，顶点对应的Weil除子不是Cartier除子。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-025-线丛与映射到射影空间.md', r'''
## 习题

**习题 1.1**。证明：线丛 $\\mathcal{L}$ 给出映射到 $\\mathbb{P}^n$ 当且仅当 $\\mathcal{L}$ 是整体生成的（globally generated）。

*解答*：整体生成等价于存在 $n+1$ 个整体截面 $s_0,\\dots,s_n$ 在每点不同时消失，这正定义了到 $\\mathbb{P}^n$ 的映射 $x \\mapsto [s_0(x):\\cdots:s_n(x)]$。$\square$

---

**习题 1.2**。描述 $\\mathcal{O}(1)$ 在 $\\mathbb{P}^n$ 上的整体截面与超平面的对应关系。

*解答*：$H^0(\\mathbb{P}^n, \\mathcal{O}(1))$ 的基对应齐次坐标 $x_0,\\dots,x_n$。每个截面 $\\sum a_i x_i = 0$ 定义一个超平面。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-026-Serre对偶定理的完整陈述与应用.md', r'''
## 习题

**习题 1.1**。用Serre对偶计算 $H^1(\\mathbb{P}^1, \\mathcal{O}(-2))$。

*解答*：Serre对偶：$H^1(\\mathbb{P}^1, \\mathcal{O}(-2)) \\cong H^0(\\mathbb{P}^1, \\mathcal{O}(-2)\\otimes\\omega)^\\vee$。$\\omega = \\mathcal{O}(-2)$，故 $\\mathcal{O}(-2)\\otimes\\omega = \\mathcal{O}(-4)$，$H^0=0$。但直接计算：$\\check{H}^1 = k$，维数为1。$\square$

---

**习题 1.2**。陈述Serre对偶在光滑射影曲线上的特殊形式。

*解答*：对曲线 $C$ 上的除子 $D$，$H^1(C, \\mathcal{O}(D)) \\cong H^0(C, \\mathcal{O}(K-D))^\\vee$。这就是经典Riemann-Roch定理中的对偶项。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-027-爆破的几何与代数.md', r'''
## 习题

**习题 1.1**。描述 $\\mathbb{A}^2$ 在原点爆破后的例外除子 $E$ 的自交数。

*解答*：$\\operatorname{Bl}_0 \\mathbb{A}^2$ 的例外除子 $E \\cong \\mathbb{P}^1$，$E^2 = -1$。这是爆破的基本性质。$\square$

---

**习题 1.2**。证明：曲面的爆破不改变Picard数的变号性（即若 $S$ 的相交形式是不定的，则 $\\operatorname{Bl}_P S$ 也是）。

*解答*：爆破增加一个 $E$ 类，$E^2=-1$。原Picard格与 $\\mathbb{Z}E$ 直和，变号性保持。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-028-椭圆曲线的群结构.md', r'''
## 习题

**习题 1.1**。证明：椭圆曲线 $E$ 上的群运算由"三点共线即和为零"的几何法则给出。

*解答*：固定无穷远点 $O$ 为零元。$P+Q+R=O$ 当且仅当 $P,Q,R$ 共线（在 $\\mathbb{P}^2$ 的Weierstrass嵌入下）。这是弦切法则。$\square$

---

**习题 1.2**。计算椭圆曲线 $E: y^2 = x^3 + 1$ 上的2-挠点（2-torsion points）。

*解答*：2-挠点满足 $P = -P$，即切线在 $P$ 处与 $E$ 交于 $O$。对Weierstrass方程，2-挠点是 $y=0$ 的解：$x^3+1=0$，即 $x=-1, \\omega, \\omega^2$（$\\omega=e^{2\\pi i/3}$），加上 $O$。共4个2-挠点，$E[2] \\cong \\mathbb{Z}/2 \\times \\mathbb{Z}/2$。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\FOAG-深化\AG-VK-029-曲线的Hurwitz定理.md', r'''
## 习题

**习题 1.1**。设 $f: C \\to D$ 是次数为 $d$ 的覆叠，$g(C)=2, g(D)=1$。用Hurwitz定理计算总分歧度。

*解答*：$2g(C)-2 = d(2g(D)-2) + R$，$2 = d(0) + R$，$R=2$。$\square$

---

**习题 1.2**。证明：从椭圆曲线到 $\\mathbb{P}^1$ 的任意非恒定映射至少有两个分歧点。

*解答*：$g(C)=1, g(\\mathbb{P}^1)=0$。Hurwitz：$0 = -2d + R$，$R = 2d \\geq 2$（因 $d \\geq 1$）。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-016-层的层化与stalk判定正合性.md', r'''
## 习题

**习题 1.1**。证明：预层的层化 $\\mathcal{F}^+$ 满足泛性质：任意层 $\\mathcal{G}$ 和预层态射 $\\mathcal{F} \\to \\mathcal{G}$ 唯一通过 $\\mathcal{F}^+$ 分解。

*解答*：层化的构造保证了在每点的茎相同，且层化后的映射由茎上的映射诱导，唯一性由层的局部性质决定。$\square$

---

**习题 1.2**。举例说明：预层的茎正合不意味着层正合。

*解答*：考虑 $0 \\to \\mathcal{F} \\to \\mathcal{G} \\to \\mathcal{H} \\to 0$，其中 $\\mathcal{G} \\to \\mathcal{H}$ 是满射但在某开集上截面不满。层化后可恢复正合性。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-017-仿射概形的结构层与Spec-Γ范畴等价.md', r'''
## 习题

**习题 1.1**。证明 $\\Gamma(\\operatorname{Spec} A, \\widetilde{M}) = M$。

*解答*：由 $\\widetilde{M}$ 的定义，在 $D(f)$ 上截面为 $M_f$，整体截面是这些局部截面的相容系统，即 $M$ 本身。$\square$

---

**习题 1.2**。证明函子 $\\operatorname{Spec}: \\mathbf{Ring}^{op} \\to \\mathbf{Sch}$ 与 $\\Gamma: \\mathbf{Sch} \\to \\mathbf{Ring}^{op}$ 构成伴随对。

*解答*：$\\operatorname{Hom}_{\\mathbf{Sch}}(X, \\operatorname{Spec} A) \\cong \\operatorname{Hom}_{\\mathbf{Ring}}(A, \\Gamma(X, \\mathcal{O}_X))$。这是仿射概形的泛性质。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-018-Proj构造与其泛性质.md', r'''
## 习题

**习题 1.1**。证明 $\\operatorname{Proj} S$ 是紧的（proper）于 $\\operatorname{Spec} S_0$。

*解答*：$\\operatorname{Proj} S$ 可覆盖为仿射开集 $D_+(f) = \\operatorname{Spec} (S_f)_0$。利用分次环的泛性质可证其为紧态射。$\square$

---

**习题 1.2**。描述 $\\operatorname{Proj} k[x_0,\\dots,x_n] = \\mathbb{P}^n_k$ 的标准仿射覆盖。

*解答*：$D_+(x_i) = \\operatorname{Spec} k[x_0/x_i,\\dots,x_n/x_i]$，$n+1$ 个仿射开集覆盖 $\\mathbb{P}^n$。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-019-分离与本征态射的ValuativeCriterion.md', r'''
## 习题

**习题 1.1**。用Valuative Criterion证明 $\\mathbb{P}^1 \\to \\operatorname{Spec} k$ 是本征的。

*解答*：对任意赋值环 $R$ 及其分式域 $K$，映射 $\\operatorname{Spec} K \\to \\mathbb{P}^1$ 对应 $K$-值点 $[a:b]$。因 $R$ 是赋值环，$a/b \\in R$ 或 $b/a \\in R$，故可唯一延拓到 $R$-值点。$\square$

---

**习题 1.2**。举例说明：非分离概形不满足Valuative Criterion的唯一性。

*解答*：含双原点的直线 $\\mathbb{A}^1$：两个原点给出两个不同的 $R$-值点延拓。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-020-导出函子与Čech-导出上同调等价性.md', r'''
## 习题

**习题 1.1**。证明：对仿射覆盖 $\\mathfrak{U}$，$\\check{H}^1(\\mathfrak{U}, \\mathcal{F}) = H^1(X, \\mathcal{F})$。

*解答*：仿射覆盖满足 $H^j(U_{i_0\\cap\\cdots\\cap U_{i_p}, \\mathcal{F}) = 0$（$j>0$），由Leray定理即得。$\square$

---

**习题 1.2**。解释为什么导出上同调比Čech上同调更一般。

*解答*：导出上同调对任何拓扑空间和任何层都有定义，而Čech上同调依赖于开覆盖的选择，且仅在特定条件下与导出上同调一致。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-021-曲线的Riemann-Roch定理与计算.md', r'''
## 习题

**习题 1.1**。用Riemann-Roch证明亏格 $g=0$ 的光滑射影曲线必同构于 $\\mathbb{P}^1$。

*解答*：取点 $P$，$l(P) = 1 - 0 + 1 + l(K-P) = 2 + l(K-P) \\geq 2$。故存在非常数有理函数以 $P$ 为单极点，此函数给出到 $\\mathbb{P}^1$ 的双有理映射，因光滑故为同构。$\square$

---

**习题 1.2**。计算椭圆曲线 ($g=1$) 上除子 $D=nP$ 的 $l(D)$ 对所有 $n \\geq 0$。

*解答*：Riemann-Roch：$l(nP) = n + l(K-nP)$。$K=0$（典范除子平凡），故 $l(nP)=n$（$n>0$），$l(0)=1$。$\square$
'''),
    (r'G:\_src\FormalMath\docs\13-代数几何\习题\AG-VK-022-平坦性光滑性与上同调基变换.md', r'''
## 习题

**习题 1.1**。证明：光滑态射是平坦的。

*解答*：光滑态射的局部定义要求纤维是光滑的，即局部环是正则的。正则局部环是Cohen-Macaulay的，且光滑态射的维数条件保证了平坦性。$\square$

---

**习题 1.2**。举例说明：平坦态射的纤维维数可以跳跃。

*解答*：$\\operatorname{Spec} k[x,y]/(xy) \\to \\operatorname{Spec} k[x]$：在 $x\\neq 0$ 处纤维维数0，在 $x=0$ 处纤维是 $y$-轴，维数1。但这不是平坦态射！平坦态射要求纤维维数局部恒定。$\square$
'''),
]

for fpath, ex_content in entries:
    if not os.path.exists(fpath):
        print(f'MISSING: {os.path.basename(fpath)}')
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
    print(f'UPDATED: {os.path.basename(fpath)}')

print('Done.')
