import os

docs_dir = r'G:\_src\FormalMath\docs\00-银层核心课程\Harvard-232br-代数几何'

exercises = {
    'II.5-模与层.md': r'''
## 习题

**习题 1.1**。证明：拟凝聚层 $\\mathcal{F}$ 在仿射概形 $\\operatorname{Spec} A$ 上由 $A$-模 $M = \\Gamma(X, \\mathcal{F})$ 完全决定。

*解答*：在仿射情形下，拟凝聚层的定义即为与某个 $A$-模 $M$ 相关联的层 $\\widetilde{M}$。由层的整体截面可恢复模结构，反之亦然。$\square$

---

**习题 1.2**。举例说明：局部自由层不一定是自由层。

*解答*：$\\mathbb{P}^1$ 上的切丛 $\\mathcal{T}_{\\mathbb{P}^1} \\cong \\mathcal{O}(2)$ 是局部自由的（在仿射覆盖上自由），但整体截面空间维数为3，而秩为1的自由层 $\\mathcal{O}$ 的整体截面维数为1，故 $\\mathcal{O}(2)$ 不是自由层。$\square$
''',
    'II.5-模与层-续.md': r'''
## 习题

**习题 1.1**。设 $0 \\to \\mathcal{F}' \\to \\mathcal{F} \\to \\mathcal{F}'' \\to 0$ 是层的短正合列。证明若 $\\mathcal{F}'$ 和 $\\mathcal{F}''$ 拟凝聚，则 $\\mathcal{F}$ 也拟凝聚。

*解答*：拟凝聚性是局部的，且在仿射开集上对应模的正合列。模的扩张保持有限生成性（在Noetherian环上），故 $\\mathcal{F}$ 拟凝聚。$\square$

---

**习题 1.2**。描述 $\\mathbb{P}^1$ 上可逆层（线丛）的Picard群 $\\operatorname{Pic}(\\mathbb{P}^1)$。

*解答*：$\\operatorname{Pic}(\\mathbb{P}^1) \\cong \\mathbb{Z}$，由 $\\mathcal{O}(n)$ 生成。任意可逆层同构于某个 $\\mathcal{O}(n)$。$\square$
''',
    'II.6-除子.md': r'''
## 习题

**习题 1.1**。在 $\\mathbb{P}^1$ 上，Weil除子与Cartier除子是否等价？为什么？

*解答*：是。$\\mathbb{P}^1$ 是正则Noetherian整概形（维数1），在这种情形下Weil除子与Cartier除子自然等价。$\square$

---

**习题 1.2**。计算 $\\mathbb{P}^2$ 中直线 $L = V(x)$ 的Weil除子类。

*解答*：$L$ 是素除子（不可约 codimension 1 子簇），其除子类为 $[L] \\in \\operatorname{Cl}(\\mathbb{P}^2) \\cong \\mathbb{Z}$。因 $\\operatorname{Cl}(\\mathbb{P}^2)$ 由超平面类生成，$[L] = 1$。$\square$
''',
    'II.7-射影态射.md': r'''
## 习题

**习题 1.1**。证明：闭浸入是射影态射。

*解答*：闭浸入 $Z \\hookrightarrow X$ 可看作由 $\\mathcal{O}_X$ 的某个理想层 $\\mathcal{I}$ 确定的相对Proj，即 $Z \\cong \\operatorname{Proj} \\bigoplus \\mathcal{I}^n / \\mathcal{I}^{n+1}$。$\square$

---

**习题 1.2**。说明为什么 $\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 不是射影态射。

*解答*：射影态射要求存在到某个 $\\mathbb{P}^n$ 的闭浸入分解。$\\mathbb{A}^1$ 不是紧的（在经典拓扑下），而射影态射的纤维是紧的（proper），故 $\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 不是射影的。$\square$
''',
    'II.8-微分形式.md': r'''
## 习题

**习题 1.1**。设 $X = \\operatorname{Spec} A$ 是仿射概形。证明 $\\Omega_{X/k} \\cong \\widetilde{\\Omega_{A/k}}$。

*解答*：Kähler微分模 $\\Omega_{A/k}$ 是 $A$-模，其相伴层 $\\widetilde{\\Omega_{A/k}}$ 满足层的泛性质，故同构于 $\\Omega_{X/k}$。$\square$

---

**习题 1.2**。计算 $\\mathbb{A}^1 = \\operatorname{Spec} k[x]$ 上的微分层 $\\Omega_{\\mathbb{A}^1/k}$。

*解答*：$\\Omega_{k[x]/k} = k[x]\\,dx$（自由 $k[x]$-模，秩1）。故 $\\Omega_{\\mathbb{A}^1/k} \\cong \\mathcal{O}_{\\mathbb{A}^1}$。$\square$
''',
    'II.9-形式概形.md': r'''
## 习题

**习题 1.1**。解释形式概形与普通概形的主要区别。

*解答*：形式概形允许“无限小邻域”的信息，即沿着闭子概形的完备化。普通概形是局部环空间，而形式概形是拓扑环空间，其结构层是完备拓扑环。$\square$

---

**习题 1.2**。设 $X$ 是概形，$Y \\subseteq X$ 是闭子概形。描述 $X$ 沿 $Y$ 的完备化 $\\widehat{X}_Y$ 的直观意义。

*解答*：$\\widehat{X}_Y$ 保留了 $Y$ 及其任意阶无限小邻域的信息，丢弃了远离 $Y$ 的几何。形式函数的Taylor展开在此完备化上收敛。$\square$
''',
    'III.2-导出函子与上同调基本性质.md': r'''
## 习题

**习题 1.1**。证明 $H^0(X, \\mathcal{F}) = \\Gamma(X, \\mathcal{F})$，即整体截面函子的导出函子在0阶恢复整体截面。

*解答*：导出函子的定义：$R^0F = F$（对任何左正合函子 $F$）。整体截面函子 $\\Gamma$ 左正合，故 $H^0 = R^0\\Gamma = \\Gamma$。$\square$

---

**习题 1.2**。设 $X$ 是仿射概形。证明对任意拟凝聚层 $\\mathcal{F}$ 和 $i > 0$，$H^i(X, \\mathcal{F}) = 0$。

*解答*：Serre定理：仿射概形上拟凝聚层的上同调在正阶消失。这是仿射性的上同调刻画。$\square$
''',
    'III.3-Čech上同调与导出上同调.md': r'''
## 习题

**习题 1.1**。在什么条件下Čech上同调 $\\check{H}^i(\\mathfrak{U}, \\mathcal{F})$ 与导出上同调 $H^i(X, \\mathcal{F})$ 一致？

*解答*：当 $X$ 是仿射概形或覆盖 $\\mathfrak{U}$ 满足 $H^j(U_{i_0\\cap\\cdots\\cap U_{i_p}, \\mathcal{F}) = 0$（$j > 0$）时，Čech上同调与导出上同调一致（Leray定理）。$\square$

---

**习题 1.2**。用Čech上同调计算 $H^1(\\mathbb{P}^1, \\mathcal{O})$。

*解答*：取标准仿射覆盖 $\\mathbb{P}^1 = U_0 \\cup U_1$。Čech复形：$\\check{C}^0 = \\mathcal{O}(U_0) \\oplus \\mathcal{O}(U_1) = k[x] \\oplus k[x^{-1}]$，$\\check{C}^1 = \\mathcal{O}(U_0 \\cap U_1) = k[x, x^{-1}]$。差分映射 $\\delta(f,g) = g - f$。$\\ker\\delta$ 中的元素是同时在 $U_0$ 和 $U_1$ 正则的函数，即常数。$\\operatorname{im}\\delta = k[x] + k[x^{-1}]$。$H^1 = k[x,x^{-1}]/(k[x]+k[x^{-1}]) = 0$（因任何Laurent多项式可分解为正幂和负幂部分）。$\square$
''',
    'III.4-上同调计算与应用.md': r'''
## 习题

**习题 1.1**。用Riemann-Roch定理计算 $\\mathbb{P}^1$ 上 $H^0(\\mathbb{P}^1, \\mathcal{O}(n))$ 的维数。

*解答*：$\\mathbb{P}^1$ 亏格 $g=0$，$\\deg \\mathcal{O}(n) = n$。Riemann-Roch：$l(D) - l(K-D) = \\deg D + 1 - g = n + 1$。当 $n \\geq 0$，$K-D$ 次数为 $-2-n < 0$，故 $l(K-D)=0$，$l(D)=n+1$。$\square$

---

**习题 1.2**。陈述Kodaira消失定理，并说明其在代数几何中的重要性。

*解答*：Kodaira消失：设 $X$ 是光滑射影簇，$\\mathcal{L}$ 是丰富线丛，则 $H^i(X, K_X \\otimes \\mathcal{L}) = 0$（$i > 0$）。重要性：提供计算上同调的强大工具，是Enriques-Kodaira分类的基础。$\square$
''',
    'IV.1-IV.4-曲线基本理论.md': r'''
## 习题

**习题 1.1**。设 $C$ 是光滑射影曲线，$P \\in C$。证明存在非恒定有理函数 $f \\in k(C)$ 仅在 $P$ 处有极点。

*解答*：由Riemann-Roch，$l(nP) = n + 1 - g + l(K-nP)$。当 $n$ 充分大，$l(nP) \\geq 2$，故存在非常数函数仅以 $P$ 为极点。$\square$

---

**习题 1.2**。计算椭圆曲线 $E: y^2 = x^3 - x$ 的亏格。

*解答*：平面曲线 $y^2 = x^3 - x$ 是光滑三次曲线。由平面曲线亏格公式 $g = (d-1)(d-2)/2 = (3-1)(3-2)/2 = 1$。$\square$
''',
    'IV.5-IV.6-曲线深化.md': r'''
## 习题

**习题 1.1**。陈述Hurwitz定理，并计算 $\\mathbb{P}^1 \\to \\mathbb{P}^1$ 的 $d$ 次覆叠的分歧点数量。

*解答*：Hurwitz：$2g(X)-2 = d(2g(Y)-2) + \\sum_{P} (e_P - 1)$。对 $\\mathbb{P}^1 \\to \\mathbb{P}^1$，$g=0$，故 $-2 = -2d + \\sum(e_P-1)$，$\\sum(e_P-1) = 2d-2$。$\square$

---

**习题 1.2**。证明：曲线 $C$ 的典范映射 $\\phi_K: C \\to \\mathbb{P}^{g-1}$ 是嵌入当且仅当 $C$ 不是超椭圆曲线。

*解答*：若 $C$ 超椭圆，$K$ 由超椭圆映射 $C \\to \\mathbb{P}^1$ 拉回，$\\phi_K$ 分解为此映射与Veronese嵌入的复合，不是嵌入。若非超椭圆，$K$ 是非常丰富的。$\square$
''',
    'V.1-V.3-曲面初步.md': r'''
## 习题

**习题 1.1**。计算 $\\mathbb{P}^2$  blown up at a point 的Picard数和相交形式。

*解答*：$\\operatorname{Pic}(\\operatorname{Bl}_P \\mathbb{P}^2) = \\mathbb{Z}H \\oplus \\mathbb{Z}E$，其中 $H$ 是严格变换的超平面类，$E$ 是例外除子。相交形式：$H^2=1, E^2=-1, H\\cdot E=0$。$\square$

---

**习题 1.2**。陈述Castelnuovo判别法：何时一个曲面是有理曲面？

*解答*：Castelnuovo：光滑射影曲面 $S$ 是有理曲面当且仅当 $q = P_2 = 0$（其中 $q = h^1(\\mathcal{O}_S)$，$P_2 = h^0(2K_S)$）。$\square$
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
