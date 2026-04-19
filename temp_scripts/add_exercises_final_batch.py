import os

# MIT 18.02 - multivariable calculus (alternate dir)
e1802_alt = {
    '01-向量与空间几何.md': r'''
## 习题

**习题 1.1**。求过点 $(1,2,3)$ 和 $(4,5,6)$ 的直线的参数方程。

*解答*：方向向量 $(3,3,3)$，参数方程 $x=1+3t, y=2+3t, z=3+3t$。$\square$

---

**习题 1.2**。求平面 $x+2y+3z=6$ 与三个坐标轴的交点，并画出截距三角形。

*解答*：$x$轴交点 $(6,0,0)$，$y$轴 $(0,3,0)$，$z$轴 $(0,0,2)$。$\square$
''',
    '02-多元函数与偏导数.md': r'''
## 习题

**习题 1.1**。设 $f(x,y)=x^2y+xy^2$，求 $\\frac{\\partial^2 f}{\\partial x\\partial y}$。

*解答*：$f_x=2xy+y^2$，$f_{xy}=2x+2y$。$\square$

---

**习题 1.2**。用链式法则求 $\\frac{d}{dt}f(x(t),y(t))$，其中 $f(x,y)=x^2+y^2$，$x(t)=\\cos t$，$y(t)=\\sin t$。

*解答*：$\\frac{df}{dt}=2x(-\\sin t)+2y(\\cos t)=-2\\cos t\\sin t+2\\sin t\\cos t=0$（符合 $f=1$ 为常数）。$\square$
''',
    '03-重积分.md': r'''
## 习题

**习题 1.1**。计算 $\\iint_R xy \\, dA$，其中 $R=[0,1]\\times[0,1]$。

*解答*：$\\int_0^1\\int_0^1 xy \\, dy \\, dx = \\int_0^1 \\frac{x}{2} \\, dx = \\frac{1}{4}$。$\square$

---

**习题 1.2**。用极坐标计算 $\\iint_D \\sqrt{x^2+y^2} \\, dA$，其中 $D$ 为单位圆盘。

*解答*：$\\int_0^{2\\pi}\\int_0^1 r\\cdot r \\, dr \\, d\\theta = 2\\pi \\cdot \\frac{1}{3} = \\frac{2\\pi}{3}$。$\square$
''',
    '04-积分应用.md': r'''
## 习题

**习题 1.1**。求曲线 $y=x^2$ 从 $x=0$ 到 $x=1$ 的弧长。

*解答*：$L=\\int_0^1 \\sqrt{1+(2x)^2} \\, dx = \\frac{1}{4}[2x\\sqrt{1+4x^2}+\\ln(2x+\\sqrt{1+4x^2})]_0^1$。$\square$

---

**习题 1.2**。求抛物面 $z=x^2+y^2$ 在 $x^2+y^2\\leq 4$ 上的表面积。

*解答*：$\\sqrt{1+z_x^2+z_y^2}=\\sqrt{1+4x^2+4y^2}$。极坐标下 $S=\\int_0^{2\\pi}\\int_0^2 \\sqrt{1+4r^2}\\cdot r \\, dr \\, d\\theta$。$\square$
''',
    '05-级数与泰勒展开.md': r'''
## 习题

**习题 1.1**。求 $f(x,y)=e^{x+y}$ 在 $(0,0)$ 处的二阶 Taylor 展开。

*解答*：$e^{x+y}=1+(x+y)+\\frac{(x+y)^2}{2}+\\cdots$。$\square$

---

**习题 1.2**。判断 $\\sum_{n=1}^{\\infty} \\frac{x^n}{n!}$ 的收敛域。

*解答*：由比值判别法，$\\frac{|x|}{n+1}\\to 0$ 对所有 $x$ 成立，故收敛域为 $\\mathbb{R}$（即 $e^x$ 的 Taylor 级数）。$\square$
''',
    '09-向量场与线积分.md': r'''
## 习题

**习题 1.1**。计算 $\\int_C \\mathbf{F}\\cdot d\\mathbf{r}$，其中 $\\mathbf{F}=(y,-x)$，$C$ 为从 $(0,0)$ 到 $(1,1)$ 的直线段。

*解答*：参数化 $\\mathbf{r}(t)=(t,t)$，$\\mathbf{F}(\\mathbf{r}(t))=(t,-t)$，$\\mathbf{r}'(t)=(1,1)$。积分 $=\\int_0^1 (t-t)\\cdot 1 \\, dt = 0$。$\square$

---

**习题 1.2**。判断 $\\mathbf{F}=(2x,2y)$ 是否保守场，若是求势函数。

*解答*：$\\frac{\\partial(2x)}{\\partial y}=0=\\frac{\\partial(2y)}{\\partial x}$，保守。$\\phi=x^2+y^2$。$\square$
'''
}

# Harvard 232br - first 4 docs only (sheaves, schemes, morphisms, separated/proper)
e232br = {
    'II.1-层的基本性质.md': r'''
## 习题

**习题 1.1**。证明：预层 $\\mathcal{F}$ 是层当且仅当对任意开覆盖 $\\{U_i\\}$，序列 $\\mathcal{F}(U) \\to \\prod \\mathcal{F}(U_i) \\rightrightarrows \\prod \\mathcal{F}(U_i\\cap U_j)$ 是等化子。

*解答*：层的定义直接对应此等化子条件：局部一致性推出全局存在性和唯一性。$\square$

---

**习题 1.2**。设 $X$ 是拓扑空间，$\\mathcal{F}$ 是常预层（对所有非空开集赋同一群 $G$）。证明 $\\mathcal{F}$ 的层化是常层 $\\underline{G}$。

*解答*：层化在每点的茎为 $G$，而常层 $\\underline{G}$ 的截面是局部常值函数，满足层的粘合条件。$\square$
''',
    'II.2-概形的基本性质.md': r'''
## 习题

**习题 1.1**。证明 $\\operatorname{Spec} \\mathbb{Z}$ 是终对象于概形范畴，即对任意概形 $X$，存在唯一的态射 $X \\to \\operatorname{Spec} \\mathbb{Z}$。

*解答*：由环的泛性质，$\\mathbb{Z}$ 是环范畴的始对象。$\\operatorname{Spec}$ 是反变函子，故 $\\operatorname{Spec}\\mathbb{Z}$ 是终对象。$\square$

---

**习题 1.2**。描述 $\\mathbb{A}^1_\\mathbb{C} = \\operatorname{Spec} \\mathbb{C}[x]$ 的闭点和generic point。

*解答*：闭点对应极大理想 $(x-a)$（$a\\in\\mathbb{C}$），即复平面上的点。Generic point 对应零理想 $(0)$。$\square$
''',
    'II.3-态射性质.md': r'''
## 习题

**习题 1.1**。证明：仿射态射 $f: X \\to Y$ 是紧的当且仅当对应的环同态使 $A$ 成为有限生成 $R$-模。

*解答*：仿射态射的紧性等价于 $\\operatorname{Spec} A \\to \\operatorname{Spec} R$ 的纤维有限，即 $A$ 是有限 $R$-模。$\square$

---

**习题 1.2**。举例说明：有限型态射不一定是有限的。

*解答*：$\\mathbb{A}^1 \\to \\operatorname{Spec} k$ 是有限型的（$k[x]$ 是有限生成 $k$-代数），但不是有限的（$k[x]$ 不是有限 $k$-模）。$\square$
''',
    'II.4-分离性与本征性.md': r'''
## 习题

**习题 1.1**。证明 $\\mathbb{A}^1$ 是分离的，但 $\\mathbb{A}^1$ 到 $\\operatorname{Spec} k$ 不是本征的。

*解答*：分离性：对角嵌入 $\\mathbb{A}^1 \\to \\mathbb{A}^2$ 是闭浸入。非本征：$\\mathbb{A}^1$ 不是紧的（在经典拓扑下同胚于 $\\mathbb{C}$，非紧）。$\square$

---

**习题 1.2**。用 Valuative Criterion 证明：若 $X$ 是本征的，则 $X$ 的任何整点 $\\operatorname{Spec} K \\to X$（$K$ 为域）可唯一延拓到 $\\operatorname{Spec} \\mathcal{O}_K \\to X$（$\\mathcal{O}_K$ 为赋值环）。

*解答*：这正是本征性的 Valuative Criterion。$\square$
'''
}

# Stanford FOAG
e_foag = {
    'Ch23-25-smooth-étale-flat态射.md': r'''
## 习题

**习题 1.1**。证明：光滑态射是平坦的，且纤维是光滑簇。

*解答*：光滑态射的局部定义要求 Jacobi 矩阵满秩，这推出平坦性（正则局部环是Cohen-Macaulay的）。纤维的维数恒定且正则，故光滑。$\square$

---

**习题 1.2**。举例说明：平坦态射不一定是光滑的。

*解答*：$\\operatorname{Spec} k[x,y]/(xy) \\to \\operatorname{Spec} k[x]$ 是平坦的（无挠），但在原点处纤维是结点，不光滑。$\square$
''',
    'Ch26-27-对偶理论.md': r'''
## 习题

**习题 1.1**。陈述 Serre 对偶定理对光滑射影簇 $X$ 上向量丛 $E$ 的形式。

*解答*：$H^i(X,E) \\cong H^{n-i}(X,E^\\vee \\otimes \\omega_X)^\\vee$，其中 $n=\\dim X$，$\\omega_X$ 是典范丛。$\square$

---

**习题 1.2**。用 Serre 对偶计算 $H^1(\\mathbb{P}^1, \\mathcal{O}(-2))$。

*解答*：$\\omega_{\\mathbb{P}^1}=\\mathcal{O}(-2)$。Serre对偶：$H^1(\\mathbb{P}^1,\\mathcal{O}(-2))\\cong H^0(\\mathbb{P}^1,\\mathcal{O})^\\vee\\cong k$。$\square$
''',
    'Ch28-29-上同调与基变换.md': r'''
## 习题

**习题 1.1**。陈述上同调与基变换定理（Cohomology and Base Change）在 $R^i f_*$ 与纤维上同调交换的条件。

*解答*：若 $f: X \\to Y$ 是紧的且平坦的，且对某 $i$，$R^i f_*\\mathcal{F}$ 是局部自由的，则 $(R^i f_*\\mathcal{F})_y \\cong H^i(X_y, \\mathcal{F}_y)$。$\square$

---

**习题 1.2**。举例说明：上同调与基变换不交换的情形。

*解答*：考虑退化椭圆曲线族 $y^2=x^3-t$ 在 $t\\to 0$ 时，$H^1$ 的维数可能跳跃。$\square$
''',
    'PartVI-L5-习题1.md': r'''
## 习题

**习题 1.1**。设 $X$ 是光滑射影曲线，$D$ 是有效除子。用 Riemann-Roch 定理计算 $l(D)$ 的表达式。

*解答*：$l(D)-l(K-D)=\\deg D+1-g$，其中 $g$ 是亏格，$K$ 是典范除子。$\square$

---

**习题 1.2**。在 $\\mathbb{P}^1$ 上，$\\deg K = -2$。验证 Riemann-Roch 定理对 $D=nP$（$P$ 为点，$n\\geq 0$）成立。

*解答*：$l(nP)=n+1$（$1,x,\\dots,x^n$），$l(K-nP)=0$（因 $\\deg(K-nP)<0$）。$n+1-0=n+1-0+1$，即 $n+1=n+1$。$\square$
''',
    'PartVI-L5-习题2.md': r'''
## 习题

**习题 1.1**。证明：光滑射影曲线 $X$ 上的线丛 $\\mathcal{L}$ 是丰富的当且仅当对任意凝聚层 $\\mathcal{F}$，$H^i(X,\\mathcal{F}\\otimes\\mathcal{L}^{\\otimes n})=0$ 对充分大的 $n$ 和 $i>0$ 成立。

*解答*：这是 Serre 消失定理，是丰富线丛的定义性质之一。$\square$

---

**习题 1.2**。计算 $\\mathbb{P}^2$ 上 $\\mathcal{O}(n)$ 的上同调群 $H^i(\\mathbb{P}^2,\\mathcal{O}(n))$ 对所有 $i,n$。

*解答*：$H^0=\\binom{n+2}{2}$（$n\\geq 0$），$H^1=0$（对所有 $n$），$H^2=H^0(\\mathcal{O}(-n-3))^\\vee$。$\square$
'''
}

def add_exercises(docs_dir, exercises):
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

add_exercises(r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.02-多变量微积分', e1802_alt)
add_exercises(r'G:\_src\FormalMath\docs\00-银层核心课程\Harvard-232br-代数几何', e232br)
add_exercises(r'G:\_src\FormalMath\docs\00-银层核心课程\Stanford-FOAG-基础代数几何', e_foag)
print('All done.')
