import os, re

docs_dir = r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.02-多元微积分'

# 每章习题模板
exercises = {
    'Ch01-向量与向量运算.md': '''
## 习题

**习题 1.1**。已知 $\\mathbf{a} = (1, 2, -1)$，$\\mathbf{b} = (3, 0, 2)$，计算：
(1) $\\mathbf{a} + 2\\mathbf{b}$；(2) $|\\mathbf{a}|$；(3) $\\mathbf{a}$ 方向的单位向量。

*解答*：
(1) $\\mathbf{a} + 2\\mathbf{b} = (1, 2, -1) + (6, 0, 4) = (7, 2, 3)$
(2) $|\\mathbf{a}| = \\sqrt{1^2 + 2^2 + (-1)^2} = \\sqrt{6}$
(3) $\\hat{\\mathbf{a}} = \\frac{1}{\\sqrt{6}}(1, 2, -1)$

---

**习题 1.2**。证明：对任意向量 $\\mathbf{u}, \\mathbf{v}, \\mathbf{w} \\in \\mathbb{R}^3$，有 $(\\mathbf{u} + \\mathbf{v}) + \\mathbf{w} = \\mathbf{u} + (\\mathbf{v} + \\mathbf{w})$。

*解答*：按分量计算：
$$((u_1+v_1)+w_1, (u_2+v_2)+w_2, (u_3+v_3)+w_3) = (u_1+(v_1+w_1), u_2+(v_2+w_2), u_3+(v_3+w_3))$$
由实数加法结合律即得。$\\square$

---

**习题 1.3**。求顶点为 $A(1,0,0)$, $B(0,2,0)$, $C(0,0,3)$ 的三角形的重心位置向量。

*解答*：重心 $G = \\frac{A+B+C}{3} = \\frac{1}{3}(1, 2, 3) = (\\frac{1}{3}, \\frac{2}{3}, 1)$。$\\square$
''',
    'Ch02-点积与叉积.md': '''
## 习题

**习题 2.1**。已知 $\\mathbf{a} = (1, 2, 3)$，$\\mathbf{b} = (4, 5, 6)$，求：
(1) $\\mathbf{a} \\cdot \\mathbf{b}$；(2) 两向量夹角；(3) $\\mathbf{a} \\times \\mathbf{b}$。

*解答*：
(1) $\\mathbf{a} \\cdot \\mathbf{b} = 4 + 10 + 18 = 32$
(2) $\\cos\\theta = \\frac{32}{\\sqrt{14}\\sqrt{77}} = \\frac{32}{\\sqrt{1078}} \\approx 0.975$，$\\theta \\approx 12.9°$
(3) $\\mathbf{a} \\times \\mathbf{b} = (12-15, 12-6, 5-8) = (-3, 6, -3)$

---

**习题 2.2**。求以 $A(1,0,0)$, $B(0,2,0)$, $C(0,0,3)$ 为顶点的三角形的面积。

*解答*：$\\overrightarrow{AB} = (-1, 2, 0)$，$\\overrightarrow{AC} = (-1, 0, 3)$。
$\\overrightarrow{AB} \\times \\overrightarrow{AC} = (6, 3, 2)$，面积 $= \\frac{1}{2}\\sqrt{36+9+4} = \\frac{7}{2}$。$\\square$

---

**习题 2.3**。证明 Lagrange 恒等式：$|\\mathbf{a} \\times \\mathbf{b}|^2 + (\\mathbf{a} \\cdot \\mathbf{b})^2 = |\\mathbf{a}|^2 |\\mathbf{b}|^2$。

*解答*：由 $|\\mathbf{a} \\times \\mathbf{b}| = |\\mathbf{a}||\\mathbf{b}|\\sin\\theta$ 和 $\\mathbf{a}\\cdot\\mathbf{b} = |\\mathbf{a}||\\mathbf{b}|\\cos\\theta$，
左边 $= |\\mathbf{a}|^2|\\mathbf{b}|^2(\\sin^2\\theta + \\cos^2\\theta) = |\\mathbf{a}|^2|\\mathbf{b}|^2$ = 右边。$\\square$
''',
    'Ch03-空间直线与平面.md': '''
## 习题

**习题 3.1**。求过点 $P(1, 2, 3)$ 且方向向量为 $\\mathbf{v} = (2, -1, 4)$ 的直线的参数方程和对称式方程。

*解答*：
参数方程：$x = 1 + 2t$, $y = 2 - t$, $z = 3 + 4t$
对称式：$\\frac{x-1}{2} = \\frac{y-2}{-1} = \\frac{z-3}{4}$。$\\square$

---

**习题 3.2**。求过三点 $A(1,0,0)$, $B(0,1,0)$, $C(0,0,1)$ 的平面方程。

*解答*：法向量 $\\mathbf{n} = \\overrightarrow{AB} \\times \\overrightarrow{AC} = (1, 1, 1)$。
平面方程：$x + y + z = 1$。$\\square$

---

**习题 3.3**。求点 $Q(2, 1, -1)$ 到平面 $2x - y + 2z + 3 = 0$ 的距离。

*解答*：$d = \\frac{|2(2) - 1(1) + 2(-1) + 3|}{\\sqrt{4+1+4}} = \\frac{|4-1-2+3|}{3} = \\frac{4}{3}$。$\\square$
''',
    'Ch04-多元函数与偏导数.md': '''
## 习题

**习题 4.1**。设 $f(x, y) = x^3 y^2 + 2xy^4$，求所有一阶和二阶偏导数。

*解答*：
$\\frac{\\partial f}{\\partial x} = 3x^2 y^2 + 2y^4$，$\\frac{\\partial f}{\\partial y} = 2x^3 y + 8xy^3$
$\\frac{\\partial^2 f}{\\partial x^2} = 6xy^2$，$\\frac{\\partial^2 f}{\\partial y^2} = 2x^3 + 24xy^2$
$\\frac{\\partial^2 f}{\\partial x \\partial y} = 6x^2 y + 8y^3 = \\frac{\\partial^2 f}{\\partial y \\partial x}$（验证Clairaut定理）。$\\square$

---

**习题 4.2**。求曲面 $z = x^2 + y^2$ 在点 $(1, 1, 2)$ 处的切平面方程。

*解答*：$\\frac{\\partial z}{\\partial x} = 2x = 2$，$\\frac{\\partial z}{\\partial y} = 2y = 2$。
切平面：$z - 2 = 2(x-1) + 2(y-1)$，即 $z = 2x + 2y - 2$。$\\square$

---

**习题 4.3**。设 $f(x,y) = \\frac{xy}{x^2+y^2}$（$(x,y) \\neq (0,0)$），$f(0,0)=0$。证明 $f$ 在 $(0,0)$ 处不连续，但两个偏导数均存在。

*解答*：沿 $y=kx$ 趋于原点，$f(x,kx) = \\frac{k}{1+k^2}$，极限依赖于 $k$，故不连续。
$f_x(0,0) = \\lim_{h\\to 0} \\frac{f(h,0)-f(0,0)}{h} = 0$，同理 $f_y(0,0)=0$。$\\square$
''',
    'Ch05-梯度与方向导数.md': '''
## 习题

**习题 5.1**。设 $f(x, y) = x^2 y + e^{xy}$，求在点 $(1, 0)$ 处的梯度，以及沿方向 $\\mathbf{u} = (\\frac{3}{5}, \\frac{4}{5})$ 的方向导数。

*解答*：$\\nabla f = (2xy + ye^{xy}, x^2 + xe^{xy})$，$\\nabla f(1,0) = (0, 2)$。
$D_{\\mathbf{u}} f = \\nabla f \\cdot \\mathbf{u} = 0 \\cdot \\frac{3}{5} + 2 \\cdot \\frac{4}{5} = \\frac{8}{5}$。$\\square$

---

**习题 5.2**。求函数 $f(x,y) = x^2 + xy + y^2$ 在点 $(1,1)$ 处方向导数的最大值及对应方向。

*解答*：$\\nabla f = (2x+y, x+2y)$，$\\nabla f(1,1) = (3, 3)$。
方向导数最大值 $= |\\nabla f| = \\sqrt{18} = 3\\sqrt{2}$，方向为 $\\frac{1}{\\sqrt{2}}(1, 1)$。$\\square$

---

**习题 5.3**。证明：若 $f$ 可微，则 $f$ 沿梯度方向增长最快，沿负梯度方向下降最快。

*解答*：$D_{\\mathbf{u}} f = \\nabla f \\cdot \\mathbf{u} = |\\nabla f||\\mathbf{u}|\\cos\\theta = |\\nabla f|\\cos\\theta$（$|\\mathbf{u}|=1$）。
当 $\\theta = 0$（即 $\\mathbf{u}$ 与 $\\nabla f$ 同向）时取最大值 $|\\nabla f|$；
当 $\\theta = \\pi$ 时取最小值 $-|\\nabla f|$。$\\square$
''',
    'Ch06-多元函数的极值.md': '''
## 习题

**习题 6.1**。求 $f(x, y) = x^3 + y^3 - 3xy$ 的所有临界点，并判断其类型。

*解答*：$f_x = 3x^2 - 3y = 0$，$f_y = 3y^2 - 3x = 0$。
临界点：$(0,0)$ 和 $(1,1)$。
$D = f_{xx}f_{yy} - f_{xy}^2 = (6x)(6y) - (-3)^2 = 36xy - 9$。
$D(0,0) = -9 < 0$，鞍点；$D(1,1) = 27 > 0$，$f_{xx}(1,1)=6>0$，局部极小值点。$\\square$

---

**习题 6.2**。求 $f(x,y) = x^2 + 2y^2$ 在约束 $x^2 + y^2 = 1$ 下的最大值和最小值。

*解答*：Lagrange函数 $L = x^2 + 2y^2 - \\lambda(x^2 + y^2 - 1)$。
$2x - 2\\lambda x = 0$，$4y - 2\\lambda y = 0$，$x^2 + y^2 = 1$。
解得：$(\\pm 1, 0)$ 对应 $f=1$（最小值）；$(0, \\pm 1)$ 对应 $f=2$（最大值）。$\\square$

---

**习题 6.3**。用 Lagrange 乘数法求原点到平面 $2x - y + 2z = 4$ 的最短距离。

*解答*：最小化 $f = x^2 + y^2 + z^2$ 约束 $g = 2x - y + 2z - 4 = 0$。
$2x = 2\\lambda$，$2y = -\\lambda$，$2z = 2\\lambda$ $\\Rightarrow$ $x = z = -2y$。
代入约束：$2(-2y) - y + 2(-2y) = 4$ $\\Rightarrow$ $y = -\\frac{4}{9}$，$x = z = \\frac{8}{9}$。
最短距离 $= \\sqrt{x^2+y^2+z^2} = \\frac{4}{3}$（与点到平面距离公式一致）。$\\square$
''',
    'Ch07-二重积分.md': '''
## 习题

**习题 7.1**。计算 $\\iint_R (x + y) \\, dA$，其中 $R = [0, 1] \\times [0, 2]$。

*解答*：$$\\int_0^1 \\int_0^2 (x+y) \\, dy \\, dx = \\int_0^1 \\left[xy + \\frac{y^2}{2}\\right]_0^2 dx = \\int_0^1 (2x + 2) \\, dx = 3$$$\\square$

---

**习题 7.2**。交换积分顺序：$\\int_0^1 \\int_{x^2}^1 f(x,y) \\, dy \\, dx$。

*解答*：积分区域：$0 \\leq x \\leq 1$，$x^2 \\leq y \\leq 1$。
交换后：$0 \\leq y \\leq 1$，$0 \\leq x \\leq \\sqrt{y}$。
$$\\int_0^1 \\int_0^{\\sqrt{y}} f(x,y) \\, dx \\, dy$$$\\square$

---

**习题 7.3**。用极坐标计算 $\\iint_D e^{-x^2-y^2} \\, dA$，其中 $D$ 为单位圆盘。

*解答*：$x = r\\cos\\theta$，$y = r\\sin\\theta$，$dA = r \\, dr \\, d\\theta$。
$$\\int_0^{2\\pi} \\int_0^1 e^{-r^2} r \\, dr \\, d\\theta = 2\\pi \\cdot \\left[-\\frac{1}{2}e^{-r^2}\\right]_0^1 = \\pi(1 - e^{-1})$$$\\square$
''',
    'Ch08-三重积分与坐标变换.md': '''
## 习题

**习题 8.1**。计算 $\\iiint_E (x + y + z) \\, dV$，其中 $E = [0,1] \\times [0,1] \\times [0,1]$。

*解答*：由对称性，$$\\iiint_E x \\, dV = \\iiint_E y \\, dV = \\iiint_E z \\, dV = \\int_0^1 x \\, dx = \\frac{1}{2}$$
所以原式 $= 3 \\cdot \\frac{1}{2} = \\frac{3}{2}$。$\\square$

---

**习题 8.2**。求半径为 $R$ 的球体的体积（用球坐标）。

*解答*：$dV = \\rho^2 \\sin\\phi \\, d\\rho \\, d\\phi \\, d\\theta$。
$$V = \\int_0^{2\\pi} \\int_0^{\\pi} \\int_0^R \\rho^2 \\sin\\phi \\, d\\rho \\, d\\phi \\, d\\theta = 2\\pi \\cdot 2 \\cdot \\frac{R^3}{3} = \\frac{4}{3}\\pi R^3$$$\\square$

---

**习题 8.3**。用柱坐标计算 $\\iiint_E z \\, dV$，其中 $E$ 为圆柱 $x^2 + y^2 \\leq 1$，$0 \\leq z \\leq 2$。

*解答*：$\\iiint_E z \\, dV = \\int_0^{2\\pi} \\int_0^1 \\int_0^2 z \\cdot r \\, dz \\, dr \\, d\\theta = 2\\pi \\cdot \\frac{1}{2} \\cdot 2 = 2\\pi$。$\\square$
''',
    'Ch09-曲线积分.md': '''
## 习题

**习题 9.1**。计算 $\\int_C (x + y) \\, ds$，其中 $C$ 为从 $(0,0)$ 到 $(1,1)$ 的直线段。

*解答*：参数化：$\\mathbf{r}(t) = (t, t)$，$0 \\leq t \\leq 1$。$|\\mathbf{r}'(t)| = \\sqrt{2}$。
$$\\int_0^1 (t + t)\\sqrt{2} \\, dt = 2\\sqrt{2} \\cdot \\frac{1}{2} = \\sqrt{2}$$ $\\square$

---

**习题 9.2**。判断 $\\mathbf{F} = (2xy, x^2)$ 是否为保守场。若是，求势函数。

*解答*：$\\frac{\\partial (2xy)}{\\partial y} = 2x = \\frac{\\partial (x^2)}{\\partial x}$，是保守场。
$\\phi_x = 2xy$ $\\Rightarrow$ $\\phi = x^2 y + g(y)$。
$\\phi_y = x^2 + g'(y) = x^2$ $\\Rightarrow$ $g'(y) = 0$。
势函数：$\\phi(x,y) = x^2 y + C$。$\\square$

---

**习题 9.3**。设 $\\mathbf{F} = (y, -x)$，计算沿单位圆（逆时针）的环量 $\\oint_C \\mathbf{F} \\cdot d\\mathbf{r}$。

*解答*：参数化：$\\mathbf{r}(t) = (\\cos t, \\sin t)$，$0 \\leq t \\leq 2\\pi$。
$\\mathbf{F}(\\mathbf{r}(t)) = (\\sin t, -\\cos t)$，$\\mathbf{r}'(t) = (-\\sin t, \\cos t)$。
$$\\oint_C \\mathbf{F} \\cdot d\\mathbf{r} = \\int_0^{2\\pi} (-\\sin^2 t - \\cos^2 t) \\, dt = -2\\pi$$$\\square$
''',
    'Ch10-Green-Stokes-散度定理.md': '''
## 习题

**习题 10.1**。用 Green 定理计算 $\\oint_C (x^2 - y) \\, dx + (y^2 + x) \\, dy$，其中 $C$ 为圆周 $x^2 + y^2 = 4$（逆时针）。

*解答*：$P = x^2 - y$，$Q = y^2 + x$。$\\frac{\\partial Q}{\\partial x} - \\frac{\\partial P}{\\partial y} = 1 - (-1) = 2$。
$$\\iint_D 2 \\, dA = 2 \\cdot \\pi \\cdot 2^2 = 8\\pi$$$\\square$

---

**习题 10.2**。用 Stokes 定理计算 $\\iint_S (\\nabla \\times \\mathbf{F}) \\cdot d\\mathbf{S}$，其中 $\\mathbf{F} = (y, z, x)$，$S$ 为上半球面 $x^2 + y^2 + z^2 = 1$，$z \\geq 0$（取上侧）。

*解答*：边界 $\\partial S$ 为 $xy$ 平面上的单位圆 $x^2 + y^2 = 1$（逆时针，从上方看）。
参数化：$\\mathbf{r}(t) = (\\cos t, \\sin t, 0)$。
$\\mathbf{F}(\\mathbf{r}(t)) = (\\sin t, 0, \\cos t)$，$\\mathbf{r}'(t) = (-\\sin t, \\cos t, 0)$。
$$\\oint_{\\partial S} \\mathbf{F} \\cdot d\\mathbf{r} = \\int_0^{2\\pi} (-\\sin^2 t) \\, dt = -\\pi$$$\\square$

---

**习题 10.3**。用散度定理计算 $\\iint_S \\mathbf{F} \\cdot d\\mathbf{S}$，其中 $\\mathbf{F} = (x, y, z)$，$S$ 为球面 $x^2 + y^2 + z^2 = R^2$（外侧）。

*解答*：$\\nabla \\cdot \\mathbf{F} = 1 + 1 + 1 = 3$。
$$\\iiint_B 3 \\, dV = 3 \\cdot \\frac{4}{3}\\pi R^3 = 4\\pi R^3$$$\\square$
'''
}

# 为每个文件追加习题
for fname, ex_content in exercises.items():
    fpath = os.path.join(docs_dir, fname)
    if not os.path.exists(fpath):
        print(f'MISSING: {fname}')
        continue
    with open(fpath, 'r', encoding='utf-8') as f:
        content = f.read()
    # 在参考文献之前插入习题
    marker = '**参考文献**'
    if marker in content:
        new_content = content.replace(marker, ex_content + '\n\n' + marker)
    else:
        new_content = content + '\n' + ex_content
    with open(fpath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    print(f'UPDATED: {fname}')

print('Done.')
