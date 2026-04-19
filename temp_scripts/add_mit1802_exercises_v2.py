import os

docs_dir = r'G:\_src\FormalMath\docs\03-分析学\01-实分析\MIT-18.100A'

exercises = {
    '01-确界原理与Archimedean性质.md': r'''
## 习题

**习题 1.1**。求集合 $S = \\{1/n : n \\in \\mathbb{N}\\}$ 的上确界和下确界。

*解答*：$\\sup S = 1$（最大元），$\\inf S = 0$（0是下界，且对任意 $\\epsilon > 0$，存在 $n$ 使 $1/n < \\epsilon$）。$\\square$

---

**习题 1.2**。用 Archimedean 性质证明 $\\mathbb{Q}$ 在 $\\mathbb{R}$ 中稠密。

*解答*：对任意 $a < b$，需找有理数 $q \\in (a,b)$。由 Archimedean 性质，存在 $n$ 使 $1/n < b-a$。再取 $m = \\lfloor na \\rfloor + 1$，则 $a < m/n < b$。$\\square$
''',
    '02-介值定理.md': r'''
## 习题

**习题 1.1**。证明：奇数次实系数多项式至少有一个实根。

*解答*：设 $p(x) = a_n x^n + \\cdots + a_0$，$n$ 奇数。当 $x \\to +\\infty$，$p(x) \\to \\operatorname{sgn}(a_n)\\infty$；当 $x \\to -\\infty$，$p(x) \\to -\\operatorname{sgn}(a_n)\\infty$。故 $p$ 变号，由介值定理存在根。$\\square$

---

**习题 1.2**。设 $f:[0,1]\\to[0,1]$ 连续且 $f(0)=0, f(1)=1$。证明存在 $c$ 使 $f(c)=c^2$。

*解答*：令 $g(x) = f(x) - x^2$，则 $g(0)=0, g(1)=0$。若 $g\\equiv 0$ 则结论显然；否则存在 $x_0$ 使 $g(x_0)\\neq 0$，由介值定理在 $(0,1)$ 内存在零点。$\\square$
''',
    '03-一致连续性.md': r'''
## 习题

**习题 1.1**。证明 $f(x) = \\sqrt{x}$ 在 $[0,\\infty)$ 上一致连续。

*解答*：$|\\sqrt{x}-\\sqrt{y}| = \\frac{|x-y|}{\\sqrt{x}+\\sqrt{y}} \\leq \\sqrt{|x-y|}$（当 $x,y \\geq 0$）。取 $\\delta = \\epsilon^2$ 即可。$\\square$

---

**习题 1.2**。设 $f$ 在 $\\mathbb{R}$ 上可微且 $|f'(x)| \\leq M$。证明 $f$ 一致连续。

*解答*：由中值定理 $|f(x)-f(y)| = |f'(c)||x-y| \\leq M|x-y|$。取 $\\delta = \\epsilon/M$。$\\square$
''',
    '04-中值定理.md': r'''
## 习题

**习题 1.1**。证明 $|\\arctan x - \\arctan y| \\leq |x-y|$ 对所有 $x,y\\in\\mathbb{R}$。

*解答*：$(\\arctan x)' = \\frac{1}{1+x^2} \\leq 1$。由中值定理 $|\\arctan x - \\arctan y| = \\frac{1}{1+c^2}|x-y| \\leq |x-y|$。$\\square$

---

**习题 1.2**。设 $f$ 在 $[a,b]$ 上二阶可微，$f(a)=f(b)=0$，且存在 $c\\in(a,b)$ 使 $f(c)>0$。证明存在 $\\xi\\in(a,b)$ 使 $f''(\\xi)<0$。

*解答*：由中值定理，存在 $\\eta_1\\in(a,c)$ 使 $f'(\\eta_1) = \\frac{f(c)}{c-a} > 0$；存在 $\\eta_2\\in(c,b)$ 使 $f'(\\eta_2) = \\frac{-f(c)}{b-c} < 0$。再对 $f'$ 在 $[\\eta_1,\\eta_2]$ 上用中值定理，存在 $\\xi$ 使 $f''(\\xi) = \\frac{f'(\\eta_2)-f'(\\eta_1)}{\\eta_2-\\eta_1} < 0$。$\\square$
''',
    '05-比较判别法与比值根值判别法.md': r'''
## 习题

**习题 1.1**。判断 $\\sum_{n=1}^{\\infty} \\frac{n+1}{n^3+2}$ 的收敛性。

*解答*：$\\frac{n+1}{n^3+2} \\sim \\frac{1}{n^2}$，由比较判别法（极限形式），级数收敛。$\\square$

---

**习题 1.2**。用根值判别法判断 $\\sum_{n=1}^{\\infty} \\left(\\frac{2n+1}{3n+2}\\right)^n$ 的收敛性。

*解答*：$\\sqrt[n]{a_n} = \\frac{2n+1}{3n+2} \\to \\frac{2}{3} < 1$，故收敛。$\\square$
''',
    '06-Taylor定理.md': r'''
## 习题

**习题 1.1**。写出 $f(x) = \\ln(1+x)$ 在 $x=0$ 处的 Taylor 级数，并确定收敛半径。

*解答*：$\\ln(1+x) = x - \\frac{x^2}{2} + \\frac{x^3}{3} - \\cdots = \\sum_{n=1}^{\\infty} \\frac{(-1)^{n-1}x^n}{n}$。由比值判别法，收敛半径 $R=1$。$\\square$

---

**习题 1.2**。用 Taylor 展开估计 $\\sqrt{e}$ 的误差小于 $0.001$ 所需的最小阶数。

*解答*：$e^x = 1 + x + \\frac{x^2}{2!} + \\cdots$。在 $x=1/2$ 处，余项 $R_n = \\frac{e^c}{(n+1)!}(1/2)^{n+1} \\leq \\frac{e}{(n+1)!2^{n+1}}$。$n=4$ 时 $R_4 < 0.001$。$\\square$
''',
    '07-Weierstrass-M-判别法.md': r'''
## 习题

**习题 1.1**。判断 $\\sum_{n=1}^{\\infty} \\frac{\\cos(nx)}{n^2+1}$ 在 $\\mathbb{R}$ 上的一致收敛性。

*解答*：$\\left|\\frac{\\cos(nx)}{n^2+1}\\right| \\leq \\frac{1}{n^2+1} < \\frac{1}{n^2}$。$\\sum \\frac{1}{n^2}$ 收敛，故由 M-判别法一致收敛。$\\square$

---

**习题 1.2**。设 $\\sum M_n$ 收敛且 $|f_n(x)| \\leq M_n$ 对所有 $x$。证明 $\\sum f_n$ 绝对收敛且一致收敛。

*解答*：绝对收敛由比较判别法；一致收敛由 M-判别法（即 Weierstrass M-判别法）。$\\square$
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
