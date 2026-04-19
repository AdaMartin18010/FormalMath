import os, re

# MIT 18.100A exercises
e1802 = {
    'Taylor定理.md': '''
## 习题

**习题 1.1**。求 $f(x) = e^x$ 在 $x=0$ 处的三阶 Taylor 多项式，并估计在 $x=1$ 处的余项上界。

*解答*：$f^{(n)}(x) = e^x$，故 $f^{(n)}(0)=1$。
$$P_3(x) = 1 + x + \frac{x^2}{2} + \frac{x^3}{6}$$
余项 $R_3(x) = \frac{e^c}{24}x^4$，$c\in(0,1)$，$|R_3(1)| \leq \frac{e}{24} \approx 0.113$。$\square$

---

**习题 1.2**。用 Taylor 展开证明 $\lim_{x\to 0}\frac{\sin x - x}{x^3} = -\frac{1}{6}$。

*解答*：$\sin x = x - \frac{x^3}{6} + O(x^5)$，故 $\sin x - x = -\frac{x^3}{6} + O(x^5)$。
$$\frac{\sin x - x}{x^3} = -\frac{1}{6} + O(x^2) \to -\frac{1}{6}$$$\square$
''',
    'Weierstrass-M判别法.md': '''
## 习题

**习题 1.1**。判断级数 $\sum_{n=1}^{\infty} \frac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上是否一致收敛。

*解答*：$\left|\frac{\sin(nx)}{n^2}\right| \leq \frac{1}{n^2} = M_n$。$\sum M_n$ 收敛（p-级数，p=2>1）。由 Weierstrass M-判别法，原级数在 $\mathbb{R}$ 上一致收敛。$\square$

---

**习题 1.2**。举例说明：$\sum f_n$ 一致收敛不能推出 $\sum |f_n|$ 一致收敛。

*解答*：取 $f_n(x) = \frac{(-1)^n}{n}$（常数函数）。$\sum f_n$ 在 $\mathbb{R}$ 上一致收敛（交错级数），但 $\sum |f_n| = \sum \frac{1}{n}$ 发散。$\square$
''',
    '比较判别法.md': '''
## 习题

**习题 1.1**。判断 $\sum_{n=1}^{\infty} \frac{1}{n^2+1}$ 的收敛性。

*解答*：$\frac{1}{n^2+1} < \frac{1}{n^2}$，而 $\sum \frac{1}{n^2}$ 收敛。由比较判别法，原级数收敛。$\square$

---

**习题 1.2**。设 $a_n > 0$ 且 $\lim_{n\to\infty} n a_n = L > 0$。证明 $\sum a_n$ 发散。

*解答*：由极限比较判别法，$\lim \frac{a_n}{1/n} = L > 0$。因 $\sum \frac{1}{n}$ 发散，故 $\sum a_n$ 发散。$\square$
''',
    '比值根值判别法.md': '''
## 习题

**习题 1.1**。用比值判别法判断 $\sum_{n=1}^{\infty} \frac{n!}{n^n}$ 的收敛性。

*解答*：$$\frac{a_{n+1}}{a_n} = \frac{(n+1)!}{(n+1)^{n+1}} \cdot \frac{n^n}{n!} = \frac{n+1}{(n+1)^{n+1}} \cdot n^n = \left(\frac{n}{n+1}\right)^n = \frac{1}{(1+1/n)^n} \to \frac{1}{e} < 1$$
故级数收敛。$\square$

---

**习题 1.2**。用根值判别法判断 $\sum_{n=1}^{\infty} \left(\frac{n}{2n+1}\right)^n$ 的收敛性。

*解答*：$$\sqrt[n]{a_n} = \frac{n}{2n+1} \to \frac{1}{2} < 1$$
故级数收敛。$\square$
''',
    '介值定理.md': '''
## 习题

**习题 1.1**。证明方程 $x^3 - 2x - 5 = 0$ 在 $(2, 3)$ 内至少有一个根。

*解答*：$f(x) = x^3 - 2x - 5$ 在 $[2,3]$ 上连续。$f(2) = -1 < 0$，$f(3) = 16 > 0$。由介值定理，存在 $c\in(2,3)$ 使 $f(c)=0$。$\square$

---

**习题 1.2**。设 $f:[0,1]\to[0,1]$ 连续。证明存在 $c\in[0,1]$ 使 $f(c)=c$。

*解答*：令 $g(x) = f(x) - x$，则 $g$ 连续。$g(0) = f(0) \geq 0$，$g(1) = f(1)-1 \leq 0$。由介值定理，存在 $c$ 使 $g(c)=0$，即 $f(c)=c$。$\square$
''',
    '确界原理与Archimedean性质.md': '''
## 习题

**习题 1.1**。求集合 $S = \{x\in\mathbb{Q}: x^2 < 2\}$ 在 $\mathbb{R}$ 中的上确界。

*解答*：$S$ 的上界为 $\sqrt{2}$（在 $\mathbb{R}$ 中）。对任意 $\epsilon > 0$，由有理数的稠密性，存在有理数 $q$ 使 $\sqrt{2}-\epsilon < q < \sqrt{2}$，且 $q^2 < 2$（取足够接近 $\sqrt{2}$ 的有理数）。故 $\sup S = \sqrt{2}$。$\square$

---

**习题 1.2**。用 Archimedean 性质证明：对任意 $x > 0$，存在 $n\in\mathbb{N}$ 使 $\frac{1}{n} < x$。

*解答*：由 Archimedean 性质，取 $y = 1$，存在 $n\in\mathbb{N}$ 使 $nx > 1$（因 $x > 0$），即 $\frac{1}{n} < x$。$\square$
''',
    '一致连续性定理.md': '''
## 习题

**习题 1.1**。证明 $f(x) = x^2$ 在 $[0,1]$ 上一致连续，但在 $\mathbb{R}$ 上不一致连续。

*解答*：在 $[0,1]$ 上，$|f(x)-f(y)| = |x+y||x-y| \leq 2|x-y|$，故取 $\delta = \epsilon/2$ 即可。
在 $\mathbb{R}$ 上，取 $x_n = n+\frac{1}{n}$，$y_n = n$，则 $|x_n-y_n| = \frac{1}{n} \to 0$，但 $|f(x_n)-f(y_n)| = 2 + \frac{1}{n^2} \to 2 \neq 0$。$\square$

---

**习题 1.2**。设 $f$ 在 $[a,b]$ 上连续。用 Cantor 定理证明 $f$ 在 $[a,b]$ 上一致连续。

*解答*：Cantor 定理：闭区间上的连续函数必一致连续。证明要点：对每点 $x$ 取 $\delta_x$ 邻域，用有限覆盖定理提取有限子覆盖，取最小 $\delta$。$\square$
''',
    '中值定理.md': '''
## 习题

**习题 1.1**。用中值定理证明 $|\sin x - \sin y| \leq |x-y|$ 对所有 $x,y\in\mathbb{R}$ 成立。

*解答*：由中值定理，$\sin x - \sin y = \cos c \cdot (x-y)$（$c$ 在 $x,y$ 之间）。$|\cos c| \leq 1$，故 $|\sin x - \sin y| \leq |x-y|$。$\square$

---

**习题 1.2**。设 $f$ 在 $[a,b]$ 上可微且 $f'(x) = 0$ 对所有 $x\in(a,b)$。证明 $f$ 在 $[a,b]$ 上为常数。

*解答*：对任意 $x_1 < x_2$ 于 $[a,b]$，由中值定理 $f(x_2)-f(x_1) = f'(c)(x_2-x_1) = 0$。故 $f(x_1)=f(x_2)$，$f$ 为常数。$\square$
'''
}

# MIT 18.06 exercises
e1806 = {
    'Ch01-线性方程组的几何.md': '''
## 习题

**习题 1.1**。求下列方程组的解（几何上解释）：$x + y = 2$，$2x + 2y = 4$。

*解答*：两方程表示同一直线，解集为直线 $x+y=2$ 上的所有点，无穷多解。$\square$

---

**习题 1.2**。判断方程组 $x + y = 1$，$x + y = 2$ 是否有解，并从几何上解释。

*解答*：两直线平行（斜率均为 $-1$）且不重合，无交点，故无解。$\square$
''',
    'Ch02-矩阵消元法.md': '''
## 习题

**习题 1.1**。用高斯消元法求解：$2x + y - z = 8$，$-3x - y + 2z = -11$，$-2x + y + 2z = -3$。

*解答*：增广矩阵经消元得阶梯形，回代得 $x=2, y=3, z=-1$。$\square$

---

**习题 1.2**。判断矩阵 $A = \begin{pmatrix} 1 & 2 & 1 \\ 2 & 4 & 2 \\ 1 & 2 & 3 \end{pmatrix}$ 的秩，并求其行最简形。

*解答*：行2 = 2×行1，消元后得秩为2。$\square$
''',
    'Ch03-矩阵运算与逆矩阵.md': '''
## 习题

**习题 1.1**。求 $A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ 的逆矩阵（若存在）。

*解答*：$\det A = -2 \neq 0$，逆存在。$A^{-1} = -\frac{1}{2}\begin{pmatrix} 4 & -2 \\ -3 & 1 \end{pmatrix} = \begin{pmatrix} -2 & 1 \\ 3/2 & -1/2 \end{pmatrix}$。$\square$

---

**习题 1.2**。证明：若 $A,B$ 均可逆，则 $(AB)^{-1} = B^{-1}A^{-1}$。

*解答*：$(AB)(B^{-1}A^{-1}) = A(BB^{-1})A^{-1} = AIA^{-1} = AA^{-1} = I$。$\square$
''',
    'Ch04-LU分解.md': '''
## 习题

**习题 1.1**。求 $A = \begin{pmatrix} 2 & 1 \\ 4 & 3 \end{pmatrix}$ 的 LU 分解（不带行交换）。

*解答*：$l_{21} = 4/2 = 2$。$U = \begin{pmatrix} 2 & 1 \\ 0 & 1 \end{pmatrix}$，$L = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix}$。$\square$

---

**习题 1.2**。说明为什么 $A = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ 没有不带行交换的 LU 分解。

*解答*：$a_{11}=0$，无法作为主元进行消元，必须先进行行交换。$\square$
''',
    'Ch05-向量空间与子空间.md': '''
## 习题

**习题 1.1**。判断 $W = \{(x,y,z)\in\mathbb{R}^3: x+y+z=0\}$ 是否为 $\mathbb{R}^3$ 的子空间。

*解答*：是。零向量在 $W$ 中；对加法封闭：若 $x+y+z=0$ 且 $x'+y'+z'=0$，则 $(x+x')+(y+y')+(z+z')=0$；对数乘封闭。$\square$

---

**习题 1.2**。求 $W = \operatorname{span}\{(1,2,3), (2,4,6)\}$ 的维数。

*解答*：$(2,4,6) = 2(1,2,3)$，两向量线性相关。基可取 $\{(1,2,3)\}$，维数为1。$\square$
''',
    'Ch06-列空间与零空间.md': '''
## 习题

**习题 1.1**。设 $A = \begin{pmatrix} 1 & 2 & 3 \\ 2 & 4 & 5 \end{pmatrix}$。求 $C(A)$ 和 $N(A)$ 的维数。

*解答*：$\operatorname{rank}(A) = 2$（前两列线性无关），故 $\dim C(A) = 2$。由秩-零化度定理，$\dim N(A) = 3 - 2 = 1$。$\square$

---

**习题 1.2**。证明 $N(A) = N(R)$，其中 $R$ 是 $A$ 的行最简形。

*解答*：行变换等价于左乘可逆矩阵，不改变解集。$\square$
''',
    'Ch07-求解线性方程组.md': '''
## 习题

**习题 1.1**。求 $Ax = b$ 的通解，其中 $A = \begin{pmatrix} 1 & 2 & 3 \\ 2 & 4 & 6 \end{pmatrix}$，$b = \begin{pmatrix} 6 \\ 12 \end{pmatrix}$。

*解答*：行最简形为 $\begin{pmatrix} 1 & 2 & 3 \\ 0 & 0 & 0 \end{pmatrix}$。特解 $x_p = (6,0,0)^T$。零空间基：$(-2,1,0)^T, (-3,0,1)^T$。通解 $x = x_p + c_1(-2,1,0)^T + c_2(-3,0,1)^T$。$\square$

---

**习题 1.2**。判断 $Ax = b$ 是否有解，其中 $A = \begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}$，$b = \begin{pmatrix} 3 \\ 7 \end{pmatrix}$。

*解答*：$b$ 不在 $C(A)$ 中（$C(A)$ 是直线 $y=2x$，而 $(3,7)$ 不满足），故无解。$\square$
''',
    'Ch08-线性无关基与维数.md': '''
## 习题

**习题 1.1**。判断 $\{(1,0,1), (0,1,1), (1,1,0)\}$ 是否为 $\mathbb{R}^3$ 的一组基。

*解答*：计算行列式 $\begin{vmatrix} 1&0&1\\0&1&1\\1&1&0 \end{vmatrix} = -2 \neq 0$，故三向量线性无关，构成基。$\square$

---

**习题 1.2**。证明：若 $v_1, v_2, v_3$ 线性无关，则 $v_1+v_2, v_2+v_3, v_3+v_1$ 也线性无关。

*解答*：设 $a(v_1+v_2)+b(v_2+v_3)+c(v_3+v_1)=0$，则 $(a+c)v_1+(a+b)v_2+(b+c)v_3=0$。由线性无关得 $a+c=a+b=b+c=0$，解得 $a=b=c=0$。$\square$
''',
    'Ch09-四大基本子空间.md': '''
## 习题

**习题 1.1**。设 $A$ 为 $m\times n$ 矩阵。证明 $\dim C(A) + \dim N(A) = n$。

*解答*：这就是秩-零化度定理。$\operatorname{rank}(A) = \dim C(A)$，$\dim N(A) = n - \operatorname{rank}(A)$。$\square$

---

**习题 1.2**。设 $A$ 为 $3\times 3$ 可逆矩阵。描述其四个基本子空间。

*解答*：$C(A) = \mathbb{R}^3$，$N(A) = \{0\}$；$C(A^T) = \mathbb{R}^3$，$N(A^T) = \{0\}$。$\square$
''',
    'Ch10-正交性与投影.md': '''
## 习题

**习题 1.1**。求向量 $v = (1,2,3)$ 在 $w = (1,1,1)$ 上的正交投影。

*解答*：$\hat{v} = \frac{v\cdot w}{w\cdot w} w = \frac{6}{3}(1,1,1) = (2,2,2)$。$\square$

---

**习题 1.2**。证明：若 $P$ 是到子空间 $S$ 的正交投影矩阵，则 $P^2 = P$ 且 $P^T = P$。

*解答*：$P^2=P$：投影两次等于投影一次。$P^T=P$：正交投影矩阵对称（由 $P = A(A^TA)^{-1}A^T$ 可直接验证）。$\square$
''',
    'Ch11-最小二乘与Gram-Schmidt.md': '''
## 习题

**习题 1.1**。求数据点 $(1,2), (2,3), (3,5)$ 的最小二乘拟合直线 $y = ax + b$。

*解答*：$A = \begin{pmatrix} 1&1\\2&1\\3&1 \end{pmatrix}$，$b = \begin{pmatrix} 2\\3\\5 \end{pmatrix}$。解正规方程 $A^TA\hat{x}=A^Tb$ 得 $a=1.5, b=0.33$。$\square$

---

**习题 1.2**。对 $v_1=(1,0,0), v_2=(1,1,0), v_3=(1,1,1)$ 应用 Gram-Schmidt 正交化。

*解答*：$u_1=v_1=(1,0,0)$；$u_2=v_2-\frac{v_2\cdot u_1}{u_1\cdot u_1}u_1=(0,1,0)$；$u_3=v_3-\frac{v_3\cdot u_1}{u_1\cdot u_1}u_1-\frac{v_3\cdot u_2}{u_2\cdot u_2}u_2=(0,0,1)$。$\square$
''',
    'Ch12-行列式.md': '''
## 习题

**习题 1.1**。计算 $\begin{vmatrix} 1 & 2 & 3 \\ 0 & 4 & 5 \\ 0 & 0 & 6 \end{vmatrix}$。

*解答*：上三角矩阵，行列式等于对角线元素乘积：$1\times 4\times 6 = 24$。$\square$

---

**习题 1.2**。证明：若 $A$ 的两行相同，则 $\det A = 0$。

*解答*：交换相同两行，行列式变号：$\det A = -\det A$，故 $\det A = 0$。$\square$
''',
    'Ch13-特征值与特征向量.md': '''
## 习题

**习题 1.1**。求 $A = \begin{pmatrix} 4 & 2 \\ 1 & 3 \end{pmatrix}$ 的特征值和特征向量。

*解答*：特征方程 $\det(A-\lambda I) = (4-\lambda)(3-\lambda)-2 = \lambda^2-7\lambda+10 = (\lambda-5)(\lambda-2)=0$。$\lambda_1=5$，特征向量 $(2,1)^T$；$\lambda_2=2$，特征向量 $(1,-1)^T$。$\square$

---

**习题 1.2**。证明：若 $\lambda$ 是 $A$ 的特征值，则 $\lambda^2$ 是 $A^2$ 的特征值。

*解答*：$Av = \lambda v$，则 $A^2v = A(\lambda v) = \lambda Av = \lambda^2 v$。$\square$
''',
    'Ch14-对角化与对称矩阵.md': '''
## 习题

**习题 1.1**。判断 $A = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ 是否可对角化。

*解答*：特征值 $\lambda=1$（二重）。$A-I = \begin{pmatrix} 0&2\\0&0 \end{pmatrix}$，零空间维数为1 < 2，几何重数 < 代数重数，不可对角化。$\square$

---

**习题 1.2**。设 $A$ 为实对称矩阵。证明其特征值均为实数，且不同特征值对应的特征向量正交。

*解答*：$\lambda\|v\|^2 = \lambda v^*v = v^*Av = (Av)^*v = \bar{\lambda}v^*v = \bar{\lambda}\|v\|^2$，故 $\lambda=\bar{\lambda}$。正交性：$\lambda_1 v_2^Tv_1 = v_2^TAv_1 = (Av_2)^Tv_1 = \lambda_2 v_2^Tv_1$，故 $(\lambda_1-\lambda_2)v_2^Tv_1=0$。$\square$
''',
    'Ch15-SVD与线性变换.md': '''
## 习题

**习题 1.1**。求 $A = \begin{pmatrix} 3 & 0 \\ 0 & -2 \end{pmatrix}$ 的 SVD。

*解答*：$A^TA = \begin{pmatrix} 9&0\\0&4 \end{pmatrix}$，奇异值 $\sigma_1=3, \sigma_2=2$。$V=I$，$U = \begin{pmatrix} 1&0\\0&-1 \end{pmatrix}$。$A = U\Sigma V^T$。$\square$

---

**习题 1.2**。证明：任意 $m\times n$ 矩阵 $A$ 的伪逆 $A^+$ 满足 $AA^+A = A$。

*解答*：由 SVD $A=U\Sigma V^T$，$A^+=V\Sigma^+U^T$。$AA^+A = U\Sigma V^T V\Sigma^+U^T U\Sigma V^T = U\Sigma\Sigma^+\Sigma V^T = U\Sigma V^T = A$。$\square$
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

add_exercises(r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.100A-实分析', e1802)
add_exercises(r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.06-线性代数', e1806)
print('Done.')
