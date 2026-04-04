---
msc_primary: "00A99"
---
msc_primary: "00A99"
---

# LaTeX数学排版速查

## 一、公式环境

### 1.1 行内公式

```latex
% 行内公式使用 $...$
The quadratic formula $x = \frac{-b \pm \sqrt{b^2-4ac}}{2a}$ 
gives the roots.

% 使用 \(...\) 也可以（推荐）
The value is \( \pi \approx 3.14159 \).

```

### 1.2 显示公式

```latex
% 无编号
\[ E = mc^2 \]

% 或
\begin{equation*}
  E = mc^2
\end{equation*}

% 自动编号
\begin{equation}\label{eq:emc}
  E = mc^2
\end{equation}

% 引用
Equation \eqref{eq:emc} states that ...

```

### 1.3 多行公式

```latex
% align 环境（推荐）
\begin{align}
  (a+b)^2 &= a^2 + 2ab + b^2 \\
          &= a^2 + b^2 + 2ab.
\end{align}

% 多行对齐
\begin{align}
  f(x) &= x^2 + 1 \\
  g(x) &= \sin(x) \\
  h(x) &= e^x
\end{align}

% 单编号多行
\begin{aligned}
  (a+b)^2 &= a^2 + 2ab + b^2 \\
          &= a^2 + b^2 + 2ab.
\end{aligned}

% gather（每行单独居中）
\begin{gather}
  a = b + c \\
  d = e + f \\
  g = h + i
\end{gather}

```

### 1.4 长公式换行

```latex
% multline（第一行左对齐，最后一行右对齐，中间居中）
\begin{multline}
  a + b + c + d + e + f + g + h + i + j + k + l + m \\
  = n + o + p + q + r + s + t + u + v + w + x + y + z
\end{multline}

% split（在equation内使用）
\begin{equation}
  \begin{split}
    (a+b)^2 &= a^2 + 2ab + b^2 \\
            &= a^2 + b^2 + 2ab.
  \end{split}
\end{equation}

```

## 二、上下标与根号

### 2.1 上标和下标

```latex
% 上标
x^2, e^{x+y}, a^{b^{c}}

% 下标
x_i, x_{ij}, a_{i_{j}}

% 同时上下标
\sum_{i=1}^{n}, \int_{a}^{b}, \prod_{i=1}^{n}

% 在右侧的上下标（积分）
\int\limits_{a}^{b}, \sum\limits_{i=1}^{n}

% 多重下标
x_{i_{j_{k}}}

% 文本下标（如max, min）
\max_{x \in X}, \min_{y \in Y}, \sup_{n \geq 1}

```

### 2.2 根号

```latex
% 平方根
\sqrt{x}, \sqrt{x+y}, \sqrt{\frac{a}{b}}

% n次方根
\sqrt[3]{x}, \sqrt[n]{x}

% 复杂根号
\sqrt{\frac{x^2 + y^2}{z^2}}

```

## 三、分数与二项式

### 3.1 分数

```latex
% 标准分数
\frac{a}{b}, \frac{x+y}{x-y}, \frac{\frac{a}{b}}{\frac{c}{d}}

% 行内分数（更小）
$\tfrac{a}{b}$

% 连分数
\cfrac{1}{1 + \cfrac{1}{1 + \cfrac{1}{1}}}

% 斜线分数（行内推荐）
$a/b$, $(x+y)/(x-y)$

```

### 3.2 二项式系数

```latex
\binom{n}{k}, \binom{n+1}{k+1}, \dbinom{n}{k}  % 显示样式
\tbinom{n}{k}  % 文本样式

```

## 四、运算符与求和积分

### 4.1 求和与乘积

```latex
% 求和
\sum_{i=1}^{n} a_i

% 乘积
\prod_{i=1}^{n} a_i

% 余积
\coprod_{i=1}^{n} A_i

% 并集与交集（大）
\bigcup_{i=1}^{n} A_i, \bigcap_{i=1}^{n} A_i

% 极限
\lim_{x \to 0} \frac{\sin x}{x}
\lim_{n \to \infty} a_n

```

### 4.2 积分

```latex
% 不定积分
\int f(x) \, dx

% 定积分
\int_{a}^{b} f(x) \, dx

% 多重积分
\iint_D f(x,y) \, dx\,dy
\iiint_V f(x,y,z) \, dx\,dy\,dz
\idotsint f \, dx_1 \dots dx_n

% 围道积分
\oint_C f(z) \, dz

% 积分限在右侧
\int\limits_{-\infty}^{\infty}

```

**注意**：积分微分前加 `\,` 以保持适当间距

### 4.3 其他运算符

```latex
% 偏微分
\partial

% nabla算子
\nabla f, \nabla \cdot \mathbf{F}, \nabla \times \mathbf{F}

% 增量
\Delta x, \delta x

% 梯度
\grad f  % (需宏包)

% 散度和旋度
\divergence \mathbf{F}, \curl \mathbf{F}

```

## 五、括号与定界符

### 5.1 自动调整大小

```latex
% 自动调整
\left( \frac{x}{y} \right), \left[ \frac{x}{y} \right]
\left\{ \frac{x}{y} \right\}, \left| \frac{x}{y} \right|
\left\| \frac{x}{y} \right\|, \left\langle \frac{x}{y} \right\rangle

% 单侧
\left. \frac{x}{y} \right\}

% 高度调整（不推荐自动调整过大）
\bigl( \bigr), \Bigl( \Bigr), \biggl( \biggr), \Biggl( \Biggr)

```

### 5.2 手动指定大小

```latex
\bigl( \bigr)      % 稍大
\Bigl( \Bigr)      % 更大
\biggl( \biggr)    % 更大
\Biggl( \Biggr)    % 最大

```

### 5.3 绝对值与范数

```latex

|x|, \lvert x \rvert, \left| \frac{x}{y} \right|
\|x\|, \lVert x \rVert, \left\| \frac{x}{y} \right\|

```

### 5.4 取整函数

```latex
\lfloor x \rfloor  % 下取整
\lceil x \rceil    % 上取整
\langle x \rangle   % 尖括号

```

## 六、矩阵与数组

### 6.1 矩阵环境

```latex
% 圆括号矩阵
\begin{pmatrix}
  a & b \\
  c & d
\end{pmatrix}

% 方括号矩阵
\begin{bmatrix}
  a & b \\
  c & d
\end{bmatrix}

% 行列式
\begin{vmatrix}
  a & b \\
  c & d
\end{vmatrix}

% 双竖线（范数）
\begin{Vmatrix}
  a & b \\
  c & d
\end{Vmatrix}

% 花括号
\begin{Bmatrix}
  a & b \\
  c & d
\end{Bmatrix}

% 无括号（需手动添加）
\begin{matrix}
  a & b \\
  c & d
\end{matrix}

```

### 6.2 大型矩阵

```latex
\begin{pmatrix}
  a_{11} & a_{12} & \cdots & a_{1n} \\
  a_{21} & a_{22} & \cdots & a_{2n} \\
  \vdots & \vdots & \ddots & \vdots \\
  a_{m1} & a_{m2} & \cdots & a_{mn}
\end{pmatrix}

```

### 6.3 分块矩阵

```latex
\left(
  \begin{array}{c|c}

    A & B \\
    \hline
    C & D
  \end{array}
\right)

```

### 6.4 数组环境

```latex
\begin{array}{rcl}
  a & = & b + c \\
  x & = & y - z
\end{array}

```

## 七、省略号与修饰符

### 7.1 省略号

```latex
% 水平省略号
\ldots  % 底部对齐（用于逗号后）
\cdots  % 居中（用于运算符间）

% 垂直和对角
\vdots  % 垂直
\ddots  % 对角

% 使用示例
a_1, a_2, \ldots, a_n
a_1 + a_2 + \cdots + a_n
\begin{pmatrix} a_{11} & \cdots \\ \vdots & \ddots \end{pmatrix}

```

### 7.2 上下修饰符

```latex
% 上划线
\bar{x}, \overline{AB}, \overline{x+y}

% 下划线
\underline{x}, \underline{AB}

% 向量箭头
\vec{x}, \overrightarrow{AB}

% 帽子
\hat{x}, \widehat{xyz}

% 波浪线
\tilde{x}, \widetilde{xyz}

% 点（导数）
\dot{x}, \ddot{x}, \dddot{x}

% 箭头
\overleftarrow{AB}, \overrightarrow{AB}, \overleftrightarrow{AB}

```

## 八、文本与标注

### 8.1 公式中的文本

```latex
% 使用 \text（需amsmath）
f(x) = \begin{cases}
  1 & \text{if } x \in \mathbb{Q} \\
  0 & \text{if } x \notin \mathbb{Q}
\end{cases}

% 罗马体函数名
\mathrm{Hom}, \operatorname{rank}, \operatorname{tr}

```

### 8.2 标注上下标

```latex
% 上标标注
x^{\text{max}}, A^{\mathrm{T}}

% 下标标注
x_{\text{initial}}, f_{\mathrm{max}}

```

### 8.3 堆叠符号

```latex
% 上堆叠
\stackrel{f}{\longrightarrow}

% 下堆叠
\underset{x \to 0}{\lim}

% 上下同时
\overset{a}{\underset{b}{=}}

% 更好的上下标（数学）
\lim_{x \to 0}, \sum_{i=1}^{n}

```

## 九、字体样式

### 9.1 数学字体

```latex
\mathbb{R}    % 黑板粗体（需amssymb）
\mathcal{C}   % 花体
\mathfrak{g}  % 哥特体（需amssymb）
\mathscr{F}   % 手写体（需mathrsfs）
\mathrm{Hom}  % 罗马体
\mathbf{v}    % 粗体
\mathsf{A}    % 无衬线
\mathtt{A}    % 打字机
\mathit{A}    % 斜体
\mathnormal{A} % 正常数学字体

```

### 9.2 文本大小

```latex
\displaystyle      % 显示样式
\textstyle         % 文本样式
\scriptstyle       % 标号样式
\scriptscriptstyle % 双重标号样式

```

## 十、间距控制

### 10.1 水平间距

```latex\,   % 小间距（约3/18 em）
\:   % 中间距（约4/18 em）
\;   % 大间距（约5/18 em）
\!   % 负间距（-3/18 em）
\quad    % 1 em
\qquad   % 2 em
\hspace{1cm}  % 指定间距
\phantom{x}   % 占位间距

```

### 10.2 使用场景

```latex
% 积分微分间距
\int f(x) \, dx

% 微分算子
\frac{dy}{dx} \, dx

% 调整
a\!b  % 减小间距

```

---

*最后更新：2026年4月*
*大部分命令需要amsmath宏包*
