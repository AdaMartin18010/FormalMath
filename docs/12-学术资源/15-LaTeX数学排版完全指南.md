# LaTeX数学排版完全指南

> 本指南全面介绍LaTeX数学排版技术，从基础符号到高级公式环境，帮助读者掌握专业数学文档排版。

---

## 一、基础数学符号

### 1.1 希腊字母

#### 小写希腊字母

| 命令 | 符号 | 命令 | 符号 | 命令 | 符号 |
|------|------|------|------|------|------|
| `\alpha` | α | `\beta` | β | `\gamma` | γ |
| `\delta` | δ | `\epsilon` | ϵ | `\varepsilon` | ε |
| `\zeta` | ζ | `\eta` | η | `\theta` | θ |
| `\vartheta` | ϑ | `\iota` | ι | `\kappa` | κ |
| `\lambda` | λ | `\mu` | μ | `\nu` | ν |
| `\xi` | ξ | `\pi` | π | `\varpi` | ϖ |
| `\rho` | ρ | `\varrho` | ϱ | `\sigma` | σ |
| `\varsigma` | ς | `\tau` | τ | `\upsilon` | υ |
| `\phi` | ϕ | `\varphi` | φ | `\chi` | χ |
| `\psi` | ψ | `\omega` | ω | | |

#### 大写希腊字母

| 命令 | 符号 | 命令 | 符号 | 命令 | 符号 |
|------|------|------|------|------|------|
| `\Gamma` | Γ | `\Delta` | Δ | `\Theta` | Θ |
| `\Lambda` | Λ | `\Xi` | Ξ | `\Pi` | Π |
| `\Sigma` | Σ | `\Upsilon` | Υ | `\Phi` | Φ |
| `\Psi` | Ψ | `\Omega` | Ω | | |

### 1.2 常用数学符号

```latex
% 运算符
\pm \mp \times \div \cdot \ast \star \circ \bullet
+ - = < > \leq \geq \ll \gg \neq \approx \sim
\simeq \cong \equiv \propto \perp \parallel \angle

% 集合符号
\in \notin \ni \subset \supset \subseteq \supseteq
\cup \cap \setminus \emptyset \varnothing
\forall \exists \nexists

% 箭头
\leftarrow \rightarrow \leftrightarrow
\Leftarrow \Rightarrow \Leftrightarrow
\uparrow \downarrow \updownarrow
\mapsto \longmapsto

% 其他符号
\infty \partial \nabla \Re \Im \aleph \hbar
```

### 1.3 括号与定界符

```latex
\left( \frac{a}{b} \right)      % 圆括号
\left[ \sum_{i=1}^n x_i \right] % 方括号
\left\{ x \in X : P(x) \right\} % 花括号
\left| \int_a^b f(x) dx \right| % 绝对值
\left\| A \mathbf{x} \right\|   % 范数
\left\langle \vec{a}, \vec{b} \right\rangle % 尖括号
\left\lfloor x \right\rfloor    % 向下取整
\left\lceil x \right\rceil      % 向上取整
```

### 1.4 数集符号

```latex
\mathbb{N}  % 自然数
\mathbb{Z}  % 整数
\mathbb{Q}  % 有理数
\mathbb{R}  % 实数
\mathbb{C}  % 复数
\mathbb{F}  % 域
```

---

## 二、公式环境

### 2.1 行内与显示公式

```latex
% 行内公式
函数 $f(x) = x^2$ 在 $x=0$ 处可导。

% 显示公式（带编号）
\begin{equation}
    \int_a^b f(x) \, dx = F(b) - F(a)
    \label{eq:fundamental}
\end{equation}

% 显示公式（无编号）
\begin{equation*}
    e^{i\pi} + 1 = 0
\end{equation*}

% 简写形式
\[ \sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6} \]
```

### 2.2 多行公式

```latex
% align环境（推荐）
\begin{align}
    (a+b)^2 &= a^2 + 2ab + b^2 \\
    &= b^2 + 2ab + a^2
\end{align}

% gather环境（居中对齐）
\begin{gather}
    a_1 = b_1 + c_1 \\
    a_2 = b_2 + c_2 - d_2
\end{gather}

% multiline环境（长公式折行）
\begin{multline}
    a + b + c + d + e + f + g + h + i + j \\
    + k + l + m + n + o + p = 0
\end{multline}
```

### 2.3 分式与根式

```latex
\frac{a}{b}                    % 普通分式
\frac{\dfrac{a}{b}}{c}        % 嵌套分式
\tfrac{a}{b}                   % 行内小分式
\sqrt{a}                       % 平方根
\sqrt[n]{x}                    % n次方根
\binom{n}{k}                   % 二项式系数
```

### 2.4 求和、积分、极限

```latex
\sum_{i=1}^{n} x_i            % 求和
\prod_{i=1}^{n} x_i           % 乘积
\int_a^b f(x) \, dx           % 定积分
\iint_D f(x,y) \, dx\,dy     % 二重积分
\lim_{x \to \infty} f(x)       % 极限
\sup_{x \in A} f(x)            % 上确界
\max_{x \in A} f(x)            % 最大值
```

### 2.5 矩阵

```latex
% 圆括号矩阵
\begin{pmatrix}
    a_{11} & a_{12} \\
    a_{21} & a_{22}
\end{pmatrix}

% 方括号矩阵
\begin{bmatrix}
    1 & 0 \\
    0 & 1
\end{bmatrix}

% 行列式
\begin{vmatrix}
    a & b \\
    c & d
\end{vmatrix}

% 带省略号的矩阵
\begin{pmatrix}
    a_{11} & \cdots & a_{1n} \\
    \vdots & \ddots & \vdots \\
    a_{m1} & \cdots & a_{mn}
\end{pmatrix}
```

### 2.6 分段函数

```latex
f(x) = \begin{cases}
    x^2, & x \geq 0, \\
    -x, & x < 0.
\end{cases}
```

---

## 三、定理环境

### 3.1 定义定理环境

```latex
\usepackage{amsthm}

\theoremstyle{plain}
\newtheorem{theorem}{定理}[section]
\newtheorem{lemma}[theorem]{引理}
\newtheorem{proposition}[theorem]{命题}
\newtheorem{corollary}[theorem]{推论}

\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{example}{例}[section]

\theoremstyle{remark}
\newtheorem{remark}{注}[section]
```

### 3.2 使用定理环境

```latex
\begin{theorem}[费马大定理]
    当整数 $n > 2$ 时，方程 $x^n + y^n = z^n$ 没有正整数解。
\end{theorem}

\begin{proof}
    证明过程...
\end{proof}

\begin{definition}[群]
    群 $(G, \cdot)$ 是一个集合配上二元运算...
\end{definition}
```

---

## 四、图表绘制

### 4.1 TikZ基础

```latex
\usepackage{tikz}

% 基础图形
\begin{tikzpicture}
    \draw (0,0) -- (2,2);
    \draw[->] (0,0) -- (3,0) node[right] {$x$};
    \filldraw[fill=blue!20] (1,1) circle (0.5);
\end{tikzpicture}

% 函数图像
\begin{tikzpicture}[domain=-2:2]
    \draw[->] (-2.5,0) -- (2.5,0);
    \draw[color=blue] plot (\x,{\x^2});
\end{tikzpicture}
```

### 4.2 交换图

```latex
\usepackage{tikz-cd}

\begin{tikzcd}
    A \arrow[r, "f"] \arrow[d, "g"'] & B \arrow[d, "h"] \\
    C \arrow[r, "k"'] & D
\end{tikzcd}
```

### 4.3 科学绘图

```latex
\usepackage{pgfplots}

\begin{tikzpicture}
\begin{axis}[
    xlabel=$x$, ylabel=$y$,
    grid=major
]
\addplot[blue,thick] {x^2};
\end{axis}
\end{tikzpicture}
```

---

## 五、参考文献管理

### 5.1 BibTeX使用

```bibtex
% references.bib
@article{einstein1905,
    author = {Einstein, Albert},
    title = {Zur Elektrodynamik bewegter Körper},
    journal = {Annalen der Physik},
    volume = {322},
    pages = {891--921},
    year = {1905}
}

@book{hartshorne1977,
    author = {Hartshorne, Robin},
    title = {Algebraic Geometry},
    publisher = {Springer},
    year = {1977}
}
```

```latex
% 文档中
\cite{einstein1905}

\bibliographystyle{plain}
\bibliography{references}
```

### 5.2 常用引用命令

```latex
\cite{key}        % [1]
\citep{key}       % (Author, 2023)
\citet{key}       % Author (2023)
\cite[page 5]{key} % [1, page 5]
```

---

## 六、中文数学排版

### 6.1 基本配置

```latex
\documentclass[UTF8]{ctexart}
\usepackage{amsmath,amssymb,amsthm}

\newtheorem{theorem}{定理}
\newtheorem{definition}{定义}
\renewcommand{\proofname}{证明}
```

### 6.2 完整示例

```latex
\documentclass[UTF8]{ctexart}
\usepackage{amsmath,amssymb}

\title{数学文档示例}
\author{作者}
\date{\today}

\begin{document}
\maketitle

\section{引言}

考虑函数 $f(x) = e^x$，它在整个实数域上无限可导。

\begin{equation}
    e^x = \sum_{n=0}^{\infty} \frac{x^n}{n!}
\end{equation}

\section{主要结果}

\begin{theorem}[欧拉公式]
    对于任意实数 $\theta$，有
    \begin{equation}
        e^{i\theta} = \cos\theta + i\sin\theta
    \end{equation}
\end{theorem}

\begin{proof}
    由泰勒展开即可得证。
\end{proof}

\end{document}
```

---

## 七、常用技巧

### 7.1 间距控制

```latex
\,    % 小间距
\:    % 中间距
\;    % 大间距
\!    % 负间距
\quad % 1em间距
\qquad % 2em间距
```

### 7.2 公式编号控制

```latex
\nonumber         % 单行不编号
\notag            % 同上
\tag{1'}          % 自定义编号
\tag*{*}          % 自定义编号（无括号）
```

### 7.3 字体选择

```latex
\mathrm{ABC}      % 罗马体
\mathbf{ABC}      % 粗体
\mathsf{ABC}      % 无衬线
\mathtt{ABC}      % 打字机
\mathit{ABC}      % 斜体
\mathcal{ABC}     % 花体
\mathfrak{ABC}    % 哥特体
\mathbb{ABC}      % 黑板粗体
```

---

## 八、推荐模板

### 数学论文模板

```latex
\documentclass[12pt,a4paper]{article}
\usepackage[UTF8]{ctex}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{geometry}
\usepackage{hyperref}

\geometry{left=2.5cm,right=2.5cm,top=2.5cm,bottom=2.5cm}

\theoremstyle{plain}
\newtheorem{theorem}{定理}[section]
\newtheorem{lemma}{引理}[section]

\theoremstyle{definition}
\newtheorem{definition}{定义}[section]

\title{论文标题}
\author{作者}
\date{\today}

\begin{document}
\maketitle

\begin{abstract}
摘要内容...
\end{abstract}

\section{引言}
...

\bibliographystyle{plain}
\bibliography{references}

\end{document}
```

---

> **提示**：熟练掌握LaTeX数学排版需要大量练习。建议从简单公式开始，逐步掌握复杂环境的用法。参考优秀的数学论文也是学习的好方法。
