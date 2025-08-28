# FormalMath符号使用规范

## LaTeX数学符号标准化使用指南

---

## 📋 规范概述

本规范为FormalMath项目的数学符号使用提供统一、准确、标准化的指导。所有符号都遵循国际数学标准，确保在项目中的一致使用。

**规范原则**：

- **准确性**：符号使用准确无误
- **一致性**：符号使用保持一致
- **完整性**：覆盖数学符号的所有重要类别
- **国际化**：符合国际数学标准

---

## 🔢 基础数学符号 / Basic Mathematical Symbols

### 集合符号 / Set Symbols

#### 集合表示

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $A, B, C, \ldots$ | `$A, B, C, \ldots$` | 集合 | $A = \{1, 2, 3\}$ |
| $\emptyset$ | `$\emptyset$` | 空集 | $A = \emptyset$ |
| $\{\}$ | `$\{\}$` | 空集（替代表示） | $A = \{\}$ |
| $\mathbb{N}$ | `$\mathbb{N}$` | 自然数集 | $\mathbb{N} = \{1, 2, 3, \ldots\}$ |
| $\mathbb{Z}$ | `$\mathbb{Z}$` | 整数集 | $\mathbb{Z} = \{\ldots, -1, 0, 1, \ldots\}$ |
| $\mathbb{Q}$ | `$\mathbb{Q}$` | 有理数集 | $\mathbb{Q} = \{\frac{a}{b} \mid a,b \in \mathbb{Z}, b \neq 0\}$ |
| $\mathbb{R}$ | `$\mathbb{R}$` | 实数集 | $\mathbb{R}$ |
| $\mathbb{C}$ | `$\mathbb{C}$` | 复数集 | $\mathbb{C} = \{a + bi \mid a,b \in \mathbb{R}\}$ |

#### 元素关系

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\in$ | `$\in$` | 属于 | $a \in A$ |
| $\notin$ | `$\notin$` | 不属于 | $a \notin A$ |
| $\ni$ | `$\ni$` | 包含 | $A \ni a$ |

#### 集合运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\cup$ | `$\cup$` | 并集 | $A \cup B$ |
| $\cap$ | `$\cap$` | 交集 | $A \cap B$ |
| $\setminus$ | `$\setminus$` | 差集 | $A \setminus B$ |
| $\triangle$ | `$\triangle$` | 对称差 | $A \triangle B$ |
| $\times$ | `$\times$` | 笛卡尔积 | $A \times B$ |
| $\mathcal{P}(A)$ | `$\mathcal{P}(A)$` | 幂集 | $\mathcal{P}(A)$ |

#### 集合关系

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\subset$ | `$\subset$` | 真子集 | $A \subset B$ |
| $\subseteq$ | `$\subseteq$` | 子集 | $A \subseteq B$ |
| $\supset$ | `$\supset$` | 真包含 | $A \supset B$ |
| $\supseteq$ | `$\supseteq$` | 包含 | $A \supseteq B$ |
| $=$ | `$=$` | 相等 | $A = B$ |
| $\neq$ | `$\neq$` | 不相等 | $A \neq B$ |

### 逻辑符号 / Logical Symbols

#### 量词

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\forall$ | `$\forall$` | 全称量词 | $\forall x \in A$ |
| $\exists$ | `$\exists$` | 存在量词 | $\exists x \in A$ |
| $\exists!$ | `$\exists!$` | 唯一存在量词 | $\exists! x \in A$ |

#### 逻辑连接词

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\land$ | `$\land$` | 合取（且） | $p \land q$ |
| $\lor$ | `$\lor$` | 析取（或） | $p \lor q$ |
| $\neg$ | `$\neg$` | 否定（非） | $\neg p$ |
| $\implies$ | `$\implies$` | 蕴含 | $p \implies q$ |
| $\iff$ | `$\iff$` | 等价 | $p \iff q$ |

#### 集合构造

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\{x \mid P(x)\}$ | `$\{x \mid P(x)\}$` | 集合构造 | $\{x \in \mathbb{R} \mid x > 0\}$ |
| $\{x : P(x)\}$ | `$\{x : P(x)\}$` | 集合构造（替代） | $\{x \in \mathbb{R} : x > 0\}$ |

### 函数符号 / Function Symbols

#### 函数定义

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $f: X \to Y$ | `$f: X \to Y$` | 函数定义 | $f: \mathbb{R} \to \mathbb{R}$ |
| $f(x)$ | `$f(x)$` | 函数值 | $f(x) = x^2$ |
| $f^{-1}(y)$ | `$f^{-1}(y)$` | 逆函数值 | $f^{-1}(y)$ |
| $f \circ g$ | `$f \circ g$` | 函数复合 | $(f \circ g)(x) = f(g(x))$ |

#### 函数性质

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\text{dom}(f)$ | `$\text{dom}(f)$` | 定义域 | $\text{dom}(f) = \mathbb{R}$ |
| $\text{ran}(f)$ | `$\text{ran}(f)$` | 值域 | $\text{ran}(f) = [0, \infty)$ |
| $\text{im}(f)$ | `$\text{im}(f)$` | 像 | $\text{im}(f)$ |

---

## 🔢 代数符号 / Algebraic Symbols

### 群论符号 / Group Theory Symbols

#### 群运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\cdot$ | `$\cdot$` | 群运算 | $a \cdot b$ |
| $\circ$ | `$\circ$` | 群运算（替代） | $a \circ b$ |
| $+$ | `$+$` | 加法群运算 | $a + b$ |
| $a^n$ | `$a^n$` | 幂运算 | $a^3 = a \cdot a \cdot a$ |
| $a^{-1}$ | `$a^{-1}$` | 逆元 | $a \cdot a^{-1} = e$ |

#### 群关系

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\triangleleft$ | `$\triangleleft$` | 正规子群 | $N \triangleleft G$ |
| $\leq$ | `$\leq$` | 子群 | $H \leq G$ |
| $<$ | `$<$` | 真子群 | $H < G$ |
| $\cong$ | `$\cong$` | 同构 | $G \cong H$ |
| $\simeq$ | `$\simeq$` | 同构（替代） | $G \simeq H$ |

#### 群映射

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\text{Hom}(G,H)$ | `$\text{Hom}(G,H)$` | 同态集合 | $\text{Hom}(G,H)$ |
| $\text{Aut}(G)$ | `$\text{Aut}(G)$` | 自同构群 | $\text{Aut}(G)$ |
| $\text{End}(G)$ | `$\text{End}(G)$` | 自同态环 | $\text{End}(G)$ |
| $\ker(\phi)$ | `$\ker(\phi)$` | 核 | $\ker(\phi)$ |
| $\text{im}(\phi)$ | `$\text{im}(\phi)$` | 像 | $\text{im}(\phi)$ |

#### 群构造

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\langle S \rangle$ | `$\langle S \rangle$` | 生成子群 | $\langle a \rangle$ |
| $G/N$ | `$G/N$` | 商群 | $G/N$ |
| $gN$ | `$gN$` | 左陪集 | $gN$ |
| $Ng$ | `$Ng$` | 右陪集 | $Ng$ |

### 环论符号 / Ring Theory Symbols

#### 环运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $+$ | `$+$` | 加法 | $a + b$ |
| $\cdot$ | `$\cdot$` | 乘法 | $a \cdot b$ |
| $\times$ | `$\times$` | 乘法（替代） | $a \times b$ |
| $ab$ | `$ab$` | 乘法（省略） | $ab$ |
| $-a$ | `$-a$` | 加法逆元 | $a + (-a) = 0$ |

#### 环关系

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\triangleleft$ | `$\triangleleft$` | 理想 | $I \triangleleft R$ |
| $R/I$ | `$R/I$` | 商环 | $R/I$ |
| $a + I$ | `$a + I$` | 陪集 | $a + I$ |

#### 特殊环

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\mathbb{Z}_n$ | `$\mathbb{Z}_n$` | 模n整数环 | $\mathbb{Z}_6$ |
| $\mathbb{Z}[x]$ | `$\mathbb{Z}[x]$` | 整数多项式环 | $\mathbb{Z}[x]$ |
| $M_n(R)$ | `$M_n(R)$` | n阶矩阵环 | $M_2(\mathbb{R})$ |

### 域论符号 / Field Theory Symbols

#### 域运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $+$ | `$+$` | 加法 | $a + b$ |
| $\cdot$ | `$\cdot$` | 乘法 | $a \cdot b$ |
| $a^{-1}$ | `$a^{-1}$` | 乘法逆元 | $a \cdot a^{-1} = 1$ |
| $\frac{a}{b}$ | `$\frac{a}{b}$` | 除法 | $\frac{a}{b} = a \cdot b^{-1}$ |

#### 域扩张

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $F/K$ | `$F/K$` | 域扩张 | $\mathbb{C}/\mathbb{R}$ |
| $[F:K]$ | `$[F:K]$` | 扩张次数 | $[\mathbb{C}:\mathbb{R}] = 2$ |
| $K(\alpha)$ | `$K(\alpha)$` | 单扩张 | $\mathbb{Q}(\sqrt{2})$ |
| $\text{Gal}(F/K)$ | `$\text{Gal}(F/K)$` | 伽罗瓦群 | $\text{Gal}(\mathbb{C}/\mathbb{R})$ |

---

## 🔢 分析符号 / Analysis Symbols

### 极限符号 / Limit Symbols

#### 序列极限

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\lim_{n \to \infty} a_n$ | `$\lim_{n \to \infty} a_n$` | 序列极限 | $\lim_{n \to \infty} \frac{1}{n} = 0$ |
| $\limsup_{n \to \infty} a_n$ | `$\limsup_{n \to \infty} a_n$` | 上极限 | $\limsup_{n \to \infty} a_n$ |
| $\liminf_{n \to \infty} a_n$ | `$\liminf_{n \to \infty} a_n$` | 下极限 | $\liminf_{n \to \infty} a_n$ |

#### 函数极限

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\lim_{x \to a} f(x)$ | `$\lim_{x \to a} f(x)$` | 函数极限 | $\lim_{x \to 0} \frac{\sin x}{x} = 1$ |
| $\lim_{x \to a^+} f(x)$ | `$\lim_{x \to a^+} f(x)$` | 右极限 | $\lim_{x \to 0^+} \frac{1}{x} = \infty$ |
| $\lim_{x \to a^-} f(x)$ | `$\lim_{x \to a^-} f(x)$` | 左极限 | $\lim_{x \to 0^-} \frac{1}{x} = -\infty$ |

### 导数符号 / Derivative Symbols

#### 一元导数

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $f'(x)$ | `$f'(x)$` | 导数 | $f'(x) = \lim_{h \to 0} \frac{f(x+h)-f(x)}{h}$ |
| $\frac{df}{dx}$ | `$\frac{df}{dx}$` | 莱布尼茨记号 | $\frac{df}{dx}$ |
| $Df(x)$ | `$Df(x)$` | 微分算子 | $Df(x)$ |
| $f^{(n)}(x)$ | `$f^{(n)}(x)$` | n阶导数 | $f''(x), f'''(x)$ |

#### 偏导数

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\frac{\partial f}{\partial x}$ | `$\frac{\partial f}{\partial x}$` | 偏导数 | $\frac{\partial f}{\partial x}$ |
| $\partial_x f$ | `$\partial_x f$` | 偏导数（简化） | $\partial_x f$ |
| $\nabla f$ | `$\nabla f$` | 梯度 | $\nabla f = (\frac{\partial f}{\partial x}, \frac{\partial f}{\partial y})$ |
| $\text{grad } f$ | `$\text{grad } f$` | 梯度（文字） | $\text{grad } f$ |

### 积分符号 / Integral Symbols

#### 定积分

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\int_a^b f(x) dx$ | `$\int_a^b f(x) dx$` | 定积分 | $\int_0^1 x^2 dx = \frac{1}{3}$ |
| $\int_{-\infty}^{\infty} f(x) dx$ | `$\int_{-\infty}^{\infty} f(x) dx$` | 无穷积分 | $\int_{-\infty}^{\infty} e^{-x^2} dx = \sqrt{\pi}$ |

#### 不定积分

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\int f(x) dx$ | `$\int f(x) dx$` | 不定积分 | $\int x^2 dx = \frac{x^3}{3} + C$ |

#### 多重积分

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\iint_D f(x,y) dx dy$ | `$\iint_D f(x,y) dx dy$` | 二重积分 | $\iint_D f(x,y) dx dy$ |
| $\iiint_V f(x,y,z) dx dy dz$ | `$\iiint_V f(x,y,z) dx dy dz$` | 三重积分 | $\iiint_V f(x,y,z) dx dy dz$ |

### 级数符号 / Series Symbols

#### 无穷级数

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\sum_{n=1}^{\infty} a_n$ | `$\sum_{n=1}^{\infty} a_n$` | 无穷级数 | $\sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6}$ |
| $\sum_{n=0}^{\infty} a_n$ | `$\sum_{n=0}^{\infty} a_n$` | 从0开始的级数 | $\sum_{n=0}^{\infty} x^n = \frac{1}{1-x}$ |

#### 收敛性

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\sum a_n$ 收敛 | `$\sum a_n$ 收敛` | 级数收敛 | $\sum \frac{1}{n^2}$ 收敛 |
| $\sum a_n$ 发散 | `$\sum a_n$ 发散` | 级数发散 | $\sum \frac{1}{n}$ 发散 |

---

## 🔢 几何符号 / Geometric Symbols

### 几何关系 / Geometric Relations

#### 基本关系

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\parallel$ | `$\parallel$` | 平行 | $AB \parallel CD$ |
| $\perp$ | `$\perp$` | 垂直 | $AB \perp CD$ |
| $\angle$ | `$\angle$` | 角 | $\angle ABC$ |
| $\triangle$ | `$\triangle$` | 三角形 | $\triangle ABC$ |
| $\cong$ | `$\cong$` | 全等 | $\triangle ABC \cong \triangle DEF$ |
| $\sim$ | `$\sim$` | 相似 | $\triangle ABC \sim \triangle DEF$ |

#### 距离和长度

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\|AB\|$ | `$\|AB\|$` | 线段长度 | `$\|AB\|` = 5$ |
| $d(A,B)$ | `$d(A,B)$` | 距离 | $d(A,B) = 5$ |
| $\text{dist}(A,B)$ | `$\text{dist}(A,B)$` | 距离（文字） | $\text{dist}(A,B) = 5$ |

### 向量符号 / Vector Symbols

#### 向量表示

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\mathbf{v}$ | `$\mathbf{v}$` | 向量 | $\mathbf{v} = (1, 2, 3)$ |
| $\vec{v}$ | `$\vec{v}$` | 向量（箭头） | $\vec{v} = (1, 2, 3)$ |
| $v_i$ | `$v_i$` | 向量分量 | $v_1, v_2, v_3$ |

#### 向量运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $\mathbf{v} \cdot \mathbf{w}$ | `$\mathbf{v} \cdot \mathbf{w}$` | 点积 | $\mathbf{v} \cdot \mathbf{w}$ |
| $\mathbf{v} \times \mathbf{w}$ | `$\mathbf{v} \times \mathbf{w}$` | 叉积 | $\mathbf{v} \times \mathbf{w}$ |
| $\|\mathbf{v}\|$ | `$\|\mathbf{v}\|$` | 向量模长 | $\|\mathbf{v}\| = \sqrt{v_1^2 + v_2^2}$ |

### 矩阵符号 / Matrix Symbols

#### 矩阵表示

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $A$ | `$A$` | 矩阵 | $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ |
| $A_{ij}$ | `$A_{ij}$` | 矩阵元素 | $A_{12}$ |
| $A^T$ | `$A^T$` | 转置 | $A^T$ |
| $A^{-1}$ | `$A^{-1}$` | 逆矩阵 | $A^{-1}$ |
| $\det(A)$ | `$\det(A)$` | 行列式 | $\det(A)$ |
| $\text{tr}(A)$ | `$\text{tr}(A)$` | 迹 | $\text{tr}(A)$ |

#### 矩阵运算

| 符号 | LaTeX代码 | 含义 | 示例 |
|------|-----------|------|------|
| $A + B$ | `$A + B$` | 矩阵加法 | $A + B$ |
| $A \cdot B$ | `$A \cdot B$` | 矩阵乘法 | $A \cdot B$ |
| $AB$ | `$AB$` | 矩阵乘法（省略） | $AB$ |
| $A \otimes B$ | `$A \otimes B$` | 张量积 | $A \otimes B$ |

---

## 📊 符号使用规范

### 符号书写规范

#### 基本规则

1. **一致性**：同一符号在整个项目中保持一致的表示
2. **准确性**：符号使用准确无误
3. **清晰性**：符号表示清晰易读
4. **标准化**：遵循国际数学标准

#### 书写格式

1. **行内公式**：使用单个美元符号 `$...$`
2. **行间公式**：使用双美元符号 `$$...$$`
3. **对齐公式**：使用 `\begin{align}...\end{align}`

#### 常见错误

1. **符号混淆**：避免相似符号的混淆
2. **格式错误**：确保LaTeX语法正确
3. **上下文错误**：确保符号在正确上下文中使用

### 符号检查清单

#### 准确性检查

- [ ] 符号定义是否正确
- [ ] 符号使用是否准确
- [ ] 符号上下文是否合适

#### 一致性检查

- [ ] 同一概念是否使用相同符号
- [ ] 符号表示是否统一
- [ ] 符号风格是否一致

#### 清晰性检查

- [ ] 符号是否清晰易读
- [ ] 符号是否容易理解
- [ ] 符号是否避免歧义

---

**规范创建时间**: 2025年1月  
**规范版本**: v1.0  
**维护状态**: 持续更新中  
**适用范围**: FormalMath项目所有文档
