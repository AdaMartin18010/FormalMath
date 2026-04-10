---
习题编号: AG-EX-005
标题: Serre对偶验证
类型: 技术型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch III
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14F17, 14C30
---

# AG-EX-005: Serre对偶验证

## 题目

### 原题 (Hartshorne III.7.1)

设 $X = \mathbb{P}^1_k$，验证Serre对偶对 $\mathcal{F} = \mathcal{O}(n)$ 对所有 $n \in \mathbb{Z}$ 成立。

即，证明存在自然的完美配对:
$$H^0(\mathbb{P}^1, \mathcal{O}(n)) \times H^1(\mathbb{P}^1, \mathcal{O}(-2-n)) \to k$$

### 验证题目

设 $X$ 是亏格 $g$ 的光滑射影曲线。

**(a)** 证明Serre对偶配对可以用留数明确写出。

**(b)** 对 $g = 1$（椭圆曲线），$D$ 是度0除子，验证:
$$H^0(\mathcal{L}(D)) \cong H^1(\mathcal{L}(-D))^*$$

**(c)** 计算配对矩阵在显式基下的形式。

---

## 解答

### 主题目解答

#### Serre对偶对 $\mathbb{P}^1$ 的验证

**已知**: 
- $\omega_{\mathbb{P}^1} = \mathcal{O}(-2)$
- $H^0(\mathcal{O}(n))$ 和 $H^1(\mathcal{O}(n))$ 的维数已知

**Step 1: 情形分类**

**情形 $n \geq 0$**:
- $h^0(\mathcal{O}(n)) = n + 1$
- $h^1(\mathcal{O}(n)) = 0$

Serre对偶断言:
$$H^0(\mathcal{O}(n)) \times H^1(\mathcal{O}(-2-n)) \to k$$

其中 $h^1(\mathcal{O}(-2-n)) = n + 1$，匹配！

**情形 $n = -1$**:
- $h^0 = h^1 = 0$（平凡成立）

**情形 $n \leq -2$**:
- $h^0(\mathcal{O}(n)) = 0$
- $h^1(\mathcal{O}(n)) = -n - 1$

Serre对偶断言:
$$H^0(\mathcal{O}(n)) \times H^1(\mathcal{O}(-2-n)) \to k$$

左边为0，右边 $h^0(\mathcal{O}(-2-n)) = -n - 1$，$h^1 = 0$。成立！

**Step 2: 显式配对构造**

设 $n \geq 0$。取标准仿射覆盖 $U_0 = \{x_0 \neq 0\}$, $U_1 = \{x_1 \neq 0\}$。

在 $U_0$ 上，坐标 $t = x_1/x_0$:
$$H^0(\mathcal{O}(n)) = \langle 1, t, t^2, \ldots, t^n \rangle$$

在Čech上同调中:
$$H^1(\mathcal{O}(-2-n)) = \langle t^{-1}, t^{-2}, \ldots, t^{-n-1} \rangle \cdot dt$$

**配对定义**:

对 $f(t) \in H^0(\mathcal{O}(n))$ 和 $\omega = g(t)dt \in H^1(\mathcal{O}(-2-n))$:

$$\langle f, \omega \rangle = \text{Res}_{t=0}(f(t) \cdot g(t) dt) + \text{Res}_{t=\infty}(f(t) \cdot g(t) dt)$$

由留数定理，$\sum \text{Res} = 0$，可仅用 $\infty$ 点的留数。

**Step 3: 验证配对完美**

取基:
- $H^0$: $e_i = t^i$, $i = 0, \ldots, n$
- $H^1$: $\epsilon_j = t^{-j-1}dt$, $j = 0, \ldots, n$

计算:
$$\langle e_i, \epsilon_j \rangle = \text{Res}_{\infty}(t^i \cdot t^{-j-1}dt) = \text{Res}_{\infty}(t^{i-j-1}dt)$$

$t = 1/s$ 在 $\infty$ 处，$dt = -s^{-2}ds$:
$$t^{i-j-1}dt = (1/s)^{i-j-1} \cdot (-s^{-2})ds = -s^{j-i-1}ds$$

$$\text{Res}_{s=0}(-s^{j-i-1}ds) = \begin{cases} -1 & i = j \\ 0 & i \neq j \end{cases}$$

**结论**: 配对矩阵是 $-I_{n+1}$，完美配对！

---

### 验证题目解答

#### (a) 留数公式

**定理**: 设 $X$ 是光滑射影曲线，$\omega_X$ 是典范丛。

Serre对偶配对:
$$H^0(X, \Omega_X^1 \otimes \mathcal{L}^{-1}) \times H^1(X, \mathcal{L}) \to k$$

可写为:
$$(\omega, \xi) \mapsto \sum_{P \in X} \text{Res}_P(\omega \cdot \xi_P)$$

其中 $\xi$ 用Čech上闭链表示，$\xi_P$ 是局部形式。

---

#### (b) 椭圆曲线情形

设 $E$ 是椭圆曲线，$D$ 度0除子。

**Step 1**: $K_E = \mathcal{O}_E$（典范平凡）。

**Step 2**: Serre对偶:
$$H^0(\mathcal{L}(D)) \cong H^1(\mathcal{L}(-D))^*$$

**Step 3**: 若 $D \not\sim 0$ 且 $D$ 不是挠除子:
- $h^0(\mathcal{L}(D)) = 0$（度0非平凡线丛无整体截面）
- $h^1(\mathcal{L}(-D)) = h^0(\mathcal{L}(D)) = 0$ ✓

**Step 4**: 若 $D \sim 0$:
- $h^0(\mathcal{O}_E) = 1$
- $h^1(\mathcal{O}_E) = 1$

配对是 $k \times k \to k$ 的标准配对。

---

#### (c) 配对矩阵

对椭圆曲线，取基 $1 \in H^0(\mathcal{O}_E)$ 和对应的对偶基。

配对矩阵是 $(1)$。

对一般 $n$，$\mathbb{P}^1$ 上的配对矩阵是负单位矩阵。

---

## 解题技巧

### 技巧1: Serre对偶三要素

```
┌─────────────────────────────────────────┐
│  Serre对偶: H^i(X, F) × H^{n-i}(X, ω⊗F^∨) → k  │
│                                         │
│  三要素:                                │
│  1. 典范丛 ω_X                          │
│  2. 维数匹配 h^i(F) = h^{n-i}(ω⊗F^∨)    │
│  3. 自然配对（Yoneda或留数）            │
└─────────────────────────────────────────┘
```

### 技巧2: $\mathbb{P}^1$ 上计算口诀

| $n$ | $h^0(\mathcal{O}(n))$ | $h^1(\mathcal{O}(n))$ |
|:---:|:---:|:---:|
| $\geq 0$ | $n+1$ | 0 |
| $-1$ | 0 | 0 |
| $\leq -2$ | 0 | $-n-1$ |

Serre对偶验证: $h^0(n) = h^1(-2-n)$

### 技巧3: 留数计算

对有理函数 $f(t)$ 在 $\infty$:
$$\text{Res}_{\infty}(f(t)dt) = -\text{Res}_{0}(f(1/s) \cdot (-s^{-2})ds)$$

---

## 变式与推广

### 变式1: 高维Serre对偶

设 $X = \mathbb{P}^n$，验证:
$$H^i(\mathcal{O}(m)) \cong H^{n-i}(\mathcal{O}(-n-1-m))^*$$

---

### 变式2: 曲线对偶的迹映射

构造典范同构:
$$\text{Tr}: H^1(X, \omega_X) \to k$$

并证明Serre对偶可由 $\text{Tr}$ 诱导。

---

### 变式3: Grothendieck对偶

推广Serre对偶到 proper morphism:
$$Rf_* R\mathcal{H}om_X(\mathcal{F}, \omega_X^\bullet) \cong R\mathcal{H}om_Y(Rf_*\mathcal{F}, \omega_Y^\bullet)$$

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Serre对偶 | 上同调的对偶定理 | - |
| 典范丛 | 最高阶微分形式 | $\omega_X$ |
| 完美配对 | 诱导同构到对偶 | perfect pairing |
| 留数 | 亚纯形式的局部不变量 | $\text{Res}$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch III, §7
2. Serre, J-P. *Un théorème de dualité*
3. Tate, J. *Residues of differentials on curves*

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
