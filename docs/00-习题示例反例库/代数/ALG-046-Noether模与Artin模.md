---
number: "ALG-046"
category: 代数
topic: 模论基础
difficulty: ⭐⭐⭐
title: Noether模与Artin模
keywords: [Noether模, Artin模, ACC, DCC, 有限生成, 有限长度]
prerequisites: [ALG-045, ALG-044]
source: 经典代数习题
---

## 题目

设 $R$ 是含幺环，$M$ 是 $R$-模。

**(a)** 定义：$M$ 是**Noether模**（满足ACC），如果子模的升链稳定。证明等价条件：
1. ACC
2. 任何非空子模集有极大元
3. 任何子模有限生成

**(b)** 定义：$M$ 是**Artin模**（满足DCC），如果子模的降链稳定。给出Artin模的例子和非例子。

**(c)** 证明：若 $0 \to M' \to M \to M'' \to 0$ 正合，则 $M$ Noether（Artin）当且仅当 $M', M''$ 都Noether（Artin）。

**(d)** 证明：域 $k$ 上的向量空间 $V$ 同时Noether和Artin当且仅当 $\dim_k V < \infty$。

## 详细解答

### (a) Noether模的等价条件

**证明：**

**(1 $\Rightarrow$ 2)** 设ACC成立，$\mathcal{S}$ 是非空子模集。

若 $\mathcal{S}$ 无极大元，可构造严格升链 $N_1 \subsetneq N_2 \subsetneq ...$，与ACC矛盾。

**(2 $\Rightarrow$ 3)** 设任何非空子模集有极大元，$N$ 是子模。

考虑有限生成子模集（含 $\{0\}$），有极大元 $N_0 \subset N$。

若 $N_0 \neq N$，取 $x \in N \setminus N_0$，则 $N_0 + Rx$ 严格大，矛盾。

故 $N = N_0$ 有限生成。

**(3 $\Rightarrow$ 1)** 设所有子模有限生成，$N_1 \subset N_2 \subset ...$ 是升链。

$N = \bigcup N_i$ 是子模，有限生成：$N = Rx_1 + ... + Rx_k$。

每个 $x_j \in N_{i_j}$，取 $N = \max(i_j)$，则所有 $x_j \in N_N$，$N \subset N_N \subset N_{N+1} \subset ... \subset N$。

故链稳定。

**证毕。**

### (b) Artin模

**定义：** $M$ 是Artin模，如果对任何降链 $N_1 \supset N_2 \supset ...$，存在 $N$ 使 $n \geq N$ 时 $N_n = N_N$。

**例子：**
- $\mathbb{Z}/p^n\mathbb{Z}$ 作为 $\mathbb{Z}$-模是Artin的（子模有限）
- 有限维向量空间

**非例子：**
- $\mathbb{Z}$ 作为 $\mathbb{Z}$-模：$\mathbb{Z} \supset 2\mathbb{Z} \supset 4\mathbb{Z} \supset ...$ 不稳定性
- $k[x]$ 作为 $k[x]$-模

### (c) 正合列的遗传性

**证明（Noether情形）：**

设 $0 \to M' \xrightarrow{f} M \xrightarrow{g} M'' \to 0$ 正合。

**($\Rightarrow$)** 设 $M$ Noether。

$M' \cong f(M')$ 是 $M$ 的子模，故Noether。

$M''$ 的子模对应 $M$ 的含 $\ker(g)$ 的子模，故Noether。

**($\Leftarrow$)** 设 $M', M''$ Noether。

设 $N_1 \subset N_2 \subset ...$ 是 $M$ 的升链。

则 $g(N_1) \subset g(N_2) \subset ...$ 在 $M''$ 中稳定，$N_i \cap \ker(g)$ 在 $M'$ 中稳定。

用五引理型论证，$N_i$ 稳定。

**Artin情形类似。**

**证毕。**

### (d) 有限维的刻画

**证明：**

**($\Rightarrow$)** 设 $V$ 同时Noether和Artin。

若 $\dim V = \infty$，有严格升链和严格降链：

$V_1 \subsetneq V_2 \subsetneq ...$，$W_1 \supsetneq W_2 \supsetneq ...$

其中 $V_i, W_i$ 是有限维子空间。

**($\Leftarrow$)** 设 $\dim V = n < \infty$。

子空间格有限，任何链稳定。

或直接：子空间由基的子集生成，有限个可能。

**证毕。**

## 证明技巧

1. **ACC/DCC的等价转化：** 升链稳定 $\leftrightarrow$ 极大元存在 $\leftrightarrow$ 有限生成
2. **正合列中的遗传性：** 子商保持链条件
3. **有限维的判定：** 同时满足ACC和DCC

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆Noether与Artin | 一个是升链，一个是降链 |
| 认为Noether等价有限生成 | 是整个模的每个子模有限生成 |
| 忘记Artin模不一定是Noether | 需要具体例子区分 |

## 变式练习

**变式1：** 证明$\mathbb{Z}$是Noether模但不是Artin模。

**变式2：** 设$R$是Noether环，$M$是有限生成$R$-模。证明$M$是Noether模。

**变式3：** 研究有有限长度的模：同时Noether和Artin，可构造合成列。
