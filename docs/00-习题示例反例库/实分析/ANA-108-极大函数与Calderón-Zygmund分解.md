---
msc_primary: 00A99
习题编号: ANA-108
学科: 实分析
知识点: 调和分析-极大函数
难度: ⭐⭐⭐⭐⭐
预计时间: 40分钟
---

# 极大函数与Calderón-Zygmund分解

## 题目

**Hardy-Littlewood极大函数**：
$$Mf(x) = \sup_{r>0} \frac{1}{|B_r(x)|} \int_{B_r(x)} |f(y)| dy$$

(a) 证明 $M$ 的弱(1,1)有界性：
$$|\{x: Mf(x) > \lambda\}| \leq \frac{C_n}{\lambda} \|f\|_{L^1}$$

(b) 证明 $M$ 的 $(p,p)$ 有界性（$1 < p \leq \infty$）。

(c) 叙述并证明Calderón-Zygmund分解：对 $f \geq 0$ 可积，$\lambda > 0$，存在不交方体 $\{Q_j\}$ 使得：
(i) $f \leq \lambda$ a.e. 于 $G = \mathbb{R}^n \setminus \bigcup Q_j$；
(ii) $\lambda < \frac{1}{|Q_j|}\int_{Q_j} f \leq 2^n \lambda$。

## 解答

### (a) 弱(1,1)有界性

**证明：**

设 $E_\lambda = \{Mf > \lambda\}$。

对 $x \in E_\lambda$，存在球 $B$ 包含 $x$ 使得：
$$\frac{1}{|B|}\int_B |f| > \lambda$$

因此 $|B| < \frac{1}{\lambda}\int_B |f|$。

**Vitali覆盖**：$\{B\}$ 覆盖 $E_\lambda$，选不交子族 $\{B_k\}$ 使得 $E_\lambda \subset \bigcup_k 5B_k$。

$$|E_\lambda| \leq 5^n \sum_k |B_k| \leq \frac{5^n}{\lambda} \sum_k \int_{B_k} |f| \leq \frac{5^n}{\lambda} \|f\|_1$$

$\square$

### (b) $(p,p)$有界性

**证明：**

**$p = \infty$**：显然 $\|Mf\|_\infty \leq \|f\|_\infty$。

**$1 < p < \infty$**：用Marcinkiewicz插值。

由(a)，$M$ 弱(1,1)；由 $\infty$，强 $(\infty,\infty)$。

插值得强 $(p,p)$。$\square$

### (c) Calderón-Zygmund分解

**构造：**

**Step 1**：二进方体分解。

将 $\mathbb{R}^n$ 分成边长为 $2^k$ 的二进方体。

对每个 $k$，令 $\mathcal{D}_k$ 为边长 $2^k$ 的二进方体族。

**Step 2**：选择方体。

从足够大的 $k$（边长很大）开始，所有方体 $Q$ 满足：
$$\frac{1}{|Q|}\int_Q f \leq \lambda$$

对不满足的方体，将其细分为 $2^n$ 个子方体，继续检验。

**Step 3**：终止条件。

过程终止于满足 $\frac{1}{|Q|}\int_Q f > \lambda$ 的方体 $Q$，但其父方体满足平均值 $\leq \lambda$。

因此：
$$\lambda < \frac{1}{|Q|}\int_Q f \leq \frac{2^n}{|P|}\int_P f \leq 2^n \lambda$$

其中 $P$ 是父方体。

**Step 4**：好集上的估计。

$G$ 上的点属于所有父方体平均 $\leq \lambda$ 的方体序列。

由Lebesgue微分定理，$f \leq \lambda$ a.e. 于 $G$。$\square$

## 证明技巧

1. **Vitali覆盖**：从任意覆盖提取不交子覆盖
2. **Marcinkiewicz插值**：弱有界性到强有界性
3. **二进分解**：分层处理函数的局部平均

## 常见错误

- ❌ 极大函数定义中忘记上确界
- ❌ Vitali覆盖常数计算错误
- ❌ CZ分解中父方体平均的估计错误

## 变式练习

**变式1：** 用CZ分解证明奇异积分算子的 $(p,p)$ 有界性。

**变式2：** 证明BMO函数的John-Nirenberg不等式。
