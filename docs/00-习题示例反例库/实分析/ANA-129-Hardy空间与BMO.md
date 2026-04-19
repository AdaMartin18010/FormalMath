---
msc_primary: 00A99
习题编号: ANA-129
学科: 实分析
知识点: 调和分析-Hardy空间与BMO
难度: ⭐⭐⭐⭐
预计时间: 45分钟
---

# Hardy空间与BMO

## 题目

设 $f \in L^1_{loc}(\mathbb{R}^n)$，定义**Hardy-Littlewood极大函数**：
$$Mf(x) = \sup_{r > 0} \frac{1}{|B(x,r)|} \int_{B(x,r)} |f(y)| dy$$

定义**BMO空间**（有界平均振动）：
$$\|f\|_{BMO} = \sup_Q \frac{1}{|Q|} \int_Q |f - f_Q| dx < \infty$$
其中 $f_Q = \frac{1}{|Q|} \int_Q f$ 是 $f$ 在方体 $Q$ 上的平均。

**(a)** 证明Hardy-Littlewood极大定理：对 $1 < p \leq \infty$，$\|Mf\|_{L^p} \leq C_p \|f\|_{L^p}$。

**(b)** 证明John-Nirenberg不等式：存在常数 $c_1, c_2 > 0$，对所有方体 $Q$ 和 $\lambda > 0$：
$$|\{x \in Q : |f(x) - f_Q| > \lambda\}| \leq c_1 |Q| \exp\left(-\frac{c_2 \lambda}{\|f\|_{BMO}}\right)$$

**(c)** 证明Fefferman-Stein定理：$(H^1)^* = BMO$。

## 解答

### (a) Hardy-Littlewood极大定理

**证明概要：**

**弱$(1,1)$估计**：
$$|\{Mf > \alpha\}| \leq \frac{C}{\alpha} \|f\|_{L^1}$$

用Vitali覆盖：若 $Mf(x) > \alpha$，存在球 $B_x$ 使 $\frac{1}{|B_x|}\int_{B_x} |f| > \alpha$。

这些球的5倍覆盖 $\{5B_i\}$ 控制 $\{Mf > \alpha\}$。

$$|\{Mf > \alpha\}| \leq \sum |5B_i| \leq 5^n \sum |B_i| \leq \frac{5^n}{\alpha} \sum \int_{B_i} |f| \leq \frac{5^n}{\alpha} \|f\|_{L^1}$$

**强$(p,p)$估计**（$p > 1$）：

用Marcinkiewicz插值，或C-Z分解：

对 $f = g + b$ 分解，$Mf \leq Mg + Mb$。

$\|Mg\|_{L^p} \leq C\|g\|_{L^p}$（因 $\|g\|_\infty \leq C\alpha$）。

$Mb$ 的弱估计由坏函数性质控制。$\square$

### (b) John-Nirenberg不等式

**证明概要：**

**Step 1**：Calderón-Zygmund分解。

设 $\|f\|_{BMO} = 1$，对 $Q_0$ 和水平 $\alpha_0 = 1$ 做C-Z分解。

得子方体 $\{Q_j\}$ 满足：
$$\alpha_0 < \frac{1}{|Q_j|} \int_{Q_j} |f - f_{Q_0}| \leq 2^n \alpha_0$$

**Step 2**：迭代。

对每个 $Q_j$，再做C-Z分解于水平 $\alpha_0$。

$$\sum |Q_j^k| \leq 2^{-k} |Q_0|$$

其中 $Q_j^k$ 是第$k$代子方体。

**Step 3**：指数衰减。

$$\{x \in Q_0 : |f - f_{Q_0}| > k\alpha_0\} \subset \bigcup_j Q_j^k$$

$$|\{\cdots\}| \leq 2^{-k} |Q_0|$$

对一般 $\lambda$，取 $k = \lfloor \lambda/\alpha_0 \rfloor$：
$$|\{|f - f_{Q_0}| > \lambda\}| \leq 2 \cdot 2^{-\lambda/\alpha_0} |Q_0|$$
$\square$

### (c) $(H^1)^* = BMO$

**证明概要：**

**Step 1**：$BMO \subset (H^1)^*$。

对原子 $a$（支撑于 $Q$，$\|a\|_\infty \leq |Q|^{-1}$，$\int a = 0$）：
$$\left|\int f a\right| = \left|\int (f - f_Q) a\right| \leq \|f\|_{BMO} \|a\|_\infty |Q| \leq \|f\|_{BMO}$$

由原子分解，$|\langle f, g \rangle| \leq C\|f\|_{BMO}\|g\|_{H^1}$。

**Step 2**：$(H^1)^* \subset BMO$。

设 $L \in (H^1)^*$，则 $L$ 对应某分布 $f$。

需证 $f \in BMO$。对任意 $Q$，构造试验函数：
$$\varphi_Q = \text{sign}(f - f_Q) \cdot \chi_Q$$

适当修改使其成为原子组合。

$|L(\varphi_Q)| \leq \|L\| \|\varphi_Q\|_{H^1}$ 给出BMO范数界。$\square$

## 证明技巧

1. **Vitali覆盖**：极大函数估计的几何工具
2. **C-Z迭代**：指数衰减的标准论证
3. **原子分解**：Hardy空间的结构定理

## 常见错误

- ❌ BMO范数中常数平均的选取混淆
- ❌ John-Nirenberg中常数的最优性忽视
- ❌ 原子定义中消失矩条件遗漏

## 变式练习

**变式1：** 证明$H^1$的极大函数刻画。

**变式2：** 讨论VMO（消失平均振动）空间。
