---
msc_primary: 00A99
习题编号: ALG-125
学科: 代数
知识点: 表示论-Burnside定理
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# Burnside定理与$p^aq^b$定理

## 题目

**(a) Burnside定理**：设 $\rho: G \to GL(V)$ 是复不可约表示，$C$ 是共轭类，$|C| = p^a$（$p$ 是素数），$C \neq \{e\}$。则 $\chi_\rho(C) = 0$ 或 $p | \dim(V)$。

**(b) $p^aq^b$定理**：若 $|G| = p^a q^b$，则 $G$ 可解。

**(c) 应用**：证明60阶单群必同构于 $A_5$。

## 解答

### (a) Burnside定理

**证明：**

设 $\chi = \chi_\rho$，$n = \dim(V)$，$\omega = \frac{|C|\chi(C)}{n}$。

**Step 1**：$\omega$ 是代数整数。

中心元 $z = \sum_{g \in C} g$ 作用在表示上为标量 $\lambda = \frac{|C|\chi(C)}{n}$。

$z$ 在群代数的中心，特征值是代数整数。

**Step 2**：若 $\chi(C) \neq 0$，则 $|\omega| \geq 1$。

$$|\omega| = \frac{|C| \cdot |\chi(C)|}{n} \geq \frac{p^a}{n}$$

由正交关系，$|\chi(C)| \leq n$。

**Step 3**：若 $p \nmid n$，则 $\omega$ 在单位根处取值。

$z/n$ 的本征值是代数整数，且 $|\omega| < 1$ 除非 $p | n$。

更严格：考虑 $\omega$ 的共轭，所有共轭的乘积是整数。

若 $p \nmid n$，则乘积的 $p$-adic估值为负，矛盾。

因此 $p | n$ 或 $\chi(C) = 0$。$\square$

### (b) $p^aq^b$定理

**证明概要**：

对 $|G|$ 归纳。

**Step 1**：Sylow子群非正规。

若 $P \lhd G$ 或 $Q \lhd G$，则商群可解，$G$ 可解。

**Step 2**：存在非平凡共轭类 $|C| = p^a$ 或 $q^b$。

由类方程。

**Step 3**：应用Burnside定理。

$G$ 有非平凡表示特征标在 $C$ 上为零或维数被 $p$ 整除。

**Step 4**：存在非平凡正规子群。

由表示的核，或特征标的不可约性。

**Step 5**：归纳。

正规子群和商群阶更小，可解，故 $G$ 可解。$\square$

### (c) 60阶单群

**证明**：

设 $|G| = 60 = 2^2 \cdot 3 \cdot 5$。

**Sylow分析**：

- $n_5 = 6$，$n_3 = 4$ 或 $10$，$n_2 = 5$ 或 $15$。

**嵌入**：$G$ 作用在Sylow 5-子群上，$G \hookrightarrow S_6$。

更精细：作用在陪集上，$G \hookrightarrow A_5$。

由单性，$G \cong A_5$。$\square$

## 证明技巧

1. **代数整数**：特征标值的数论性质
2. **共轭类方程**：群的组合结构
3. **Sylow定理**：有限群分类的工具

## 常见错误

- ❌ 忘记Burnside条件中非单位共轭类
- ❌ 可解性归纳步骤不完整
- ❌ Sylow数计算的约束条件遗漏

## 变式练习

**变式1：** 证明100阶群不是单群。

**变式2：** 分类120阶单群。
