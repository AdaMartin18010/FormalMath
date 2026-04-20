---
msc_primary: 00A99
习题编号: ALG-210
学科: 代数
知识点: 表示论-Weyl公式
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
---

# Weyl 特征标公式

## 题目

**(a)** 证明 Weyl 特征标公式。

**(b)** 证明 Weyl 维数公式。

**(c)** 计算经典群不可约表示的维数。

## 解答

### (a) Weyl 特征标公式

**设置**：$G$ 是紧连通 Lie 群，$T \subset G$ 是极大环面，$W = N_G(T)/T$ 是 Weyl 群。

**特征标**：表示 $(\pi, V)$ 的特征标 $\chi_\pi(t) = \operatorname{tr}(\pi(t))$，$t \in T$。

**Weyl 特征标公式**：对支配权 $\lambda$，不可约表示 $V_\lambda$ 的特征标：

$$
\chi_\lambda(t) = \frac{\sum_{w \in W} \varepsilon(w) e^{w(\lambda + \rho)}(t)}{\prod_{\alpha > 0}(e^{\alpha/2}(t) - e^{-\alpha/2}(t))}
$$

其中 $\rho = \frac{1}{2}\sum_{\alpha > 0} \alpha$ 是 Weyl 向量，$\varepsilon(w) = (-1)^{l(w)}$。

等价（分母公式）：$\sum_{w \in W} \varepsilon(w) e^{w(\rho)} = \prod_{\alpha > 0}(e^{\alpha/2} - e^{-\alpha/2})$。

*证明概要*（Weyl 积分公式 + 反对称化）：

1. **特征标的 Weyl 反对称性**：$\chi_\lambda$ 在 $W$ 作用下不变：$\chi_\lambda(w \cdot t) = \chi_\lambda(t)$。

2. **Weyl 积分公式**：对类函数 $f$：
   $$\int_G f(g) dg = \frac{1}{|W|} \int_T f(t) |\Delta(t)|^2 dt$$
   其中 $\Delta(t) = \prod_{\alpha > 0}(e^{\alpha/2}(t) - e^{-\alpha/2}(t))$。

3. **正交关系**：$\langle \chi_\lambda, \chi_\mu \rangle = \delta_{\lambda\mu}$。

4. **Weyl 分母**：函数 $\Delta(t)$ 是 $W$-反对称的，且生成所有反对称函数的 $1$ 维空间（在适当函数空间中）。

5. **特征标的形式**：$\chi_\lambda \cdot \Delta$ 是 $W$-反对称指数函数的线性组合。由支配权和最高权理论，恰为 $\sum_{w \in W} \varepsilon(w) e^{w(\lambda + \rho)}$。

---

### (b) Weyl 维数公式

**定理**：

$$
\dim V_\lambda = \prod_{\alpha > 0} \frac{\langle \lambda + \rho, \alpha^\vee \rangle}{\langle \rho, \alpha^\vee \rangle}
$$

*证明*：特征标在 $t = e$（单位元）处有奇点。取 $t = \exp(h)$，$h \to 0$。

用 L'Hôpital：分子 $\sum_{w \in W} \varepsilon(w) e^{w(\lambda + \rho)(h)} \approx |W| \prod_{\alpha > 0} \langle \lambda + \rho, \alpha \rangle \cdot h^{|\Phi^+|}$。

分母 $\prod_{\alpha > 0}(e^{\alpha/2}(h) - e^{-\alpha/2}(h)) \approx \prod_{\alpha > 0} \langle \alpha, \alpha \rangle \cdot h^{|\Phi^+|}$。

比值给出维数公式。

---

### (c) 经典群的维数

**$SL(n, \mathbb{C})$**：根系统 $A_{n-1}$，$\rho = \frac{1}{2}\sum_{i=1}^n (n+1-2i)\varepsilon_i$。

最高权 $\lambda = \sum m_i \omega_i$，$\omega_i$ 是基本权。

**对称幂**：$V(k\omega_1) = S^k(\mathbb{C}^n)$，$\dim = \binom{n+k-1}{k}$。

**外幂**：$V(\omega_k) = \Lambda^k(\mathbb{C}^n)$，$\dim = \binom{n}{k}$。

**$SO(2n+1, \mathbb{C})$**：根系统 $B_n$。

**旋量表示**：$V(\omega_n)$，$\dim = 2^n$。

**$Sp(2n, \mathbb{C})$**：根系统 $C_n$。

**$SO(2n, \mathbb{C})$**：根系统 $D_n$。

**半旋量**：$V(\omega_{n-1}), V(\omega_n)$，$\dim = 2^{n-1}$。

---

## 常见错误

- **Weyl 向量的计算**：$\rho = \frac{1}{2}\sum_{\alpha > 0} \alpha$，对 $A_n$ 是 $(n, n-2, \ldots, -n)$，需正确计算。
- **支配权的条件**：$\langle \lambda, \alpha^\vee \rangle \geq 0$ 对所有单根，不是所有正根。
- **特征标的奇点**：$\chi_\lambda$ 在 Weyl 墙（$e^\alpha = 1$）上有奇点，公式需解析延拓。

## 参考文献

- Humphreys, *Introduction to Lie Algebras and Representation Theory*.
- Fulton & Harris, *Representation Theory*, GTM 129.
- Knapp, *Lie Groups Beyond an Introduction*.
