---
习题编号: ALG-140
学科: 代数
知识点: 同调代数-群上同调谱序列
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Lyndon-Hochschild-Serre谱序列

## 题目

设 $G$ 是群，$H \triangleleft G$ 是正规子群。对 $G$-模 $M$，LHS谱序列联系群上同调。

**(a)** 证明：$H^p(G/H, H^q(H, M)) \Rightarrow H^{p+q}(G, M)$。

**(b)** 用此谱序列证明inflation-restriction正合列：
$$0 \to H^1(G/H, M^H) \to H^1(G, M) \to H^1(H, M)^{G/H} \to H^2(G/H, M^H) \to \cdots$$

**(c)** 计算 $H^*(\mathbb{Z}/p \times \mathbb{Z}/p, \mathbb{Z}/p)$。

## 解答

### (a) LHS谱序列

**证明：**

函子 $\text{Hom}_{\mathbb{Z}[G]}(\mathbb{Z}, -) = \text{Hom}_{\mathbb{Z}[G/H]}(\mathbb{Z}, \text{Hom}_{\mathbb{Z}[H]}(\mathbb{Z}, -))$。

应用Grothendieck谱序列于 $F = (-)^H$，$G = (-)^{G/H}$。

$(R^q F)(M) = H^q(H, M)$，$G$ 作用由共轭诱导。

得谱序列。$\square$

### (b) 膨胀-限制序列

**证明：**

由谱序列的低次项：
- $E^{2,0}_2 = H^2(G/H, M^H)$
- $E^{1,1}_2 = H^1(G/H, H^1(H, M))$
- $E^{0,2}_2 = H^0(G/H, H^2(H, M))$

$E^3 = H^3(G, M)$，有滤过。

由 $E_2$ 页结构，$d_2: E^{0,1}_2 \to E^{2,0}_2$ 给出连接同态。

正合列来自谱序列的边界映射。$\square$

### (c) 初等交换$p$群上同调

**解答：**

$G = \mathbb{Z}/p \times \mathbb{Z}/p = \langle a \rangle \times \langle b \rangle$。

用Künneth公式（或LHS）：
$$H^*(G, \mathbb{Z}/p) \cong H^*(\mathbb{Z}/p, \mathbb{Z}/p) \otimes H^*(\mathbb{Z}/p, \mathbb{Z}/p)$$

作为分次代数：
$$\cong \mathbb{Z}/p[x_1, x_2] \otimes \Lambda(y_1, y_2)$$
其中 $|x_i| = 2$，$|y_i| = 1$。

维数：$\dim H^n(G, \mathbb{Z}/p) = n+1$。
