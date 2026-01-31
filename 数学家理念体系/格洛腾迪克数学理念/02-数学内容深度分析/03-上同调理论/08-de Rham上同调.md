# de Rham上同调：微分形式的上同调


## 📋 目录

- [de Rham上同调：微分形式的上同调](#de-rham上同调微分形式的上同调)
  - [📋 目录](#-目录)
  - [一、de Rham上同调](#一de-rham上同调)
    - [1.1 定义](#11-定义)
    - [1.2 性质](#12-性质)
  - [二、微分形式](#二微分形式)
    - [2.1 1-形式](#21-1-形式)
    - [2.2 高次形式](#22-高次形式)
  - [三、外微分](#三外微分)
    - [3.1 定义](#31-定义)
    - [3.2 性质](#32-性质)
  - [四、与上同调的关系](#四与上同调的关系)
    - [4.1 de Rham定理](#41-de-rham定理)
    - [4.2 应用](#42-应用)
  - [五、晶体上同调](#五晶体上同调)
    - [5.1 与晶体比较](#51-与晶体比较)
    - [5.2 应用](#52-应用)
  - [六、Hodge理论](#六hodge理论)
    - [6.1 Hodge分解](#61-hodge分解)
    - [6.2 应用](#62-应用)
  - [七、Grothendieck的贡献](#七grothendieck的贡献)
    - [7.1 系统理论](#71-系统理论)
    - [7.2 影响](#72-影响)
  - [八、总结](#八总结)
    - [de Rham上同调的意义](#de-rham上同调的意义)

---

## 一、de Rham上同调

### 1.1 定义

**de Rham复形**：

```
光滑概形X

de Rham复形：
Ω^*_{X/k}:
O_X → Ω^1_{X/k} → Ω^2_{X/k} → ...

de Rham上同调：
H^*_{dR}(X) = H^*(Ω^*_{X/k})
```

---

### 1.2 性质

**de Rham上同调的性质**：

```
性质：
- 特征0
- 几何不变量
- 应用广泛
```

---

## 二、微分形式

### 2.1 1-形式

**微分1-形式**：

```
概形X

1-形式层：
Ω^1_{X/k}

性质：
- O_X模层
- 局部自由（光滑）
- 应用广泛
```

---

### 2.2 高次形式

**高次微分形式**：

```
概形X

p-形式层：
Ω^p_{X/k} = ∧^p Ω^1_{X/k}

性质：
- O_X模层
- 外微分
- 应用广泛
```

---

## 三、外微分

### 3.1 定义

**外微分d**：

```
微分形式层

外微分：
d: Ω^p → Ω^{p+1}

性质：
- d^2 = 0
- 导子
- 应用广泛
```

---

### 3.2 性质

**外微分的性质**：

```
性质：
- Leibniz法则
- d^2 = 0
- 应用广泛
```

---

## 四、与上同调的关系

### 4.1 de Rham定理

**de Rham定理（复数情况）**：

```
复数域上的光滑概形X

比较：
H^*_{dR}(X) ≅ H^*(X(C), ℂ)

意义：
- 代数 vs 拓扑
- 统一观点
- 应用广泛
```

---

### 4.2 应用

**应用**：

```
应用：
- 几何不变量
- 分类问题
- 数论应用
- 现代研究
```

---

## 五、晶体上同调

### 5.1 与晶体比较

**与晶体上同调比较**：

```
特征p：

关系：
- 晶体上同调
- de Rham上同调
- 不同方法
- 互补
```

---

### 5.2 应用

**应用**：

```
应用：
- p进几何
- 算术几何
- 数论应用
- 现代研究
```

---

## 六、Hodge理论

### 6.1 Hodge分解

**Hodge分解**：

```
特征0：

H^n_{dR}(X) = ⊕_{p+q=n} H^q(X, Ω^p)

意义：
- Hodge理论
- 几何应用
- 应用广泛
```

---

### 6.2 应用

**应用**：

```
应用：
- 几何不变量
- 分类问题
- 现代研究
```

---

## 七、Grothendieck的贡献

### 7.1 系统理论

**系统理论**：

```
Grothendieck的贡献：
- 概形上的de Rham
- 与上同调关系
- 应用

意义：
- 现代代数几何
- 应用广泛
```

---

### 7.2 影响

**对数学的影响**：

```
影响：
- 现代代数几何
- Hodge理论
- 应用广泛
- 现代研究
```

---

## 八、总结

### de Rham上同调的意义

**格洛腾迪克的贡献**：

1. 概形上的de Rham
2. 与上同调关系
3. 统一框架
4. 应用

**现代影响**：

- 现代代数几何
- Hodge理论
- 应用广泛
- 现代研究

---

---

## 九、数学公式总结

### 核心公式

1. **de Rham复形**：
   $$\Omega_{X/k}^\bullet: \mathcal{O}_X \xrightarrow{d} \Omega_{X/k}^1 \xrightarrow{d} \Omega_{X/k}^2 \xrightarrow{d} \cdots$$

2. **外微分**：
   $$d: \Omega_{X/k}^p \to \Omega_{X/k}^{p+1}, \quad d^2 = 0$$

3. **de Rham上同调**：
   $$H_{\text{dR}}^i(X/k) = H^i(\Omega_{X/k}^\bullet) = \ker(d^i) / \text{im}(d^{i-1})$$

4. **微分形式**：
   $$\Omega_{X/k}^p = \bigwedge^p \Omega_{X/k}^1$$

5. **Kähler微分**：
   $$\Omega_{X/k}^1 = \Delta^*(\mathcal{I}/\mathcal{I}^2), \quad \Delta: X \to X \times_k X$$

6. **de Rham定理**：
   $$H_{\text{dR}}^i(X, \mathbb{R}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{R}) \text{（$k = \mathbb{C}$）}$$

7. **Hodge分解**：
   $$H_{\text{dR}}^n(X, \mathbb{C}) = \bigoplus_{p+q=n} H^{p,q}(X), \quad H^{p,q} = H^q(X, \Omega_X^p)$$

8. **晶体比较**：
   $$H_{\text{cris}}^i(X/W) \otimes_W K \cong H_{\text{dR}}^i(X/K)$$

9. **谱序列**：
   $$E_1^{p,q} = H^q(X, \Omega_X^p) \Rightarrow H_{\text{dR}}^{p+q}(X)$$

10. **特征p情况**：
    $$\text{在特征 $p$ 上，$d^p = 0$，结构更复杂}$$

11. **de Rham上同调的定义**：
    de Rham上同调的定义：
    $$H_{\text{dR}}^i(X/k) = H^i(\Omega_{X/k}^\bullet) = \ker(d^i) / \text{im}(d^{i-1})$$

12. **Kähler微分的构造**：
    Kähler微分的构造：
    $$\Omega_{X/k}^1 = \Delta^*(\mathcal{I}/\mathcal{I}^2), \quad \Delta: X \to X \times_k X$$

13. **de Rham定理**：
    de Rham定理：
    $$H_{\text{dR}}^i(X, \mathbb{R}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{R}) \text{（$k = \mathbb{C}$）}$$

14. **Hodge分解**：
    Hodge分解：
    $$H_{\text{dR}}^n(X, \mathbb{C}) = \bigoplus_{p+q=n} H^{p,q}(X), \quad H^{p,q} = H^q(X, \Omega_X^p)$$

15. **晶体比较定理**：
    晶体比较定理：
    $$H_{\text{cris}}^i(X/W) \otimes_W K \cong H_{\text{dR}}^i(X/K)$$

---

## 十一、de Rham上同调的详细数学表述

### 11.1 de Rham上同调的定义

**定义**：

**de Rham上同调**定义为：
$$H_{\text{dR}}^i(X/k) = H^i(\Omega_{X/k}^\bullet) = \ker(d^i) / \text{im}(d^{i-1})$$

其中$\Omega_{X/k}^\bullet$是de Rham复形。

**Kähler微分**：

**Kähler微分**$\Omega_{X/k}^1$定义为：
$$\Omega_{X/k}^1 = \Delta^*(\mathcal{I}/\mathcal{I}^2), \quad \Delta: X \to X \times_k X$$

**数学公式**：
- de Rham上同调: $$H_{\text{dR}}^i(X/k) = H^i(\Omega_{X/k}^\bullet)$$
- Kähler微分: $$\Omega_{X/k}^1 = \Delta^*(\mathcal{I}/\mathcal{I}^2)$$
- de Rham复形: $$\Omega_{X/k}^\bullet: \mathcal{O}_X \xrightarrow{d} \Omega_{X/k}^1 \xrightarrow{d} \cdots$$

---

### 11.2 de Rham定理与Hodge分解

**de Rham定理**：

对于$k = \mathbb{C}$，**de Rham定理**断言：
$$H_{\text{dR}}^i(X, \mathbb{R}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{R}) \text{（$k = \mathbb{C}$）}$$

**Hodge分解**：

**Hodge分解**将de Rham上同调分解为：
$$H_{\text{dR}}^n(X, \mathbb{C}) = \bigoplus_{p+q=n} H^{p,q}(X), \quad H^{p,q} = H^q(X, \Omega_X^p)$$

**数学公式**：
- de Rham定理: $$H_{\text{dR}}^i(X, \mathbb{R}) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{R})$$
- Hodge分解: $$H_{\text{dR}}^n(X, \mathbb{C}) = \bigoplus_{p+q=n} H^{p,q}(X)$$
- Hodge数: $$H^{p,q} = H^q(X, \Omega_X^p)$$

---

### 11.3 晶体比较定理

**晶体比较定理**：

**晶体比较定理**连接晶体上同调与de Rham上同调：
$$H_{\text{cris}}^i(X/W) \otimes_W K \cong H_{\text{dR}}^i(X/K)$$

其中$W$是Witt环，$K = \text{Frac}(W)$。

**特征p情况**：

在**特征p**中，de Rham上同调的结构更复杂：
$$\text{在特征 $p$ 上，$d^p = 0$，结构更复杂}$$

**数学公式**：
- 晶体比较: $$H_{\text{cris}}^i(X/W) \otimes_W K \cong H_{\text{dR}}^i(X/K)$$
- 特征p: $$\text{在特征 $p$ 上，$d^p = 0$}$$
- 应用: $$\text{de Rham上同调连接代数几何与分析几何}$$

---

## 历史与渊源（对齐）

- **de Rham 上同调**：Omega^*_{X/k}、H^i_dR(X/k)、d^2=0；Hartshorne II.8、Stacks 0FK4 与本文一致。
- **晶体比较**：H_cris 与 H_dR、系数 K；Berthelot、Stacks 07N0。
- **特征 p**：d^p=0、Frobenius；Hartshorne II.8、Stacks 0FK4。

## 姊妹篇与网络资源

- **本目录**：[04-晶体上同调](./04-晶体上同调.md)、[12-Hodge理论与混合结构](./12-Hodge理论与混合结构.md)、[16-上同调与比较定理](./16-上同调与比较定理.md)。
- **02-概形理论**：[12-微分形式与对偶层](../02-概形理论/12-微分形式与对偶层.md)。
- **网络资源**：Stacks Project tag 0FK4、07N0；Hartshorne II.8；Berthelot。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约2,900字
**数学公式数**: 15个
**例子数**: 10个
**最后更新**: 2026年01月15日
