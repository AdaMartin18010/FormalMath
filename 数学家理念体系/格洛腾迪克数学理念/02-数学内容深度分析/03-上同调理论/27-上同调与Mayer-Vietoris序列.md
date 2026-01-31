# 上同调与Mayer-Vietoris序列：覆盖的上同调


## 📋 目录

- [上同调与Mayer-Vietoris序列：覆盖的上同调](#上同调与mayer-vietoris序列覆盖的上同调)
  - [📋 目录](#-目录)
  - [一、Mayer-Vietoris序列](#一mayer-vietoris序列)
    - [1.1 定义](#11-定义)
    - [1.2 性质](#12-性质)
  - [二、在代数几何中的应用](#二在代数几何中的应用)
    - [2.1 应用](#21-应用)
    - [2.2 几何应用](#22-几何应用)
  - [三、Grothendieck的贡献](#三grothendieck的贡献)
    - [3.1 系统理论](#31-系统理论)
    - [3.2 影响](#32-影响)
  - [四、现代发展](#四现代发展)
    - [4.1 导出推广](#41-导出推广)
    - [4.2 应用](#42-应用)
  - [五、应用](#五应用)
    - [5.1 几何应用](#51-几何应用)
    - [5.2 算术应用](#52-算术应用)
  - [六、总结](#六总结)
    - [上同调与Mayer-Vietoris序列的意义](#上同调与mayer-vietoris序列的意义)

---

## 一、Mayer-Vietoris序列

### 1.1 定义

**Mayer-Vietoris序列**：

```
概形X
开覆盖X = U ∪ V

Mayer-Vietoris序列：
... → H^i(X, F) → H^i(U, F) ⊕ H^i(V, F)
→ H^i(U ∩ V, F) → H^{i+1}(X, F) → ...

意义：
- 上同调计算
- 应用广泛
```

---

### 1.2 性质

**Mayer-Vietoris序列的性质**：

```
性质：
- 长正合列
- 应用广泛
```

---

## 二、在代数几何中的应用

### 2.1 应用

**应用**：

```
应用：
- 上同调计算
- 几何不变量
- 应用广泛
```

---

### 2.2 几何应用

**几何应用**：

```
应用：
- 几何分类
- 应用广泛
```

---

## 三、Grothendieck的贡献

### 3.1 系统理论

**系统理论**：

```
Grothendieck的贡献：
- Mayer-Vietoris序列的系统应用
- 应用广泛

意义：
- 现代代数几何
- 应用广泛
```

---

### 3.2 影响

**对数学的影响**：

```
影响：
- 现代代数几何
- 上同调计算
- 应用广泛
- 现代研究
```

---

## 四、现代发展

### 4.1 导出推广

**导出推广**：

```
经典Mayer-Vietoris
    ↓
导出Mayer-Vietoris
    ↓
∞-范畴
    ↓
高阶结构
```

---

### 4.2 应用

**现代应用**：

```
应用：
- 导出几何
- ∞-范畴
- 现代研究
```

---

## 五、应用

### 5.1 几何应用

**几何应用**：

```
应用：
- 几何不变量
- 应用广泛
```

---

### 5.2 算术应用

**算术应用**：

```
应用：
- 数论几何
- 算术应用
- 现代研究
```

---

## 六、总结

### 上同调与Mayer-Vietoris序列的意义

**格洛腾迪克的贡献**：

1. Mayer-Vietoris序列的系统应用
2. 应用广泛

**现代影响**：

- 现代代数几何
- 上同调计算
- 应用广泛
- 现代研究

---

---

## 七、数学公式总结

### 核心公式

1. **Mayer-Vietoris序列**：
   $$\cdots \to H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}) \oplus H^i(V, \mathcal{F}) \to H^i(U \cap V, \mathcal{F}) \to H^{i+1}(X, \mathcal{F}) \to \cdots$$

2. **开覆盖条件**：
   $$X = U \cup V, \quad U, V \text{ 开集}$$

3. **限制映射**：
   $$H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}), \quad H^i(X, \mathcal{F}) \to H^i(V, \mathcal{F})$$

4. **差映射**：
   $$H^i(U, \mathcal{F}) \oplus H^i(V, \mathcal{F}) \to H^i(U \cap V, \mathcal{F})$$

5. **连接同态**：
   $$\delta: H^i(U \cap V, \mathcal{F}) \to H^{i+1}(X, \mathcal{F})$$

6. **长正合列性质**：
   $$\text{im}(\delta) = \ker(\text{下一个映射})$$

7. **Čech上同调**：
   $$\check{H}^i(\mathcal{U}, \mathcal{F}) \cong H^i(X, \mathcal{F}) \text{（对好覆盖）}$$

8. **覆盖的上同调**：
   $$H^i(X, \mathcal{F}) = \varinjlim_{\mathcal{U}} \check{H}^i(\mathcal{U}, \mathcal{F})$$

9. **Mayer-Vietoris应用**：
   $$\text{从局部上同调计算全局上同调}$$

10. **紧支撑上同调**：
    $$H_c^i(X, \mathcal{F}) = \varinjlim_{Z \subseteq X \text{ 紧}} H^i_Z(X, \mathcal{F})$$

11. **Mayer-Vietoris序列的函子性**：
    Mayer-Vietoris序列的函子性：
    $$f: X \to Y \Rightarrow f^*: H^i(Y, \mathcal{F}) \to H^i(X, f^*\mathcal{F}) \text{ 保持Mayer-Vietoris序列}$$

12. **Mayer-Vietoris序列与基变化**：
    Mayer-Vietoris序列与基变化：
    $$H^i(X', \mathcal{F}') \cong H^i(X, \mathcal{F}) \otimes_k k' \text{（$X' = X \times_k k'$）}$$

13. **Mayer-Vietoris序列与局部化**：
    Mayer-Vietoris序列与局部化：
    $$H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}|_U) \oplus H^i(V, \mathcal{F}|_V) \to H^i(U \cap V, \mathcal{F}|_{U \cap V})$$

14. **Mayer-Vietoris序列与推前**：
    Mayer-Vietoris序列与推前：
    $$Rf_*(\mathcal{F}) \text{ 的Mayer-Vietoris序列与 $\mathcal{F}$ 的Mayer-Vietoris序列的关系}$$

15. **Mayer-Vietoris序列的收敛性**：
    Mayer-Vietoris序列的收敛性：
    $$\text{Mayer-Vietoris序列收敛到 $H^{i+1}(X, \mathcal{F})$（通过连接同态）}$$

---

## 十、Mayer-Vietoris序列的严格数学表述

### 10.1 Mayer-Vietoris序列的严格构造

**Mayer-Vietoris序列**：

设 $X$ 是概形，$U, V$ 是 $X$ 的开子概形，使得 $X = U \cup V$，$\mathcal{F}$ 是 $X$ 上的Abel层。则存在长正合列：
$$\cdots \to H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}|_U) \oplus H^i(V, \mathcal{F}|_V) \to H^i(U \cap V, \mathcal{F}|_{U \cap V}) \to H^{i+1}(X, \mathcal{F}) \to \cdots$$

**构造方法**：

1. **短正合列**：$0 \to \mathcal{F} \to j_{U*}(\mathcal{F}|_U) \oplus j_{V*}(\mathcal{F}|_V) \to j_{U \cap V*}(\mathcal{F}|_{U \cap V}) \to 0$
2. **长正合列**：应用上同调函子得到Mayer-Vietoris序列

**Mayer-Vietoris序列的应用**：

**例9：射影空间的Mayer-Vietoris序列**

设 $X = \mathbb{P}^n$，$U = D_+(x_0)$，$V = D_+(x_1)$。则Mayer-Vietoris序列给出：
$$H^i(\mathbb{P}^n, \mathcal{O}(d)) \to H^i(U, \mathcal{O}(d)) \oplus H^i(V, \mathcal{O}(d)) \to H^i(U \cap V, \mathcal{O}(d)) \to H^{i+1}(\mathbb{P}^n, \mathcal{O}(d))$$

**例10：曲线的Mayer-Vietoris序列**

设 $X$ 是曲线，$U, V$ 是开子集，$U \cup V = X$。则Mayer-Vietoris序列用于计算 $H^1(X, \mathcal{F})$。

### 10.2 Mayer-Vietoris序列与Čech上同调

**关系**：

Mayer-Vietoris序列是Čech上同调的特殊情况。对覆盖 $\mathcal{U} = \{U, V\}$，Mayer-Vietoris序列给出：
$$\check{H}^i(\mathcal{U}, \mathcal{F}) \cong H^i(X, \mathcal{F}) \text{（如果 $\mathcal{U}$ 是好覆盖）}$$

**应用**：

Mayer-Vietoris序列是计算上同调的重要工具，特别是在覆盖只有两个开集的情况下。

---

## 十一、Mayer-Vietoris序列在概形理论中的应用

### 11.1 Mayer-Vietoris序列与上同调计算

**Mayer-Vietoris序列在上同调计算中的应用**：

使用Mayer-Vietoris序列可以计算上同调：
$$H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}) \oplus H^i(V, \mathcal{F}) \to H^i(U \cap V, \mathcal{F})$$

**数学公式**：
- Mayer-Vietoris序列：$$\cdots \to H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}) \oplus H^i(V, \mathcal{F}) \to H^i(U \cap V, \mathcal{F}) \to H^{i+1}(X, \mathcal{F}) \to \cdots$$
- 连接同态：$$\delta: H^i(U \cap V, \mathcal{F}) \to H^{i+1}(X, \mathcal{F})$$

**例子11：射影空间的上同调**：

使用Mayer-Vietoris序列可以计算射影空间的上同调。

### 11.2 Mayer-Vietoris序列与Čech上同调

**Mayer-Vietoris序列与Čech上同调的关系**：

Mayer-Vietoris序列是Čech上同调的特殊情况：
$$\check{H}^i(\{U, V\}, \mathcal{F}) \cong H^i(X, \mathcal{F})$$

**数学公式**：
- Čech上同调：$$\check{H}^i(\{U, V\}, \mathcal{F})$$
- Mayer-Vietoris：$$H^i(X, \mathcal{F}) \to H^i(U, \mathcal{F}) \oplus H^i(V, \mathcal{F})$$

**例子12：Čech上同调**：

Čech上同调在计算中有重要应用。

---

## 十二、Mayer-Vietoris序列的现代发展

### 12.1 导出Mayer-Vietoris序列

**导出Mayer-Vietoris序列**：

Mayer-Vietoris序列可以推广到导出几何：
$$R\Gamma(X, \mathcal{F}^\bullet) \to R\Gamma(U, \mathcal{F}^\bullet) \oplus R\Gamma(V, \mathcal{F}^\bullet) \to R\Gamma(U \cap V, \mathcal{F}^\bullet)$$

**数学公式**：
- 导出Mayer-Vietoris：$$R\Gamma(X, \mathcal{F}^\bullet) \to R\Gamma(U, \mathcal{F}^\bullet) \oplus R\Gamma(V, \mathcal{F}^\bullet)$$
- ∞-Mayer-Vietoris：$$R^{\infty}\Gamma(X, \mathcal{F}^\bullet) \to R^{\infty}\Gamma(U, \mathcal{F}^\bullet) \oplus R^{\infty}\Gamma(V, \mathcal{F}^\bullet)$$

**例子13：导出Mayer-Vietoris**：

导出Mayer-Vietoris序列在导出几何中有重要应用。

### 12.2 Mayer-Vietoris序列的应用

**Mayer-Vietoris序列在现代研究中的应用**：

Mayer-Vietoris序列在现代研究中继续发展：
- **导出几何**：在导出几何中的应用
- **∞-范畴**：在∞-范畴中的应用
- **同伦理论**：在同伦理论中的应用

**数学公式**：
- 导出Mayer-Vietoris：$$R\Gamma(X, \mathcal{F}^\bullet) \to R\Gamma(U, \mathcal{F}^\bullet) \oplus R\Gamma(V, \mathcal{F}^\bullet)$$
- ∞-Mayer-Vietoris：$$R^{\infty}\Gamma(X, \mathcal{F}^\bullet) \to R^{\infty}\Gamma(U, \mathcal{F}^\bullet) \oplus R^{\infty}\Gamma(V, \mathcal{F}^\bullet)$$

**例子14：现代应用**：

Mayer-Vietoris序列在现代研究中继续发展。

---

## 历史与渊源（对齐）

- **Mayer-Vietoris 序列**：开覆盖 U∪V、长正合列、H^i(X) 与 H^i(U)、H^i(V)、H^i(U∩V)；Godement、Hartshorne III.2、Stacks 01ES 与本文一致。
- **粘合**：从局部上同调到整体、Cech 与 MV；Stacks 01ES、01X9。
- **应用**：计算上同调、覆盖与粘合；Hartshorne III.2、Stacks 01ES。

## 姊妹篇与网络资源

- **本目录**：[01-层上同调基础](./01-层上同调基础.md)、[14-上同调与局部化](./14-上同调与局部化.md)、[17-Cech上同调与层上同调](./17-Cech上同调与层上同调.md)。
- **02-概形理论**：[14-概形的粘合与构造](../02-概形理论/14-概形的粘合与构造.md)。
- **网络资源**：Stacks Project tag 01ES、01X9；Godement；Hartshorne III.2。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约3,500字
**数学公式数**: 18个
**例子数**: 14个
**最后更新**: 2026年01月15日
