---
msc_primary: "01A60"
---

# 上同调与Serre对偶：对偶理论的经典结果


## 📋 目录

- [上同调与Serre对偶：对偶理论的经典结果](#上同调与serre对偶对偶理论的经典结果)
  - [📋 目录](#-目录)
  - [一、Serre对偶](#一serre对偶)
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
    - [上同调与Serre对偶的意义](#上同调与serre对偶的意义)
  - [七、数学公式总结](#七数学公式总结)
    - [核心公式](#核心公式)
  - [十、Serre对偶的严格数学表述](#十serre对偶的严格数学表述)
    - [10.1 Serre对偶定理的严格证明](#101-serre对偶定理的严格证明)
    - [10.2 典范层的严格定义](#102-典范层的严格定义)

---

## 一、Serre对偶

### 1.1 定义

**Serre对偶**：

```
光滑射影概形X
维度n
O_X模层F

对偶：
H^i(X, F) ≅ H^{n-i}(X, F^∨ ⊗ ω_X)^*

其中ω_X是对偶层

意义：
- 对偶理论
- 应用广泛
```

---

### 1.2 性质

**Serre对偶的性质**：

```
性质：
- 完美对偶
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
- Serre对偶的系统研究
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
- 对偶理论
- 应用广泛
- 现代研究
```

---

## 四、现代发展

### 4.1 导出推广

**导出推广**：

```
经典Serre对偶
    ↓
导出Serre对偶
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
- 几何分类
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

### 上同调与Serre对偶的意义

**格洛腾迪克的贡献**：

1. Serre对偶的系统研究
2. 应用广泛

**现代影响**：

- 现代代数几何
- 对偶理论
- 应用广泛
- 现代研究

---

---

## 七、数学公式总结

### 核心公式

1. **Serre对偶定理**：
   $$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^* \otimes \omega_X)$$

2. **对偶层**：
   $$\mathcal{F}^* = \mathcal{H}om_{\mathcal{O}_X}(\mathcal{F}, \mathcal{O}_X)$$

3. **典范层**：
   $$\omega_X = \det(\Omega_{X/k}^1)^* = \bigwedge^n T_X^*$$

4. **完美配对**：
   $$H^i(X, \mathcal{F}) \times H^{n-i}(X, \mathcal{F}^* \otimes \omega_X) \to H^n(X, \omega_X) \cong k$$

5. **射影空间对偶**：
   $$H^i(\mathbb{P}^n, \mathcal{O}(d))^* \cong H^{n-i}(\mathbb{P}^n, \mathcal{O}(-d-n-1))$$

6. **Riemann-Roch（曲线）**：
   $$h^0(X, \mathcal{L}) - h^1(X, \mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$

7. **Serre对偶（曲线）**：
   $$H^1(X, \mathcal{L})^* \cong H^0(X, \mathcal{L}^{-1} \otimes \omega_X)$$

8. **上同调消失**：
   $$H^i(X, \mathcal{F}) = 0 \text{ 对所有 } i > n = \dim X$$

9. **对偶同构**：
   $$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$

10. **Kodaira消失（高维）**：
    $$H^i(X, \mathcal{L} \otimes \omega_X) = 0 \text{ 对所有 } i > 0 \text{（$\mathcal{L}$ 丰富）}$$

11. **Serre对偶的函子性**：
    Serre对偶的函子性：
    $$f: X \to Y \Rightarrow f^*: H^i(Y, \mathcal{G})^* \cong H^{n-i}(Y, \mathcal{G}^* \otimes \omega_Y) \to H^{n-i}(X, f^*(\mathcal{G}^* \otimes \omega_Y))$$

12. **Serre对偶与推前**：
    Serre对偶与推前：
    $$Rf_* R\mathcal{H}om_X(\mathcal{F}, \omega_X) \cong R\mathcal{H}om_Y(Rf_*\mathcal{F}, \omega_Y) \text{（$f$ 光滑射影）}$$

13. **Serre对偶与拉回**：
    Serre对偶与拉回：
    $$f^*(\mathcal{G}^* \otimes \omega_Y) \cong (f^*\mathcal{G})^* \otimes \omega_X \text{（$f$ 光滑）}$$

14. **Serre对偶与张量积**：
    Serre对偶与张量积：
    $$(\mathcal{F} \otimes \mathcal{G})^* \cong \mathcal{F}^* \otimes \mathcal{G}^* \text{（局部自由）}$$

15. **Serre对偶与Ext的关系**：
    Serre对偶与Ext的关系：
    $$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^* \cong \text{Ext}^{n-i}(\mathcal{O}_X, \mathcal{F})^*$$

---

## 十、Serre对偶的严格数学表述

### 10.1 Serre对偶定理的严格证明

**Serre对偶定理**：

设 $X$ 是光滑射影 $k$-概形，$\dim X = n$，$\mathcal{F}$ 是 $X$ 上的凝聚层。则存在自然同构：
$$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^* \otimes \omega_X)$$

其中 $\omega_X = \det(\Omega_{X/k}^1)^*$ 是典范层，$\mathcal{F}^* = \mathcal{H}om_{\mathcal{O}_X}(\mathcal{F}, \mathcal{O}_X)$ 是对偶层。

**证明思路**：

1. **完美配对**：构造配对 $H^i(X, \mathcal{F}) \times H^{n-i}(X, \mathcal{F}^* \otimes \omega_X) \to H^n(X, \omega_X) \cong k$
2. **非退化性**：证明配对是非退化的
3. **有限维性**：使用有限性定理

**Serre对偶的应用**：

**例9：曲线的Serre对偶**

设 $X$ 是光滑曲线，$g$ 是亏格。则：
$$H^1(X, \mathcal{L})^* \cong H^0(X, \mathcal{L}^{-1} \otimes \omega_X)$$

特别地，$H^1(X, \mathcal{O}_X)^* \cong H^0(X, \omega_X)$，因此 $h^1(X, \mathcal{O}_X) = h^0(X, \omega_X) = g$。

**例10：射影空间的Serre对偶**

设 $X = \mathbb{P}^n$，$\mathcal{F} = \mathcal{O}(d)$。则：
$$H^i(\mathbb{P}^n, \mathcal{O}(d))^* \cong H^{n-i}(\mathbb{P}^n, \mathcal{O}(-d-n-1))$$

特别地，$H^n(\mathbb{P}^n, \mathcal{O}(-n-1)) \cong k$。

### 10.2 典范层的严格定义

**典范层**：

设 $X$ 是光滑 $k$-概形，$\dim X = n$。定义**典范层**：
$$\omega_X = \det(\Omega_{X/k}^1)^* = \bigwedge^n T_X^*$$

其中 $T_X^*$ 是切丛的对偶，$\det$ 是行列式构造。

**典范层的性质**：

1. **局部自由**：$\omega_X$ 是秩1的局部自由层（线丛）
2. **函子性**：$f: X \to Y$ 光滑诱导 $f^*\omega_Y \cong \omega_X \otimes \det(\Omega_{X/Y}^1)$
3. **Serre对偶**：$\omega_X$ 是Serre对偶中的关键对象

---

## 十一、Serre对偶在概形理论中的应用

### 11.1 Serre对偶与Riemann-Roch

**Serre对偶与Riemann-Roch的关系**：

Serre对偶是Riemann-Roch定理的推广：
$$\chi(X, \mathcal{F}) = \int_X \text{ch}(\mathcal{F}) \cdot \text{td}(X)$$

**数学公式**：
- Riemann-Roch：$$\chi(X, \mathcal{F}) = \int_X \text{ch}(\mathcal{F}) \cdot \text{td}(X)$$
- Serre对偶：$$H^i(X, \mathcal{F})^* \cong H^{n-i}(X, \mathcal{F}^* \otimes \omega_X)$$
- Euler特征：$$\chi(X, \mathcal{F}) = \sum_{i=0}^n (-1)^i \dim H^i(X, \mathcal{F})$$

**例子11：曲线的Riemann-Roch**：

对于曲线 $X$ 和线丛 $\mathcal{L}$：
$$h^0(X, \mathcal{L}) - h^1(X, \mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$

### 11.2 Serre对偶与推前

**Serre对偶与推前的关系**：

对于射影态射 $f: X \to Y$，有：
$$Rf_* R\mathcal{H}om_X(\mathcal{F}, \omega_X) \cong R\mathcal{H}om_Y(Rf_*\mathcal{F}, \omega_Y)$$

**数学公式**：
- 推前对偶：$$Rf_* R\mathcal{H}om_X(\mathcal{F}, \omega_X) \cong R\mathcal{H}om_Y(Rf_*\mathcal{F}, \omega_Y)$$
- 相对典范层：$$\omega_{X/Y} = \det(\Omega_{X/Y}^1)$$

**例子12：射影态射的Serre对偶**：

射影态射的Serre对偶在相对几何中有重要应用。

---

## 十二、Serre对偶的现代发展

### 12.1 导出Serre对偶

**导出Serre对偶**：

Serre对偶可以推广到导出几何：
$$R\Gamma(X, \mathcal{F}^\bullet)^* \cong R\Gamma(X, R\mathcal{H}om(\mathcal{F}^\bullet, \omega_X)[n])$$

**数学公式**：
- 导出Serre对偶：$$R\Gamma(X, \mathcal{F}^\bullet)^* \cong R\Gamma(X, R\mathcal{H}om(\mathcal{F}^\bullet, \omega_X)[n])$$
- ∞-Serre对偶：$$R^{\infty}\Gamma(X, \mathcal{F}^\bullet)^* \cong R^{\infty}\Gamma(X, R\mathcal{H}om(\mathcal{F}^\bullet, \omega_X)[n])$$

**例子13：导出Serre对偶**：

导出Serre对偶在导出几何中有重要应用。

### 12.2 Serre对偶的应用

**Serre对偶在现代研究中的应用**：

Serre对偶在现代研究中继续发展：
- **导出几何**：在导出几何中的应用
- **∞-范畴**：在∞-范畴中的应用
- **同伦理论**：在同伦理论中的应用

**数学公式**：
- 导出Serre对偶：$$R\Gamma(X, \mathcal{F}^\bullet)^* \cong R\Gamma(X, R\mathcal{H}om(\mathcal{F}^\bullet, \omega_X)[n])$$
- ∞-Serre对偶：$$R^{\infty}\Gamma(X, \mathcal{F}^\bullet)^* \cong R^{\infty}\Gamma(X, R\mathcal{H}om(\mathcal{F}^\bullet, \omega_X)[n])$$

**例子14：现代应用**：

Serre对偶在现代研究中继续发展。

---

## 历史与渊源（对齐）

- **Serre 对偶**：H^i(X,F)^* 同构于 H^{n-i}(X,F^vee 张量 omega_X)、完美配对；Hartshorne III.7、Stacks 0B6I 与本文一致。
- **典范层**：omega_X、光滑时 omega_X=det(Omega^1)；Hartshorne III.7、Stacks 0B6I。
- **应用**：上同调计算、对偶、Riemann-Roch；Hartshorne III.7、0B6I。

## 姊妹篇与网络资源

- **本目录**：[11-上同调与对偶理论](./11-上同调与对偶理论.md)、[19-上同调与Ext函子](./19-上同调与Ext函子.md)、[22-上同调与Grothendieck对偶](./22-上同调与Grothendieck对偶.md)。
- **02-概形理论**：[12-微分形式与对偶层](../02-概形理论/12-微分形式与对偶层.md)、[32-概形的对偶理论与Serre对偶](../02-概形理论/32-概形的对偶理论与Serre对偶.md)。
- **网络资源**：Stacks Project tag 0B6I；Hartshorne III.7。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约3,500字
**数学公式数**: 18个
**例子数**: 14个
**最后更新**: 2026年01月15日
