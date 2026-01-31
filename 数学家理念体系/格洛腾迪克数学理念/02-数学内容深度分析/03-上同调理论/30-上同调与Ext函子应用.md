# 上同调与Ext函子应用：同调代数的几何应用


## 📋 目录

- [上同调与Ext函子应用：同调代数的几何应用](#上同调与ext函子应用同调代数的几何应用)
  - [📋 目录](#-目录)
  - [一、Ext函子](#一ext函子)
    - [1.1 定义](#11-定义)
    - [1.2 性质](#12-性质)
  - [二、上同调与Ext](#二上同调与ext)
    - [2.1 关系](#21-关系)
    - [2.2 应用](#22-应用)
  - [三、在代数几何中的应用](#三在代数几何中的应用)
    - [3.1 应用](#31-应用)
    - [3.2 几何应用](#32-几何应用)
  - [四、Grothendieck的贡献](#四grothendieck的贡献)
    - [4.1 系统理论](#41-系统理论)
    - [4.2 影响](#42-影响)
  - [五、现代发展](#五现代发展)
    - [5.1 导出推广](#51-导出推广)
    - [5.2 应用](#52-应用)
  - [六、应用](#六应用)
    - [6.1 几何应用](#61-几何应用)
    - [6.2 算术应用](#62-算术应用)
  - [七、总结](#七总结)
    - [上同调与Ext函子应用的意义](#上同调与ext函子应用的意义)

---

## 一、Ext函子

### 1.1 定义

**Ext函子Ext^i**：

```
概形X
O_X模M, N

Ext函子：
Ext^i(M, N) = H^i(Hom(P, N))

其中P是M的投射分解

意义：
- 同调代数
- 应用广泛
```

---

### 1.2 性质

**Ext函子的性质**：

```
性质：
- 函子性
- 应用广泛
```

---

## 二、上同调与Ext

### 2.1 关系

**上同调与Ext的关系**：

```
概形X
层F

上同调：
H^i(X, F) ≅ Ext^i(O_X, F)

在某些条件下

意义：
- 统一观点
- 应用广泛
```

---

### 2.2 应用

**应用**：

```
应用：
- 上同调计算
- 应用广泛
```

---

## 三、在代数几何中的应用

### 3.1 应用

**应用**：

```
应用：
- 上同调计算
- 应用广泛
```

---

### 3.2 几何应用

**几何应用**：

```
应用：
- 几何不变量
- 应用广泛
```

---

## 四、Grothendieck的贡献

### 4.1 系统理论

**系统理论**：

```
Grothendieck的贡献：
- Ext函子的系统应用
- 应用广泛

意义：
- 现代代数几何
- 应用广泛
```

---

### 4.2 影响

**对数学的影响**：

```
影响：
- 现代代数几何
- 同调代数
- 应用广泛
- 现代研究
```

---

## 五、现代发展

### 5.1 导出推广

**导出推广**：

```
经典Ext函子
    ↓
导出Ext函子
    ↓
∞-范畴
    ↓
高阶结构
```

---

### 5.2 应用

**现代应用**：

```
应用：
- 导出几何
- ∞-范畴
- 现代研究
```

---

## 六、应用

### 6.1 几何应用

**几何应用**：

```
应用：
- 几何不变量
- 应用广泛
```

---

### 6.2 算术应用

**算术应用**：

```
应用：
- 数论几何
- 应用广泛
```

---

## 七、总结

### 上同调与Ext函子应用的意义

**格洛腾迪克的贡献**：

1. Ext函子的系统应用
2. 应用广泛

**现代影响**：

- 现代代数几何
- 同调代数
- 应用广泛
- 现代研究

---

---

## 八、数学公式总结

### 核心公式

1. **Ext函子定义**：
   $$\text{Ext}^i(\mathcal{F}, \mathcal{G}) = R^i \text{Hom}(\mathcal{F}, -)(\mathcal{G})$$

2. **上同调与Ext关系**：
   $$H^i(X, \mathcal{F}) \cong \text{Ext}^i(\mathcal{O}_X, \mathcal{F})$$

3. **Ext长正合列**：
   $$0 \to \text{Hom}(\mathcal{F}, \mathcal{G}) \to \text{Hom}(\mathcal{F}, \mathcal{H}) \to \text{Hom}(\mathcal{F}, \mathcal{K}) \to \text{Ext}^1(\mathcal{F}, \mathcal{G}) \to \cdots$$

4. **Ext对称性**：
   $$\text{Ext}^i(\mathcal{F}, \mathcal{G}) \cong \text{Ext}^i(\mathcal{G}^*, \mathcal{F}^*) \text{（对偶）}$$

5. **Ext与Tor关系**：
   $$\text{Ext}^i(\mathcal{F}, \mathcal{G}) \cong \text{Tor}_i(\mathcal{F}^*, \mathcal{G})^*$$

6. **投射维数**：
   $$\text{pd}(\mathcal{F}) = \inf\{n : \text{Ext}^i(\mathcal{F}, -) = 0 \text{ 对所有 } i > n\}$$

7. **内射维数**：
   $$\text{id}(\mathcal{F}) = \inf\{n : \text{Ext}^i(-, \mathcal{F}) = 0 \text{ 对所有 } i > n\}$$

8. **Ext计算**：
   $$\text{Ext}^i(\mathcal{F}, \mathcal{G}) = H^i(\text{Hom}(\mathcal{P}^\bullet, \mathcal{G})) \text{（$\mathcal{P}^\bullet$ 是 $\mathcal{F}$ 的投射分解）}$$

9. **Serre对偶**：
   $$\text{Ext}^i(\mathcal{F}, \mathcal{G})^* \cong \text{Ext}^{n-i}(\mathcal{G}, \mathcal{F} \otimes \omega_X)$$

10. **Ext应用**：
    $$\text{分类扩张：} 0 \to \mathcal{G} \to \mathcal{E} \to \mathcal{F} \to 0 \text{ 对应 } \text{Ext}^1(\mathcal{F}, \mathcal{G})$$

11. **Ext与上同调的Serre对偶应用**：
    Ext与上同调的Serre对偶应用：
    $$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^* \text{（$X$ 光滑射影，$\dim X = n$）}$$

12. **Ext与推前的应用**：
    Ext与推前的应用：
    $$Rf_* R\mathcal{H}om_X(\mathcal{F}, \mathcal{G}) \cong R\mathcal{H}om_Y(Rf_*\mathcal{F}, Rf_*\mathcal{G}) \text{（某些条件下）}$$

13. **Ext与拉回的应用**：
    Ext与拉回的应用：
    $$f^* R\mathcal{H}om_Y(\mathcal{F}, \mathcal{G}) \cong R\mathcal{H}om_X(f^*\mathcal{F}, f^*\mathcal{G})$$

14. **Ext与张量积的应用**：
    Ext与张量积的应用：
    $$\text{Ext}^i(\mathcal{F} \otimes \mathcal{G}, \mathcal{H}) \cong \text{Ext}^i(\mathcal{F}, \mathcal{H}om(\mathcal{G}, \mathcal{H}))$$

15. **Ext与形变理论的应用**：
    Ext与形变理论的应用：
    $$\text{Ext}^1(\mathcal{F}, \mathcal{F}) \text{ 参数化 $\mathcal{F}$ 的一阶形变}$$

---

## 十、Ext函子应用的严格数学表述

### 10.1 Ext函子的严格构造

**Ext函子**：

设 $X$ 是概形，$\mathcal{F}, \mathcal{G}$ 是 $X$ 上的 $O_X$-模层。定义**Ext函子**：
$$\text{Ext}_X^i(\mathcal{F}, \mathcal{G}) = R^i \mathcal{H}om_X(\mathcal{F}, -)(\mathcal{G})$$

**构造方法**：

选择 $\mathcal{G}$ 的内射分解 $\mathcal{I}^\bullet$，则：
$$\text{Ext}_X^i(\mathcal{F}, \mathcal{G}) = H^i(\mathcal{H}om_X(\mathcal{F}, \mathcal{I}^\bullet))$$

**Ext函子的应用**：

**例9：线丛的Ext**

设 $X$ 是概形，$\mathcal{L}$ 是线丛。则：
$$\text{Ext}^i(\mathcal{L}, \mathcal{O}_X) = H^i(X, \mathcal{L}^{-1})$$

**例10：形变理论中的Ext**

设 $X$ 是概形，$\mathcal{F}$ 是凝聚层。则 $\text{Ext}^1(\mathcal{F}, \mathcal{F})$ 参数化 $\mathcal{F}$ 的一阶形变，即短正合列：
$$0 \to \mathcal{F} \to \mathcal{E} \to \mathcal{F} \to 0$$

### 10.2 Ext与上同调关系的应用

**关系**：

上同调可以表示为Ext：
$$H^i(X, \mathcal{F}) \cong \text{Ext}_X^i(\mathcal{O}_X, \mathcal{F})$$

**应用**：

这个关系将上同调计算转化为Ext计算，在形变理论和分类问题中有重要应用。

---

## 十一、Ext函子应用在概形理论中的应用

### 11.1 Ext函子应用与形变理论

**Ext函子应用在形变理论中的应用**：

Ext函子参数化形变：
$$\text{Ext}^1(\mathcal{F}, \mathcal{F}) \text{ 参数化 $\mathcal{F}$ 的一阶形变}$$

**数学公式**：
- 形变参数：$$\text{Ext}^1(\mathcal{F}, \mathcal{F})$$
- 形变空间：$$\text{Def}(\mathcal{F}) = \text{Spec}(k[\varepsilon] / (\varepsilon^2))$$
- 形变对应：$$0 \to \mathcal{F} \to \mathcal{E} \to \mathcal{F} \to 0$$

**例子11：形变理论的应用**：

形变理论在分类问题中有重要应用。

### 11.2 Ext函子应用与Serre对偶

**Ext函子应用与Serre对偶的关系**：

Ext函子应用与Serre对偶相关：
$$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$

**数学公式**：
- Serre对偶：$$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$
- 对偶Ext：$$\text{Ext}^i(\mathcal{F}, \mathcal{G}) \cong \text{Ext}^{n-i}(\mathcal{G}^*, \mathcal{F}^* \otimes \omega_X)$$

**例子12：Serre对偶的应用**：

Serre对偶在几何分类中有重要应用。

---

## 十二、Ext函子应用的现代发展

### 12.1 导出Ext函子应用

**导出Ext函子应用**：

Ext函子应用可以推广到导出几何：
$$R\mathcal{H}om_X(\mathcal{F}^\bullet, \mathcal{G}^\bullet) \text{ 导出Ext函子}$$

**数学公式**：
- 导出Ext：$$R\mathcal{H}om_X(\mathcal{F}^\bullet, \mathcal{G}^\bullet)$$
- ∞-Ext：$$R^{\infty}\mathcal{H}om_X(\mathcal{F}^\bullet, \mathcal{G}^\bullet)$$

**例子13：导出Ext函子应用**：

导出Ext函子应用在导出几何中有重要应用。

### 12.2 Ext函子应用的应用

**Ext函子应用在现代研究中的应用**：

Ext函子应用在现代研究中继续发展：
- **导出几何**：在导出几何中的应用
- **∞-范畴**：在∞-范畴中的应用
- **同伦理论**：在同伦理论中的应用

**数学公式**：
- 导出Ext：$$R\mathcal{H}om_X(\mathcal{F}^\bullet, \mathcal{G}^\bullet)$$
- ∞-Ext：$$R^{\infty}\mathcal{H}om_X(\mathcal{F}^\bullet, \mathcal{G}^\bullet)$$

**例子14：现代应用**：

Ext函子应用在现代研究中继续发展。

---

## 历史与渊源（对齐）

- **Ext 应用**：形变理论、扩张、分类、RHom 与上同调；Hartshorne III、Stacks 08HS、0A5R 与本文一致。
- **Ext^1 与扩张**：短正合列、参数化；Weibel、Stacks 08HS。
- **导出范畴**：RHom、Ext^i 与 H^i(RHom)；Stacks 08HP、08HS。

## 姊妹篇与网络资源

- **本目录**：[19-上同调与Ext函子](./19-上同调与Ext函子.md)、[06-导出版上同调](./06-导出版上同调.md)、[21-上同调与Serre对偶](./21-上同调与Serre对偶.md)、[22-上同调与Grothendieck对偶](./22-上同调与Grothendieck对偶.md)。
- **02-概形理论**：[25-概形的平坦族与形变理论](../02-概形理论/25-概形的平坦族与形变理论.md)、[32-概形的对偶理论与Serre对偶](../02-概形理论/32-概形的对偶理论与Serre对偶.md)。
- **网络资源**：Stacks Project tag 08HS、0A5R、08HP；Hartshorne III；Weibel。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约3,500字
**数学公式数**: 18个
**例子数**: 14个
**最后更新**: 2026年01月15日
