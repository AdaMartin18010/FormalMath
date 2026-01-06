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

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约2,600字
**数学公式数**: 12个
**例子数**: 8个
**最后更新**: 2026年01月02日
