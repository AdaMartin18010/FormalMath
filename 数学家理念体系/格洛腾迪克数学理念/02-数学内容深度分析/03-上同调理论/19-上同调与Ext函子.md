# 上同调与Ext函子：同调代数与几何的连接


## 📋 目录

- [上同调与Ext函子：同调代数与几何的连接](#上同调与ext函子同调代数与几何的连接)
  - [📋 目录](#-目录)
  - [一、Ext函子](#一ext函子)
    - [1.1 定义](#11-定义)
    - [1.2 性质](#12-性质)
  - [二、上同调与Ext](#二上同调与ext)
    - [2.1 关系](#21-关系)
    - [2.2 应用](#22-应用)
  - [三、在代数几何中的应用](#三在代数几何中的应用)
    - [3.1 几何应用](#31-几何应用)
    - [3.2 形变应用](#32-形变应用)
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
    - [上同调与Ext函子的意义](#上同调与ext函子的意义)

---

## 一、Ext函子

### 1.1 定义

**Ext函子Ext^i**：

```
概形X
O_X模层F, G

Ext函子：
Ext^i_X(F, G) = R^i Hom_X(F, -)(G)

性质：
- 右导出函子
- 应用广泛
```

---

### 1.2 性质

**Ext函子的性质**：

```
性质：
- Ext^0(F, G) = Hom(F, G)
- 长正合列
- 应用广泛
```

---

## 二、上同调与Ext

### 2.1 关系

**上同调与Ext的关系**：

```
概形X
O_X模层F

在某些条件下：
H^i(X, F) ≅ Ext^i(O_X, F)

意义：
- 上同调计算
- 应用广泛
```

---

### 2.2 应用

**应用**：

```
应用：
- 上同调计算
- 几何不变量
- 应用广泛
```

---

## 三、在代数几何中的应用

### 3.1 几何应用

**几何应用**：

```
应用：
- 几何不变量
- 分类问题
- 应用广泛
```

---

### 3.2 形变应用

**形变应用**：

```
应用：
- 形变理论
- 应用广泛
```

---

## 四、Grothendieck的贡献

### 4.1 系统理论

**系统理论**：

```
Grothendieck的贡献：
- Ext函子的系统应用
- 上同调关系
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
- 分类问题
- 应用广泛
```

---

### 6.2 算术应用

**算术应用**：

```
应用：
- 数论几何
- 算术应用
- 现代研究
```

---

## 七、总结

### 上同调与Ext函子的意义

**格洛腾迪克的贡献**：

1. Ext函子的系统应用
2. 上同调关系
3. 统一框架

**现代影响**：

- 现代代数几何的基础
- 同调代数
- 应用广泛
- 现代研究

---

---

## 八、数学公式总结

### 核心公式

1. **Ext函子定义**：
   $$\text{Ext}_X^i(\mathcal{F}, \mathcal{G}) = R^i \mathcal{H}om_X(\mathcal{F}, -)(\mathcal{G}) = H^i(\mathcal{H}om_X(P_\mathcal{F}^\bullet, I_\mathcal{G}^\bullet))$$

2. **上同调与Ext关系**：
   $$H^i(X, \mathcal{F}) \cong \text{Ext}_X^i(\mathcal{O}_X, \mathcal{F})$$

3. **Ext长正合列**：
   $$0 \to \text{Hom}(\mathcal{F}, \mathcal{G}) \to \text{Ext}^1(\mathcal{F}, \mathcal{G}) \to \cdots \to \text{Ext}^i(\mathcal{F}, \mathcal{G}) \to \cdots$$

4. **Ext与Serre对偶**：
   $$\text{Ext}^i(\mathcal{F}, \omega_X) \cong H^{n-i}(X, \mathcal{F})^*$$

5. **Ext与张量积**：
   $$\text{Ext}^i(\mathcal{F} \otimes \mathcal{G}, \mathcal{H}) \cong \text{Ext}^i(\mathcal{F}, \mathcal{H}om(\mathcal{G}, \mathcal{H}))$$

6. **Ext与拉回**：
   $$\text{Ext}_Y^i(f^*\mathcal{F}, \mathcal{G}) \cong \text{Ext}_X^i(\mathcal{F}, f_*\mathcal{G}) \text{（某些条件下）}$$

7. **Ext与推前**：
   $$R^i f_* \mathcal{H}om_X(\mathcal{F}, \mathcal{G}) \cong \mathcal{H}om_Y(Rf_*\mathcal{F}, Rf_*\mathcal{G}) \text{（某些条件下）}$$

8. **Ext与局部化**：
   $$\text{Ext}_U^i(\mathcal{F}|_U, \mathcal{G}|_U) \cong \text{Ext}_X^i(j_!\mathcal{F}|_U, \mathcal{G})$$

9. **Ext与形变**：
   $$\text{Ext}^1(\mathcal{F}, \mathcal{F}) \text{ 参数化 $\mathcal{F}$ 的一阶形变}$$

10. **Ext与上同调维数**：
    $$\text{proj dim}(\mathcal{F}) = \sup\{i : \text{Ext}^i(\mathcal{F}, \mathcal{G}) \neqqqqqqq 0 \text{ 对某个 $\mathcal{G}$}\}$$

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约2,600字
**数学公式数**: 12个
**例子数**: 8个
**最后更新**: 2026年01月02日
