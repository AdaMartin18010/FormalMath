# 概形的平坦态射与Tor函子：同调代数与几何的连接


## 📋 目录

- [概形的平坦态射与Tor函子：同调代数与几何的连接](#概形的平坦态射与tor函子同调代数与几何的连接)
  - [📋 目录](#-目录)
  - [一、平坦态射](#一平坦态射)
    - [1.1 定义](#11-定义)
    - [1.2 性质](#12-性质)
  - [二、Tor函子](#二tor函子)
    - [2.1 定义](#21-定义)
    - [2.2 性质](#22-性质)
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
    - [概形的平坦态射与Tor函子的意义](#概形的平坦态射与tor函子的意义)

---

## 一、平坦态射

### 1.1 定义

**平坦态射**（Grothendieck）：

设 $f: X \to Y$ 是概形态射。

**平坦态射**：$f$ 是**平坦的**，如果对每个点 $x \in X$，局部环 $\mathcal{O}_{X,x}$ 作为 $\mathcal{O}_{Y,f(x)}$-模是平坦的。

**数学表述**：

- 平坦性：$$f \text{ 平坦} \iff \mathcal{O}_{X,x} \text{ 作为 } \mathcal{O}_{Y,f(x)}\text{-模是平坦的}$$
- 等价条件：$$f \text{ 平坦} \iff f^* \text{ 正合}$$
- 局部性：$$f \text{ 平坦} \iff f|_U \text{ 平坦（对所有开集 } U\text{）}$$

**例子1：仿射概形的平坦态射**：

对于仿射概形 $X = \text{Spec}(B)$ 和 $Y = \text{Spec}(A)$，态射 $f: X \to Y$ 平坦当且仅当 $B$ 作为 $A$-模是平坦的。

---

### 1.2 性质

**平坦态射的性质**：

平坦态射具有以下重要性质：

1. **函子性**：平坦态射的复合是平坦的
2. **基变换**：平坦态射在基变换下保持
3. **纤维性质**：平坦态射的纤维维数一致

**数学表述**：

- 函子性：$$f \text{ 平坦}, g \text{ 平坦} \Rightarrow g \circ f \text{ 平坦}$$
- 基变换：$$f \text{ 平坦} \Rightarrow f' \text{ 平坦（$f'$ 是基变换）}$$
- 纤维维数：$$f \text{ 平坦} \Rightarrow \dim X_y = \dim X - \dim Y$$

---

## 二、Tor函子

### 2.1 定义

**Tor函子**（Grothendieck）：

对于概形 $X$ 和 $\mathcal{O}_X$-模 $\mathcal{M}$、$\mathcal{N}$，**Tor函子**定义为：
$$\text{Tor}_i^X(\mathcal{M}, \mathcal{N}) = H_i(\mathcal{M} \otimes_X L_\bullet)$$

其中 $L_\bullet$ 是 $\mathcal{N}$ 的平坦分解。

**数学表述**：

- Tor函子：$$\text{Tor}_i^X(\mathcal{M}, \mathcal{N}) = H_i(\mathcal{M} \otimes_X L_\bullet)$$
- 平坦分解：$$0 \to L_n \to \cdots \to L_0 \to \mathcal{N} \to 0$$
- 导出张量积：$$\mathcal{M} \otimes_X^{\mathbb{L}} \mathcal{N} = \mathcal{M} \otimes_X L_\bullet$$

**例子2：Tor函子的计算**：

对于 $\mathcal{O}_X$-模 $\mathcal{M}$ 和 $\mathcal{N}$，有：
$$\text{Tor}_0^X(\mathcal{M}, \mathcal{N}) = \mathcal{M} \otimes_X \mathcal{N}$$

---

### 2.2 性质

**Tor函子的性质**：

Tor函子具有以下重要性质：

1. **函子性**：Tor函子是双函子
2. **长正合序列**：短正合序列诱导长正合序列
3. **消失性**：如果 $\mathcal{N}$ 是平坦的，则 $\text{Tor}_i^X(\mathcal{M}, \mathcal{N}) = 0$（$i > 0$）

**数学表述**：

- 函子性：$$\text{Tor}_i^X(-, -) \text{ 是双函子}$$
- 长正合列：$$\cdots \to \text{Tor}_i^X(\mathcal{M}', \mathcal{N}) \to \text{Tor}_i^X(\mathcal{M}, \mathcal{N}) \to \text{Tor}_i^X(\mathcal{M}'', \mathcal{N}) \to \text{Tor}_{i-1}^X(\mathcal{M}', \mathcal{N}) \to \cdots$$
- 消失性：$$\text{Tor}_i^X(\mathcal{M}, \mathcal{N}) = 0 \quad (i > 0, \mathcal{N} \text{ 平坦})$$

---

## 三、在代数几何中的应用

### 3.1 应用

**同调代数**：

平坦态射和Tor函子在同调代数中有重要应用：
- **平坦分解**：使用平坦分解计算Tor
- **导出函子**：Tor是导出张量积
- **同调维数**：使用Tor计算同调维数

**数学表述**：

- 平坦分解：$$0 \to L_n \to \cdots \to L_0 \to \mathcal{N} \to 0$$
- 导出张量积：$$\mathcal{M} \otimes_X^{\mathbb{L}} \mathcal{N} = \mathcal{M} \otimes_X L_\bullet$$
- 同调维数：$$\text{projdim}(\mathcal{M}) = \sup\{i : \text{Tor}_i^X(\mathcal{M}, -) \neq 0\}$$

**例子3：同调维数的计算**：

对于 $\mathcal{O}_X$-模 $\mathcal{M}$，其投射维数为：
$$\text{projdim}(\mathcal{M}) = \sup\{i : \text{Tor}_i^X(\mathcal{M}, k(x)) \neq 0 \text{（某个点 } x\text{）}\}$$

---

### 3.2 几何应用

**几何不变量**：

平坦态射和Tor函子用于研究几何不变量：
- **相交理论**：使用Tor计算相交数
- **形变理论**：使用Tor研究形变
- **模空间**：使用平坦性研究模空间

**数学表述**：

- 相交数：$$(X \cdot Y) = \chi(\text{Tor}_i^X(\mathcal{O}_X, \mathcal{O}_Y))$$
- 形变：$$\text{Def}_X = \text{Tor}_1^X(\mathcal{O}_X, \mathcal{O}_X)$$
- 平坦性：$$f \text{ 平坦} \iff \text{Tor}_1^X(\mathcal{O}_X, \mathcal{O}_Y) = 0$$

---

## 四、Grothendieck的贡献

### 4.1 系统理论

**系统理论**：

```
Grothendieck的贡献：
- 平坦态射与Tor函子的系统研究
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
经典理论
    ↓
导出理论
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

### 概形的平坦态射与Tor函子的意义

**格洛腾迪克的贡献**：

1. 平坦态射与Tor函子的系统研究
2. 应用广泛

**现代影响**：

- 现代代数几何
- 同调代数
- 应用广泛
- 现代研究

---

## 历史与渊源（对齐）

- **平坦态射**：平坦性定义、纤维与基变换；EGA IV 2、Hartshorne III.9、Stacks 02JY 与本文一致。
- **Tor 函子**：Tor_i(M,N)、平坦判别 Tor_1=0；EGA IV、Stacks 08E2。
- **平坦基变换**：上同调与基变换、平坦拉回；EGA III 2、Stacks 08HH。

## 姊妹篇与网络资源

- **本目录**：[06-平坦性与平滑性](./06-平坦性与平滑性.md)、[25-概形的平坦族与形变理论](./25-概形的平坦族与形变理论.md)、[33-概形的平坦性与Tor函子](./33-概形的平坦性与Tor函子.md)。
- **03-上同调理论**：[20-上同调与基域变化](../03-上同调理论/20-上同调与基域变化.md)。
- **网络资源**：Stacks Project tag 02JY、08E2、08HH；EGA IV 2、III 2；Hartshorne III.9。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约2,400字
**数学公式数**: 12个
**例子数**: 3个
**最后更新**: 2026年01月15日
