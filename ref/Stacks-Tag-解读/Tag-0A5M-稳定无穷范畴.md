# Stacks Project Tag 0A5M - 稳定∞-范畴

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0A5M |
| **英文名称** | Stable ∞-Categories |
| **所属章节** | Derived Categories |
| **主题分类** | 高阶范畴论 - 同调代数 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 稳定性概念的动机

**稳定∞-范畴**（Stable ∞-Category）是代数拓扑和同调代数中高阶结构的抽象框架。它统一了：
- 谱（Spectra）的稳定同伦范畴
- 链复形的导出范畴
- 凝聚层的导出范畴

### 2.2 关键定义

**定义 2.2.1**（∞-范畴）
一个**∞-范畴**（或准范畴，quasi-category）是一个单纯集 $\mathcal{C}$，满足**内Kan条件**：

对于 $0 < i < n$，任何角 $\Lambda^n_i \to \mathcal{C}$ 可填充为 $n$-单形 $\Delta^n \to \mathcal{C}$。

**定义 2.2.2**（零对象）
在具有有限极限和余极限的∞-范畴中，**零对象** $0$ 是既是初始对象又是终末对象的对象。

**定义 2.2.3**（纤维和余纤维）
对于态射 $f: X \to Y$：
- **纤维**（fiber）：$\text{fib}(f) = X \times_Y 0$
- **余纤维**（cofiber）：$\text{cofib}(f) = Y \amalg_X 0$

**定义 2.2.4**（稳定∞-范畴）
一个**稳定∞-范畴**是满足以下等价条件的∞-范畴 $\mathcal{C}$：

**(a)** 存在零对象，且每个正方形
$$\begin{array}{ccc}
X & \to & Y \\
\downarrow & & \downarrow \\
0 & \to & Z
\end{array}$$
是推出当且仅当它是拉回（推出=拉回的正方形称为**双笛卡尔**）。

**(b)** 平移函子 $\Sigma: \mathcal{C} \to \mathcal{C}$ 是等价。

**(c)** 有限极限和余极限存在，且纤维和余纤维是互逆运算。

### 2.3 三角结构

**定义 2.3.1**（正合三角形）
在稳定∞-范畴中，一个**正合三角形**是形如

$$X \xrightarrow{f} Y \xrightarrow{g} Z \xrightarrow{h} X[1]$$

的图表，其中 $Z \cong \text{cofib}(f)$ 且 $X[1] = \Sigma X$。

**命题 2.3.2**
稳定∞-范畴的同伦范畴 $h\mathcal{C}$ 是**三角范畴**。

---

## 3. 主要结果与定理

### 3.1 稳定性的刻画

**定理 3.1.1**（Tag 0A5M）
设 $\mathcal{C}$ 是带有有限极限和余极限的∞-范畴。以下等价：

**(a)** $\mathcal{C}$ 是稳定的。

**(b)** 纤维序列和余纤维序列重合。

**(c)** 存在等价 $h\mathcal{C} \cong D^b(\mathcal{A})$ 对某个Abel范畴 $\mathcal{A}$（局部）。

**(d)** 对任何对象 $X$，自然映射 $X \to \Omega\Sigma X$ 是等价。

### 3.2 稳定∞-范畴的构造

**定理 3.2.1**（谱的∞-范畴）
**谱的∞-范畴** $\text{Sp}$ 是稳定的：

- 对象是**谱**（Ω-谱）：序列 $(E_0, E_1, \ldots)$ 带有 $E_n \cong \Omega E_{n+1}$
- 态射谱是映射谱

**定理 3.2.2**（导出∞-范畴）
对于Abel范畴 $\mathcal{A}$，其**导出∞-范畴** $D(\mathcal{A})$ 是稳定的：

- 对象是链复形 $C_\bullet$
- 态射是链映射的同伦类
- 平移：$C[1]_n = C_{n-1}$

### 3.3 伴随与正合性

**定理 3.3.1**
设 $F: \mathcal{C} \to \mathcal{D}$ 是稳定∞-范畴之间的伴随：

$$F \dashv G$$

则以下等价：

- $F$ 保持余纤维序列（左正合）
- $G$ 保持纤维序列（右正合）
- $(F, G)$ 是$t$-正合对

---

## 4. 证明思路

### 4.1 稳定性条件的等价性

**步骤1**：(a) ⟹ (b)
- 在稳定范畴中，$\text{fib}(f) \to X \to Y \to \text{cofib}(f)$
- 由双笛卡尔性质，$\text{fib}(f) \cong \Omega\text{cofib}(f)$

**步骤2**：(b) ⟹ (c)
- 构造$h$-范畴的三角结构
- 验证Verdier的公理

**步骤3**：(c) ⟹ (a)
- 从三角结构重建∞-范畴结构
- 验证推出=拉回

### 4.2 谱范畴的稳定性

**核心观察**：
对于谱 $E$，其Ω-结构给出：

$$E_n \cong \Omega E_{n+1} \cong \Omega^2 E_{n+2} \cong \cdots$$

这确保了$\Sigma$和$\Omega$是互逆的（在同伦意义下）。

### 4.3 导出范畴的构造

**技术步骤**：
1. 从链复形范畴 $Ch(\mathcal{A})$ 开始
2. 局部化拟同构
3. 证明结果范畴是稳定的
4. 验证同伦范畴是经典导出范畴

---

## 5. 应用与例子

### 5.1 基本例子

**例子 5.1.1**（谱范畴 $\text{Sp}$）
稳定同伦论的基本范畴。

关键性质：
- $\pi_n(E) = [S^n, E]$ 是稳定同伦群
-  smash积 $E \wedge F$ 给出张量结构

**例子 5.1.2**（导出范畴 $D(R)$）
环 $R$ 的导出∞-范畴。

- 对象是微分分次$R$-模
- 可计算Tor和Ext：$\text{Tor}^R_n(M, N) = \pi_n(M \otimes_R^L N)$

**例子 5.1.3**（凝聚层的导出范畴）
对于概形 $X$，$D_{\text{coh}}^b(X)$ 是稳定的。

### 5.2 代数K-理论

**应用 5.2.1**
稳定∞-范畴是代数K-理论的天然定义域：

$$K(\mathcal{C}) = \Omega^\infty|S_\bullet \mathcal{C}^\simeq|$$

其中 $S_\bullet$ 是Waldhausen的$S$-构造。

### 5.3 代数几何中的应用

**例子 5.3.1**（Grothendieck六运算）
对于态射 $f: X \to Y$，在稳定∞-范畴 $D_{\text{qc}}(X)$ 上：

- $(f^*, f_*)$ 伴随
- $(f_!, f^!)$ 伴随（对于proper态射）
- 张量积 $\otimes$ 和内部Hom

这六种运算在导出∞-范畴中有自然的提升。

### 5.4 拓扑Hochschild同调

**应用 5.4.1**（THH）
稳定∞-范畴上的循环同调：

$$\text{THH}(\mathcal{C}) = \text{colim}_{\Delta^{\text{op}}} \text{Map}(S^1, \mathcal{C}^{\otimes n})$$

这是代数几何和拓扑的深刻联系。

---

## 6. 与其他概念的关系

### 6.1 范畴理论的谱系

```
        经典范畴
           │
           │ 高阶化
           ▼
        ∞-范畴
           │
           │ 稳定化
           ▼
      稳定∞-范畴
           │
     ┌─────┴─────┐
     │           │
     ▼           ▼
  谱范畴      导出范畴
  (拓扑)      (代数)
     │           │
     └─────┬─────┘
           ▼
      模空间理论
```

### 6.2 与三角范畴的关系

稳定∞-范畴的同伦范畴是三角范畴，但稳定∞-范畴包含更多信息：

| 三角范畴 | 稳定∞-范畴 |
|---------|-----------|
| 同伦类映射 | 高阶同伦 |
| 映射锥（同伦类） | 映射锥（典范） |
| 正合三角形 | 纤维序列 |
| 高阶结构丢失 | 完全保留 |

### 6.3 与模型范畴的关系

**谱模型范畴**呈现稳定∞-范畴：

- 谱的模型范畴 → $L_W(\mathcal{M}) \cong \text{Sp}$
- 链复形的模型范畴 → $L_W(Ch) \cong D(\mathcal{A})$

---

## 7. 参考文献

### 7.1 奠基文献

1. **Lurie, J.** (2006). *Stable ∞-Categories*
   - arXiv:math/0608228
   - 系统理论建立

2. **Lurie, J.** (2017). *Higher Algebra*
   - 第1章
   - 全面参考

3. **Boardman, J.M. & Vogt, R.M.** (1973). *Homotopy Invariant Algebraic Structures*
   - 准范畴的早期工作

### 7.2 经典参考

4. **Verdier, J.-L.** (1963). *Des catégories dérivées des catégories abéliennes*
   - 三角范畴的原始工作

5. **Quillen, D.** (1967). *Homotopical Algebra*
   - 模型范畴

### 7.3 现代应用

6. **Blumberg, A., Gepner, D., Tabuada, G.** (2013). *A universal characterization of higher algebraic K-theory*
   - 稳定∞-范畴的K-理论

7. **Antieau, B., Nikolaus, T., Venjakob, O.** (2021). *On the Beilinson fiber square*
   - 代数几何应用

### 7.4 在线资源

8. **Stacks Project**: [Tag 0A5M](https://stacks.math.columbia.edu/tag/0A5M)
9. **Kerodon**: [Stable ∞-Categories](https://kerodon.net/)
10. **nLab**: [stable (∞,1)-category](https://ncatlab.org/nlab/show/stable+%28infinity%2C1%29-category)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0A5N](#tag-0a5n) | 谱与环谱 | 具体实现 |
| [0A5O](#tag-0a5o) | 导出范畴 | 经典对应 |
| [0G6U](#tag-0g6u) | 三角范畴 | 同伦范畴 |

### 8.2 ∞-范畴基础

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G6V](#tag-0g6v) | ∞-范畴基础 | 预备知识 |
| [0G6W](#tag-0g6w) | 极限与余极限 | 技术工具 |
| [0G6X](#tag-0g6x) | 伴随函子 | 结构理论 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G6Y](#tag-0g6y) | 代数K-理论 | 主要应用 |
| [0G6Z](#tag-0g6z) | THH/TC | 拓扑应用 |
| [0G70](#tag-0g70) | 导出代数几何 | 几何应用 |

---

## 附录：关键公式

### 稳定同伦群的计算

对于谱 $E$：

$$\pi_n(E) = \text{colim}_k \pi_{n+k}(E_k)$$

### 导出张量积

对于链复形：

$$(C \otimes^L D)_n = \bigoplus_{i+j=n} C_i \otimes D_j$$

微分：$d(c \otimes d) = dc \otimes d + (-1)^{|c|}c \otimes dd$

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
