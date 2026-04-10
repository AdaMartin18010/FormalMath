# Stacks Project Tag 0A1C - 刚性上同调

## 1. 基本概念与定义

### 1.1 刚性上同调的动机

**问题：** 对于特征 $p > 0$ 的代数簇，étale上同调系数有限，无法提供Betti数的完整信息。

**解决方案（Berthelot）：** 刚性上同调 $H^i_{rig}(X)$ ——特征$p$的de Rham上同调类比。

### 1.2 形式定义

**设置：** 设 $k$ 为特征 $p > 0$ 的 perfect 域，$K$ 为 $W(k)[1/p]$（$p$-adic域）。

**定义：** 设 $X$ 为 $k$ 上的光滑概形，$P$ 为 $K$ 上的光滑形式概形使得 $X \hookrightarrow P_k$ 是闭浸入。

**刚性上同调：** $$H^i_{rig}(X/K) = \mathbb{H}^i(]X[_P, j^\dagger \Omega^\bullet_{]X[_P})$$

其中：

- $]X[_P$ 是 $X$ 在 $P$ 中的管状邻域（tube）
- $j^\dagger$ 是特殊化函子
- $\Omega^\bullet$ 是微分形式复形

---

## 2. 数学背景与动机

### 2.1 Weil猜想与上同调理论

**Weil猜想（1949）：** 关于有限域上代数簇的Zeta函数的性质。

**证明历史：**

- **Dwork (1960):** $p$-adic方法证明有理性
- **Grothendieck (1960s):** étale上同调证明大部分（但系数$\mathbb{Q}_\ell$，$\ell \neq p$）
- **Deligne (1974):** 完成Weil猜想的证明

**缺失的部分：** 特征$p$的"integral"上同调理论。

### 2.2 刚性上同调的发展

**Berthelot (1980s):** 创立刚性上同调理论

**关键突破：**

- 提供了特征$p$的de Rham类比
- 与晶体上同调的关系
- 有限维数定理（Kedlaya）

---

## 3. 形式化性质与定理

### 1. 基本性质

**定理（有限生成）：** 对于光滑 $k$-概形 $X$，$H^i_{rig}(X/K)$ 是有限维 $K$-向量空间。

**证明历史：**

- Berthelot：射影情形
- Kedlaya (2006)：一般光滑情形（使用 $p$-adic微分方程）

### 3.2 与晶体上同调的关系

**定理（Berthelot）：** 对于 proper 光滑 $X$：$$H^i_{rig}(X/K) \cong H^i_{crys}(X/W(k)) \otimes_{W(k)} K$$

**推论：** 刚性上同调是晶体上同调的generic fiber。

### 3.3 六个functor的形式主义

**定理：** 刚性上同调满足Grothendieck的六个functor：

- $f^*, f_*, f^!, f_!$
- $\otimes^L, R\mathcal{H}om$

以及 Poincaré 对偶和 Künneth 公式。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Crystalline Cohomology (Chapter 60)
- **前置Tags：**
  - Tag 07MG (晶体上同调)
  - Tag 0A1A (刚性解析空间)

### 4.2 依赖关系

```
Tag 0A1C (刚性上同调)
├── Tag 07MG (晶体上同调)
├── Tag 0A1A (刚性解析)
├── Tag 0F1D (p进微分方程)
└── Tag 0F1E (Riemann-Hilbert)
```

---

## 5. 应用与例子

### 5.1 计算示例

**例1：仿射空间**

$$H^i_{rig}(\mathbb{A}^n_k/K) = \begin{cases} K & i = 0 \\ 0 & i > 0 \end{cases}$$

**例2：乘法群**

$$H^1_{rig}(\mathbb{G}_{m,k}/K) = K \cdot \frac{dt}{t}$$

**例3：超椭圆曲线（Kedlaya算法）**

对于 $y^2 = f(x)$，可以使用Kedlaya算法显式计算刚性上同调。

### 5.2 在数学中的应用

**(1) 韦伊猜想（完整证明）**

刚性上同调提供了特征$p$的cohomological解释，完成Weil猜想的框架。

**(2) Zeta函数计算**

$$Z(X, t) = \prod_{i=0}^{2n} \det(1 - t\cdot Frob | H^i_{rig}(X))^{(-1)^{i+1}}$$

**(3) $p$-adic朗兰兹纲领**

刚性上同调在 $p$-adic Langlands对应中有重要应用。

---

## 6. 与其他概念的联系

### 6.1 上同调理论谱系

```
代数 de Rham
    ↓
晶体上同调 ──→ 刚性上同调
    ↓              ↓
收敛上同调      dagger上同调
    ↓              ↓
刚性上同调 ←── 统一理论
```

### 6.2 特征$p$ vs 特征0

| 特征0 | 特征$p$类比 |
|-------|------------|
| de Rham上同调 | 刚性上同调 |
| 代数构造 | 管状邻域+特殊化 |
| 微分形式 | overconvergent形式 |
| Gauss-Manin | $p$-adic微分方程 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0A1C
- **章节：** Crystalline Cohomology

### 7.2 核心教材

1. **Berthelot, P.** *Cohomologie rigide et cohomologie rigide à supports propres*
   - 刚性上同调的奠基论文

2. **Kedlaya, K.** "Finiteness of rigid cohomology with coefficients"
   - 有限性定理的证明

3. **Le Stum, B.** *Rigid Cohomology*
   - 现代综合处理

### 7.3 计算文献

- **Kedlaya, K.** "Counting points on hyperelliptic curves using Monsky-Washnitzer cohomology"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现

```lean
-- 管状邻域
def Tube {k : Type} [Field k] [CharP k p]
    {K : Type} [pAdicField K] (X : Scheme k)
    (P : FormalScheme K) (i : ClosedImmersion X P.specialFiber) :
    RigidAnalyticSpace K :=
  sorry

-- 刚性上同调
def rigidCohomology {k K : Type} [Field k] [CharP k p]
    [pAdicField K] (X : Scheme k) [Smooth X] (i : ℕ) :
    Module K :=
  Hypercohomology i (Tube X P i) (OverconvergentDeRham (Tube X P i))

-- 有限性定理
theorem rigidCohomology_finiteDimensional {X : Scheme k}
    [Smooth X] [QuasiCompact X] (i : ℕ) :
    FiniteDimensional K (rigidCohomology X i) :=
  sorry
```

### 8.2 形式化挑战

1. **Overconvergent层：** 需要管状邻域上的特殊函数理论
2. **有限性证明：** Kedlaya的复杂论证
3. **六个functor：** 导出范畴的完整形式化

---

## 总结

Tag 0A1C (刚性上同调) 是特征$p$代数几何的核心理论，由Berthelot创立，Kedlaya完善。它填补了étale上同调在特征$p$的空白，为Weil猜想提供了完整的cohomological框架，并在计算数论和$p$-adic Langlands纲领中有重要应用。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第89个*
