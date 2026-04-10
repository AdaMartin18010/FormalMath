# Stacks Project Tag 03QY - Étale上同调与极限交换

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 03QY |
| **英文名称** | Étale Cohomology Commutes with Limits |
| **所属章节** | Theorem on Formal Functions |
| **主题分类** | 代数几何 - 极限与上同调 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 极限与上同调交换问题

在代数几何中，经常需要研究**逆系统**（inverse system）的极限与上同调的关系。这种交换性是许多重要结果（如形式函数定理）的基础。

### 2.2 关键定义

**定义 2.2.1**（逆系统）
范畴 $\mathcal{C}$ 中的**逆系统** $(A_i, \varphi_{ij})$ 包含：
- 对象族 $\{A_i\}_{i \in I}$，其中 $I$ 是有向集
- 转移态射 $\varphi_{ij}: A_j \to A_i$（对于 $i \leq j$）

满足：$\varphi_{ii} = \text{id}$，$\varphi_{ij} \circ \varphi_{jk} = \varphi_{ik}$

**定义 2.2.2**（概形的逆极限）
对于概形逆系统 $\{X_i\}$，其**逆极限** $X = \varprojlim X_i$ 是泛性质定义的对象：

$$\text{Hom}(T, X) \cong \varprojlim \text{Hom}(T, X_i)$$

**定义 2.2.3**（层的逆极限）
对于层逆系统 $\{\mathcal{F}_i\}$ 在 $X$ 上，定义：

$$(\varprojlim \mathcal{F}_i)(U) := \varprojlim \mathcal{F}_i(U)$$

### 2.4 特殊极限类型

**定义 2.4.1**（完备化）
设 $X$ 是诺特概形，$Z \subseteq X$ 是闭子集，$\mathcal{I}$ 是理想层。$X$ 沿 $Z$ 的**形式完备化**定义为：

$$\hat{X} = \varprojlim X_n, \quad X_n = V(\mathcal{I}^{n+1})$$

---

## 3. 主要结果与定理

### 3.1 极限交换定理

**定理 3.1.1**（Tag 03QY）
设 $\{X_i\}_{i \in I}$ 是拟紧且拟分离概形的逆系统，转移态射为仿射的。设 $X = \varprojlim X_i$，$\mathcal{F}_i$ 是 $X_i$ 上的Abel群层，满足转移映射 $\mathcal{F}_j \to f_{ij*}\mathcal{F}_i$。

则对任意 $q \geq 0$：

$$\boxed{H^q_{\text{ét}}(X, \varprojlim \mathcal{F}_i) \cong \varprojlim H^q_{\text{ét}}(X_i, \mathcal{F}_i)}$$

**推论 3.1.2**
在上述条件下，若所有 $\mathcal{F}_i$ 是挠层（$\ell$-进系数），则同构成立。

### 3.2 形式函数定理

**定理 3.2.1**（Grothendieck形式函数定理）
设 $f: X \to Y$ 是真态射，$\mathcal{F}$ 是 $X$ 上的凝聚层，$y \in Y$。设 $\mathfrak{m}$ 是 $y$ 的极大理想，$\hat{\mathcal{O}}_{Y,y}$ 是完备化。

则对任意 $q \geq 0$：

$$R^q f_*\mathcal{F} \otimes_{\mathcal{O}_Y} \hat{\mathcal{O}}_{Y,y} \cong \varprojlim H^q(X_n, \mathcal{F}_n)$$

其中 $X_n = X \times_Y \text{Spec}(\mathcal{O}_{Y,y}/\mathfrak{m}^{n+1})$。

### 3.3 比较定理

**定理 3.3.1**（代数与解析比较）
设 $X$ 是复代数簇，$\hat{X}$ 是沿闭子簇的完备化，则：

$$H^q_{\text{ét}}(\hat{X}, \mathbb{Z}/n\mathbb{Z}) \cong \varprojlim H^q_{\text{ét}}(X_n, \mathbb{Z}/n\mathbb{Z}) \cong H^q_{\text{sing}}(X(\mathbb{C})^{\text{an}}, \mathbb{Z}/n\mathbb{Z})$$

---

## 4. 证明思路

### 4.1 核心证明策略

**步骤1**：Čech上同调逼近
- 对有限仿射覆盖使用Čech上同调
- 利用拟紧性约化到有限情形

**步骤2**：层上同调的可计算性
- 证明 $\varprojlim$ 保持内射对象（在适当意义下）
- 使用Flasque分解

**步骤3**：拓扑论证
- 利用 $X$ 的拓扑可由 $X_i$ 的拓扑逼近
- Étale拓扑的有限性性质

### 4.2 关键引理

**引理 4.2.1**（Mittag-Leffler条件）
若上同调系统满足**Mittag-Leffler条件**（最终稳定），则 $\varprojlim^1$ 消失，从而：

$$R^q \varprojlim = 0, \quad q > 0$$

**引理 4.2.2**（有限性控制）
对于诺特概形和凝聚层，$H^q_{\text{ét}}(X_i, \mathcal{F}_i)$ 是有限生成模。

### 4.3 形式函数定理的证明

**核心观察**：
1. $R^q f_*\mathcal{F}$ 是凝聚层（由Grauert定理）
2. 沿纤维的完备化对应于逆极限
3. 基变换与极限交换

---

## 5. 应用与例子

### 5.1 形式概形的上同调

**例子 5.1.1**（形式射影空间）
设 $\hat{\mathbb{P}}^n = \varprojlim \mathbb{P}^n_k$（形式完备化），则：

$$H^q_{\text{ét}}(\hat{\mathbb{P}}^n, \mathbb{Z}/\ell^m\mathbb{Z}) = \begin{cases} \mathbb{Z}/\ell^m\mathbb{Z} & q \text{ 偶数}, 0 \leq q \leq 2n \\ 0 & \text{否则} \end{cases}$$

这与通常射影空间的上同调结构相同。

### 5.2 形变理论中的应用

**应用 5.2.1**（Kodaira-Spencer理论）
设 $X \to S$ 是光滑族，$0 \in S$ 是闭点。形式完备化 $\hat{X}$ 控制无穷小形变。

极限交换定理给出：

$$H^1(\hat{X}, T_{\hat{X}}) \cong \varprojlim H^1(X_n, T_{X_n})$$

这是形变函子的切空间。

### 5.3 刚性解析几何

**例子 5.3.1**（Tate曲线）
Tate曲线的刚性解析构造：

$$E_q^{\text{rig}} = \mathbb{G}_m^{\text{rig}}/q^{\mathbb{Z}}$$

其中极限过程用于从代数簇过渡到刚性解析空间。

### 5.4 $p$-进Hodge理论

**应用 5.4.1**（比较同构）
在$p$-进Hodge理论中，极限交换用于建立：

$$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{C}_K \cong \bigoplus_j H^{i-j}(X, \Omega^j_X) \otimes_K \mathbb{C}_K(j)$$

---

## 6. 与其他概念的关系

### 6.1 极限类型的谱系

```
            上同调极限交换
                   │
      ┌────────────┼────────────┐
      │            │            │
      ▼            ▼            ▼
  形式函数定理  Mittag-Leffler  完备化理论
      │            │            │
      ├────────────┴────────────┤
      │                         │
      ▼                         ▼
  形变理论              刚性/形式几何
      │                         │
      └──────────┬──────────────┘
                 ▼
          算术几何应用
```

### 6.2 与导出完备化的关系

在现代导出代数几何中，极限被**导出完备化**（derived completion）取代：

$$R\varprojlim: D(X_{\text{ét}})^I \to D(X_{\text{ét}})$$

这提供了更精细的控制，特别是对于 $R^1\varprojlim$。

### 6.3 与pro-étale上同调的关系

**pro-étale上同调**（Bhatt-Scholze）通过允许更一般的极限构造，将极限交换性内建到理论中：

$$H^i_{\text{pro-ét}}(X, \hat{\mathbb{Z}}_p) = H^i_{\text{ét}}(X, \mathbb{Z}_p)$$

---

## 7. 参考文献

### 7.1 原始文献

1. **Grothendieck, A.** (1961). *Éléments de géométrie algébrique III*
   - Pub. Math. IHÉS 11, 17
   - 形式函数定理的原始证明

2. **Grothendieck, A.** (1960s). *SGA 1: Revêtements étales et groupe fondamental*
   - 极限与基本群的关系

### 7.2 现代发展

3. **Bhatt, B.** (2014). *Algebraization and Tannaka duality*
   - 导出完备化的系统研究

4. **Bhatt, B. & Scholze, P.** (2015). *The pro-étale topology*
   - 极限交换的内建处理

### 7.3 应用文献

5. **Serre, J.-P.** (1956). *Géométrie algébrique et géométrie analytique*
   - GAGA原理，比较定理

6. **Tate, J.** (1971). *Rigid analytic spaces*
   - 刚性几何中的极限

### 7.4 在线资源

7. **Stacks Project**: [Tag 03QY](https://stacks.math.columbia.edu/tag/03QY)
8. **Stacks Project**: [Tag 0A07](https://stacks.math.columbia.edu/tag/0A07) (形式函数定理)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [03QP](#tag-03qp) | Étale上同调基础 | 理论基础 |
| [03QU](#tag-03qu) | 函子性 | 技术工具 |
| [0A07](#tag-0a07) | 形式函数定理 | 主要应用 |
| [09ZR](#tag-09zr) | 导出完备化 | 现代版本 |

### 8.2 进阶主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0DAG](#tag-0dag) | 形式概形 | 几何背景 |
| [0F4N](#tag-0f4n) | 刚性解析空间 | 非Archimedean几何 |
| [0GHZ](#tag-0ghz) | 完备化与基变换 | 技术工具 |

### 8.3 应用领域

| Tag | 主题 | 说明 |
|-----|------|------|
| [0DJN](#tag-0djn) | 形变理论 | 主要应用 |
| [0FK9](#tag-0fk9) | Kodaira-Spencer映射 | 具体实例 |
| [0GJF](#tag-0gjf) | 代数化定理 | 逆向问题 |

---

## 附录：技术细节

### Mittag-Leffler条件详解

**定义**：逆系统 $(A_n)$ 满足Mittag-Leffler条件，如果对所有 $n$，像序列

$$\text{Im}(A_{n+k} \to A_n)$$

最终稳定。

**重要性**：
$$R^1\varprojlim = 0 \Leftarrow \text{Mittag-Leffler条件}$$

### 导出极限

对于复形的逆系统，使用：

$$R\varprojlim K_n^\bullet \cong \text{holim} K_n^\bullet$$

其中 $\text{holim}$ 是同伦极限。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
