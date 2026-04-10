# Stacks Project Tag 01V5 - 光滑态射（Smooth Morphisms）

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01V5 |
| **英文名称** | Smooth Morphisms |
| **所属章节** | Morphisms of Schemes |
| **主题分类** | 代数几何 - 态射性质 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 光滑态射概述

**光滑态射**（Smooth Morphism）是代数几何中"光滑族"概念的相对版本。它推广了：
- 光滑代数簇的概念
- 复几何中的子浸没（submersion）
- 微分几何中的光滑纤维丛

### 2.2 关键定义

**定义 2.2.1**（形式光滑）
态射 $f: X \to S$ 是**形式光滑**（formally smooth）的，如果对于任何仿射 $S$-概形 $T$ 和 $T$ 的闭子概形 $T_0$（由幂零理想定义），映射

$$\text{Hom}_S(T, X) \to \text{Hom}_S(T_0, X)$$

是满射。

**定义 2.2.2**（光滑态射）
态射 $f: X \to S$ 是**光滑**的，如果：
- $f$ 是局部有限展示
- $f$ 是形式光滑的

**定义 2.2.3**（étale态射）
态射 $f: X \to S$ 是**étale**的，如果：
- $f$ 是光滑的
- $f$ 是相对维数0的

等价地，$f$ 是平坦的且 $\Omega_{X/S} = 0$。

**定义 2.2.4**（相对维数）
光滑态射 $f: X \to S$ 的**相对维数** $d$ 是纤维 $X_s$ 的维数（在光滑点处是常数）。

等价地，$\Omega_{X/S}$ 是秩 $d$ 的局部自由层。

### 2.3 切空间与微分

**定义 2.3.1**（相对微分模）
**相对微分模** $\Omega_{X/S}$ 定义为：

$$\Omega_{X/S} = \Delta^* \mathcal{I}/\mathcal{I}^2$$

其中 $\Delta: X \to X \times_S X$ 是对角线，$\mathcal{I}$ 是对角线的理想层。

**定义 2.3.2**（切层）
**相对切层**（或相对导子层）定义为：

$$\mathcal{T}_{X/S} = \mathcal{H}om_{\mathcal{O}_X}(\Omega_{X/S}, \mathcal{O}_X)$$

对于光滑态射，$\mathcal{T}_{X/S}$ 是局部自由的。

---

## 3. 主要结果与定理

### 3.1 光滑态射的基本性质

**定理 3.1.1**（Tag 01V5）
光滑态射满足以下性质：

**(a) 复合性**
若 $f: X \to Y$ 和 $g: Y \to Z$ 是光滑的，则 $g \circ f: X \to Z$ 是光滑的。

**(b) 基变换**
若 $f: X \to S$ 是光滑的，$S' \to S$ 是任意态射，则基变换 $f': X \times_S S' \to S'$ 是光滑的。

**(c) 局部结构**
光滑态射 $f: X \to S$ 在点 $x \in X$ 处局部可分解为：

$$X \xrightarrow{\text{étale}} \mathbb{A}^d_S \to S$$

其中 $\mathbb{A}^d_S$ 是仿射空间，$d$ 是相对维数。

**(d) 纤维性质**
光滑态射的纤维是光滑概形（在剩余域上是正则的）。

### 3.2 判别准则

**定理 3.2.1**（Jacobi判别法）
设 $f: X \to S$ 局部有限展示，$x \in X$，$s = f(x)$。

则 $f$ 在 $x$ 处光滑当且仅当：
- $f$ 在 $x$ 处平坦
- 纤维 $X_s$ 在 $x$ 处光滑
- 等价地，Jacobian矩阵满秩

**定理 3.2.2**（微分判别法）
$f$ 是相对维数 $d$ 的光滑态射当且仅当：
- $f$ 是局部有限展示的
- $\Omega_{X/S}$ 是秩 $d$ 的局部自由层

### 3.3 与其他态射的关系

**定理 3.3.1**

| 态射类型 | 包含关系 |
|---------|---------|
| 局部自由态射 | $\subset$ 光滑态射 |
| étale态射 | $\subset$ 光滑态射（维数0） |
| 光滑态射 | $\subset$ 平坦态射 |
| 平坦态射 | $\subset$ 开态射 |

**定理 3.3.2**（光滑模概形的结构）
设 $G \to S$ 是光滑群概形，则：
- $G$ 局部是 $S$ 上的线性群
- 若 $G$ 是交换的且真，则 $G$ 是Abel概形

---

## 4. 证明思路

### 4.1 形式光滑性的提升性质

**核心观察**：
形式光滑性对应于无穷小提升问题：

$$\begin{array}{ccc}
T_0 & \to & X \\
\downarrow & \nearrow & \downarrow \\
T & \to & S
\end{array}$$

光滑性保证这种提升存在。

### 4.2 局部结构的证明

**步骤1**：约化到仿射情形
- $X = \text{Spec}(B)$，$S = \text{Spec}(A)$
- $B$ 是有限展示 $A$-代数

**步骤2**：选择坐标
- 由于 $\Omega_{B/A}$ 局部自由，选择基
- 构造映射 $A[x_1, \ldots, x_d] \to B$

**步骤3**：étale性验证
- 验证诱导的映射是étale的
- 使用Jacobian判别法

### 4.3 纤维光滑性的证明

**技术步骤**：
1. 光滑性蕴含局部有限展示
2. 纤维上的微分形式与相对微分形式的关系
3. 正则性来自Jacobian判别的满秩条件

---

## 5. 应用与例子

### 5.1 基本例子

**例子 5.1.1**（仿射空间）
投影 $\mathbb{A}^n_S \to S$ 是光滑的，相对维数 $n$。

**例子 5.1.2**（射影空间丛）
若 $\mathcal{E}$ 是 $S$ 上的局部自由层，则：

$$\mathbb{P}(\mathcal{E}) \to S$$

是光滑的，相对维数 $\text{rank}(\mathcal{E}) - 1$。

**例子 5.1.3**（Abel概形）
Abel概形 $A \to S$（真光滑群概形）是光滑的。

**例子 5.1.4**（光滑超曲面）
$\mathbb{P}^n$ 中光滑超曲面 $X$ 到 $\text{Spec}(k)$ 是光滑的。

### 5.2 形变理论

**应用 5.2.1**（形变的存在性）
设 $X_0/k$ 是光滑真簇，$A' \to A$ 是Artin局部环的小扩张。

若 $X/A$ 是 $X_0$ 的形变，则光滑性保证：
- 形变函子是光滑的（无阻碍）
- $H^2(X_0, T_{X_0}) = 0$ ⟹ 形变存在

### 5.3 上同调中的应用

**应用 5.3.1**（光滑基变换）
对于光滑态射的交换图：

$$\begin{array}{ccc}
X' & \to & X \\
\downarrow & & \downarrow \\
S' & \to & S
\end{array}$$

光滑基变换定理给出：

$$g^* R^i f_* \mathcal{F} \cong R^i f'_* (g')^* \mathcal{F}$$

### 5.4 代数拓扑的联系

**应用 5.4.1**（特征类）
对于光滑簇 $X$，有**切丛** $T_X$，可定义：
- Chern类 $c_i(X) = c_i(T_X)$
- Todd类 $\text{td}(X)$
- Pontryagin类（对于实向量丛）

---

## 6. 与其他概念的关系

### 6.1 态射的层次结构

```
        局部自由态射
               │
               ▼
          光滑态射
               │
       ┌───────┴───────┐
       │               │
       ▼               ▼
   étale态射      平坦态射
   (维数0)            │
                      ▼
                  开态射
```

### 6.2 与微分几何的比较

| 代数几何 | 微分几何 |
|---------|---------|
| 光滑态射 | 子浸没（submersion） |
| étale态射 | 局部微分同胚 |
| 相对切层 | 相对切丛 |
| 微分形式 | 微分形式 |
| 光滑纤维 | 光滑纤维 |

### 6.3 与复几何的关系

对于复代数簇，光滑态射对应于：
- 全纯子浸没
- 微分纤维化的全纯版本
- 族的结构定理（Ehresmann定理的代数版本）

---

## 7. 参考文献

### 7.1 原始文献

1. **Grothendieck, A.** (1960s). *EGA IV*
   - Pub. Math. IHÉS 20, 24, 28, 32
   - 光滑态射的系统理论

2. **Grothendieck, A.** (1960s). *SGA 1: Revêtements étales et groupe fondamental*
   - étale态射的理论

### 7.2 教科书

3. **Hartshorne, R.** (1977). *Algebraic Geometry*
   - Springer GTM 52
   - 第III章：光滑态射

4. **Liu, Q.** (2002). *Algebraic Geometry and Arithmetic Curves*
   - Oxford University Press
   - 第6章

5. **Vakil, R.** (2017). *The Rising Sea: Foundations of Algebraic Geometry*
   - 在线讲义，现代处理

### 7.3 技术参考

6. **Matsumura, H.** (1986). *Commutative Ring Theory*
   - 光滑性的代数基础

7. **Bosch, S., Lütkebohmert, W., Raynaud, M.** (1990). *Néron Models*
   - 光滑群概形的详细处理

### 7.4 在线资源

8. **Stacks Project**: [Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
9. **Stacks Project**: [Chapter Morphisms](https://stacks.math.columbia.edu/chapter/01QY)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [01TZ](#tag-01tz) | étale态射 | 特例 |
| [01U2](#tag-01u2) | 平坦态射 | 包含关系 |
| [01VC](#tag-01vc) | 非ramified态射 | 相关概念 |

### 8.2 微分理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [01UM](#tag-01um) | 微分模 | 技术工具 |
| [01US](#tag-01us) | 切层 | 几何解释 |
| [02G1](#tag-02g1) | 光滑覆叠 | 应用 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0B8W](#tag-0b8w) | 形变理论 | 主要应用 |
| [0C0K](#tag-0c0k) | 光滑基变换 | 上同调应用 |
| [0C0L](#tag-0c0l) | 基本群 | 几何应用 |

---

## 附录：判别准则速查

### Jacobi判别法（局部形式）

设 $X = \text{Spec}(k[x_1, \ldots, x_n]/(f_1, \ldots, f_r))$，$P \in X$。

$X$ 在 $P$ 处光滑当且仅当：

$$\text{rank}\left(\frac{\partial f_i}{\partial x_j}(P)\right) = r$$

### 维数公式

对于光滑态射 $f: X \to S$：

$$\dim_x X = \dim_{f(x)} S + d$$

其中 $d$ 是在 $x$ 处的相对维数。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
