# Stacks Project Tag 0E7N - 导出Hilbert概形

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0E7N |
| **英文名称** | Derived Hilbert Schemes |
| **所属章节** | Derived Algebraic Geometry |
| **主题分类** | 高阶代数几何 - 导出模空间 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 历史背景与动机

**导出Hilbert概形**（Derived Hilbert Schemes）是经典Hilbert概形的导出推广，由Toën-Vezzosi和Lurie独立发展。它解决经典Hilbert概形的**奇异性问题**，为模空间理论提供了更自然的框架。

**核心问题**：经典Hilbert概形往往是奇异的，其奇点反映了几何的「高阶」信息。导出Hilbert概形通过引入**导出结构**，使这些高阶信息内在化。

### 2.2 经典Hilbert概形回顾

**定义 2.2.1**（Hilbert函子）
对于射影簇 $X/\mathbb{C}$，**Hilbert函子**定义为：
$$\text{Hilb}_X: \text{Sch}^{\text{op}} \to \text{Set}$$
$$S \mapsto \{\text{闭子概形 } Z \subset X \times S \text{，平坦}/S\}$$

**定义 2.2.2**（Hilbert概形）
**Hilbert概形** $\text{Hilb}_X$ 是表示Hilbert函子的概形（Grothendieck）。

**定理 2.2.3**（存在性）
$\text{Hilb}_X$ 存在且是局部有限型概形。

**问题 2.2.4**：$\text{Hilb}_X$ 通常是**奇异**的。

### 2.3 导出Hilbert函子

**定义 2.3.1**（单纯交换环）
**单纯交换环**是函子：
$$A_\bullet: \Delta^{\text{op}} \to \text{CRing}$$
满足单纯关系。

**定义 2.3.2**（导出环）
**导出环**是单纯交换环的同伦等价类，形成**导出仿射概形**的坐标环。

**定义 2.3.3**（导出Hilbert预层）
**导出Hilbert预层**定义为：
$$\text{dHilb}_X: \text{dAff}^{\text{op}} \to \mathcal{S}$$
$$A \mapsto \{\text{闭浸入 } Z \hookrightarrow X \times \text{Spec}(A) \text{（导出意义）}\}$$

**定义 2.3.4**（导出闭子概形）
**导出闭子概形**是态射 $i: Z \to X$ 使得：

- $i$ 是仿射态射
- 诱导的 $\mathcal{O}_X \to i_*\mathcal{O}_Z$ 是满射（在导出意义下）

### 2.4 导出Hilbert概形

**定义 2.4.1**（导出Hilbert概形）
**导出Hilbert概形** $\text{dHilb}_X$ 是导出栈（derived stack），满足：

- 截断 $t_0(\text{dHilb}_X) = \text{Hilb}_X$（经典Hilbert概形）
- 配备自然的导出结构

**定义 2.4.2**（切复形）
在点 $[Z \subset X] \in \text{dHilb}_X$，**切复形**为：
$$\mathbb{T}_{[Z]} \text{dHilb}_X \cong R\text{Hom}_Z(\mathcal{I}_Z, \mathcal{O}_Z)[1]$$
其中 $\mathcal{I}_Z$ 是理想层。

**定义 2.4.3**（导出Hilbert概形的结构）
导出Hilbert概形是**导出代数空间**（derived algebraic space），局部形式为：
$$\text{Spec}(A), \quad A \text{ 是单纯交换环}$$

---

## 3. 主要结果与定理

### 3.1 存在性定理

**定理 3.1.1**（Tag 0E7N - 导出Hilbert概形）
设 $X$ 是光滑射影簇，则：

**(a) 存在性**
导出Hilbert概形 $\text{dHilb}_X$ 存在且是**局部几何导出代数空间**。

**(b) 表示性**
$\text{dHilb}_X$ 表示导出Hilbert函子：
$$\text{Map}(S, \text{dHilb}_X) \cong \{\text{闭浸入 } Z \hookrightarrow X \times S\}$$
对所有导出概形 $S$。

**(c) 截断兼容性**
$$t_0(\text{dHilb}_X) \cong \text{Hilb}_X$$

### 3.2 切复形与阻碍理论

**定理 3.2.1**（切复形公式）
对于点 $[Z] \in \text{dHilb}_X$：
$$\mathbb{T}_{[Z]} \cong R\Gamma(Z, \mathcal{N}_{Z/X})$$
其中 $\mathcal{N}_{Z/X} = \mathcal{H}om(\mathcal{I}_Z/\mathcal{I}_Z^2, \mathcal{O}_Z)$ 是法丛。

**定理 3.2.2**（阻碍理论）
导出Hilbert概形携带自然的**完美阻碍理论**（perfect obstruction theory）：
$$\mathbb{E}_{[Z]} := R\Gamma(Z, \mathcal{N}_{Z/X})^\vee[-1]$$

**推论 3.2.3**（虚维数）
导出Hilbert概形有**虚维数**：
$$\text{vdim}(\text{dHilb}_X^{P}) = \chi(\mathcal{N}_{Z/X})$$
其中 $P$ 是Hilbert多项式。

### 3.3 与经典Hilbert概形的关系

**定理 3.3.1**（光滑性判定）
经典Hilbert概形在 $[Z]$ 光滑当且仅当：
$$H^1(Z, \mathcal{N}_{Z/X}) = 0$$
等价地，导出Hilbert概形在 $[Z]$ 是「经典」的（无导出方向）。

**定理 3.3.2**（奇点解释）
经典Hilbert概形的奇点由导出Hilbert概形的**高阶同伦**编码：
$$\pi_i(\text{dHilb}_X, [Z]) \cong H^{1-i}(Z, \mathcal{N}_{Z/X}), \quad i > 0$$

### 3.4 模空间的性质

**定理 3.4.1**（紧性）
若 $X$ 是射影的，则 $\text{dHilb}_X$ 在导出意义下**局部紧**。

**定理 3.4.2**（通用族）
存在**通用导出族**：
$$\mathcal{Z} \subset X \times \text{dHilb}_X$$
平坦于 $\text{dHilb}_X$。

---

## 4. 证明思路

### 4.1 ∞-范畴框架

**步骤1**：导出环的模
导出环 $A$ 的模形成**稳定∞-范畴** $\text{Mod}_A$。

**步骤2**：导出概形
导出概形是环化空间 $(X, \mathcal{O}_X)$，其中 $\mathcal{O}_X$ 取值于导出环。

**步骤3**：导出浸入
态射 $Z \to X$ 是**闭浸入**如果：

- 拓扑上是闭浸入
- $\mathcal{O}_X \to f_*\mathcal{O}_Z$ 是满射

### 4.2 Hilbert函子的导出化

**步骤1**：几何实现
将Hilbert条件几何化：子概形 = 商层 = 投射对象。

**步骤2**：导出商
在导出范畴中构造商：
$$\mathcal{O}_X \to \mathcal{F} \to 0$$
其中 $\mathcal{F}$ 平坦且有有限支撑。

**步骤3**：可表性证明
使用Lurie的可表性定理验证导出可表性。

### 4.3 切复形的计算

**关键引理**：
对于导出形变问题，形变函子在导出意义下是**正合**的。

**计算**：

1. 使用导出形变理论
2. 计算切复形为导出Hom
3. 识别为法丛的上同调

---

## 5. 应用与例子

### 5.1 点的Hilbert概形

**例子 5.1.1**
$X$ 上 $n$ 个点的对称积：
$$\text{Hilb}_X^n = X^{[n]}$$
导出版本 $t_0(\text{dHilb}_X^n) = X^{[n]}$。

对曲面，$X^{[n]}$ 是光滑的（Foglary, Göttsche）。

### 5.2 曲线的Hilbert概形

**例子 5.1.2**
$X = \mathbb{P}^3$ 中曲线的Hilbert概形通常是奇异的。

导出Hilbert概形提供：

- 虚拟基本类
- 正确的形变计数

### 5.3 Donaldson-Thomas理论

**应用 5.3.1**
导出Hilbert概形是**Donaldson-Thomas不变量**的自然模空间：
$$DT_{\beta, n} = \int_{[\text{dHilb}_X^{(\beta, n)}]^{\text{vir}}} 1$$

**应用 5.3.2**（MNOP猜想）
通过导出Hilbert概形，Donaldson-Thomas理论与Gromov-Witten理论联系。

### 5.4 PT稳定对

**应用 5.3.3**（Pandharipande-Thomas）
**稳定对模空间**是导出Hilbert概形的变体：
$$\text{dPT}(X) := \{(F, s) : F \text{ 纯1维}, s: \mathcal{O}_X \to F\}$$

### 5.5 高亏格Gromov-Witten理论

**应用 5.4.1**
导出Hilbert概形用于定义：

- 稳定映射的虚拟模空间
- 高亏格不变量

---

## 6. 与其他概念的关系

### 6.1 与经典Hilbert概形的对比

| 特征 | 经典Hilbert概形 | 导出Hilbert概形 |
|------|----------------|----------------|
| 存在性 | Grothendieck | Lurie-Toën-Vezzosi |
| 奇点 | 有奇点 | 导出光滑 |
| 切空间 | 向量空间 | 切复形 |
| 形变 | 一阶 | 完整同伦 |
| 模空间 | 概形 | 导出代数空间 |

### 6.2 与导出形变理论

```
    导出形变理论
         │
         │ 应用于 Hilbert 问题
         ▼
    导出Hilbert概形
         │
         │ 特殊化
         ▼
    经典Hilbert概形（截断）
```

### 6.3 与虚拟基本类

**关系**：导出Hilbert概形的截断给出**虚拟基本类**：
$$[\text{Hilb}_X]^{\text{vir}} = t_0[\text{dHilb}_X]$$
这是现代枚举几何的核心工具。

### 6.4 与高阶结构

**前沿发展**：

- 谱Hilbert概形
- 与拓扑Hochschild同调的联系
- 导出代数几何中的对称积

---

## 7. 参考文献

### 7.1 奠基文献

1. **Toën, B., Vezzosi, G.** (2008). *Homotopical Algebraic Geometry II: Geometric Stacks and Applications*
   - Mem. Amer. Math. Soc.
   - 导出Hilbert概形的原始构造

2. **Lurie, J.** (2004). *Derived Algebraic Geometry*
   - MIT Thesis
   - 系统理论

3. **Lurie, J.** (2011). *Derived Algebraic Geometry X: Formal Moduli Problems*
   - 导出形变理论

### 7.2 应用文献

1. **Thomas, R.P.** (2000). *A holomorphic Casson invariant for Calabi-Yau threefolds*
   - J. Diff. Geom.
   - DT理论

2. **Pandharipande, R., Thomas, R.P.** (2009). *Curve counting via stable pairs*
   - Ann. of Math.
   - PT理论

3. **Maulik, D., Nekrasov, N., Okounkov, A., Pandharipande, R.** (2006). *Gromov-Witten theory and Donaldson-Thomas theory*
   - Compositio Math.

### 7.3 教科书

1. **Toën, B.** (2014). *Derived Algebraic Geometry*
   - EMS Surv. Math. Sci.
   - 全面概述

2. **Ciocan-Fontanine, I., Kapranov, M.** (2001). *Derived Quot schemes*
   - Ann. Sci. Éc. Norm. Sup.

### 7.4 在线资源

1. **Stacks Project**: [Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N)
2. **Lurie's DAG**: 导出代数几何系列

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0E7P](#tag-0e7p) | 导出几何应用 | 应用方向 |
| [0A9K](#tag-0a9k) | 导出形变理论 | 理论基础 |
| [0A9L](#tag-0a9l) | 导出Hilbert概形 | 本Tag |

### 8.2 经典理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G70](#tag-0g70) | Hilbert概形 | 经典版本 |
| [0G71](#tag-0g71) | Quot概形 | 推广 |
| [0G72](#tag-0g72) | 模空间 | 一般理论 |

### 8.3 导出几何

| Tag | 主题 | 说明 |
|-----|------|------|
| [0A5M](#tag-0a5m) | 稳定无穷范畴 | 基础 |
| [0A5N](#tag-0a5n) | 谱与环谱 | 技术 |
| [0G73](#tag-0g73) | 导出叠 | 全局化 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **现代枚举几何的核心**：DT不变量、PT理论的模空间

2. **导出代数几何的成功应用**：展示了导出几何的威力

3. **物理应用**：弦理论、镜像对称的计算工具

4. **活跃研究**：与墙交叉公式、拓扑弦的联系

### A.2 未解决问题

- **导出Donaldson-Thomas理论的完整发展**
- **高亏格不变量的导出定义**
- **与几何Langlands的联系**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 导出环 | 🔄 进行中 | ★★★★☆ |
| 导出概形 | ❌ 待建设 | ★★★★★ |
| 导出Hilbert函子 | ❌ 待建设 | ★★★★★ |
| 存在性证明 | ❌ 待建设 | ★★★★★ |
| 切复形计算 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
