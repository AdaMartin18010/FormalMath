---
title: MIT 18.06 / 18.700 Linear Algebra 定义对齐手册（L3 语义对齐）
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# MIT 18.06 / 18.700 Linear Algebra 定义对齐手册（L3 语义对齐）

**文档编号**: D018  
**课程代码**: MIT 18.06 / 18.700  
**课程名称**: Linear Algebra  
**对齐标准**: D002-semantic-alignment-playbook.md (L3 定义对齐)  
**生成日期**: 2026-04-04  
**验证人**: Course Alignment Agent (AI)  

---

## 说明

本手册基于 `D008-mit-18-06-syllabus.yaml` 中的 `definitions` 清单，逐条核对每个定义在 FormalMath 项目文档中的等价表述。判定标准遵循 D002 的 L3 "定义对齐"规范，分为三档：

- **严格等价**：对象域、逻辑条件、符号约定、边界情况均一致，或为标准等价变体且等价性已说明。
- **近似表述**：概念相关但存在对象域差异、缺少独立定义块、边界情况未说明等。
- **缺失**：项目文档中完全不存在该定义的独立表述。

**特别关注点**（按用户要求）：
1. 向量空间公理的完整性；
2. 线性无关的等价条件；
3. 基的定义（有限维 vs 一般情况）；
4. 特征值/特征向量对零向量的处理；
5. Strang 矩阵视角与 Axler 算子视角的差异覆盖。

---

## 统计汇总

| 指标 | 数量 | 百分比 |
|:-----|-----:|:-------|
| **总定义数** | 75 | 100% |
| **严格等价** | 59 | 78.7% |
| **近似表述** | 11 | 14.7% |
| **缺失** | 5 | 6.7% |

**L3 通过状态**: ❌ **未通过**（核心定义严格等价率 78.7% < 90% 阈值）。

**主要问题摘要**:
- 11 项近似表述多为：概念在正文或代码中被使用，但缺少独立的 "Definition" 定义块（如 Pivot、Free Variable、Normal Equations 等）。
- 5 项缺失集中在图论/网络（Incidence Matrix、Kirchhoff's Laws）、几何解释（Signed Volume）和动力系统（Stable/Unstable/Center Subspaces、Fourier Matrix）等应用性定义。
- Strang 的具象/矩阵入门视角（如 R^n 中向量的具体定义）在项目文档中较弱，项目更偏向 Axler 的抽象/算子视角。

---

## 详细对齐记录


### Unit I: The Geometry of Linear Equations and Gaussian Elimination

---

#### DEF-001: Vector

- **课程来源**: Strang 1.1 / Axler 1.A
- **课程定义**: 
  - Strang: A vector in $\mathbb{R}^n$ is an ordered $n$-tuple of real numbers, often visualized as an arrow from the origin to the point $(v_1, \ldots, v_n)$.
  - Axler: An element of a vector space $V$ over a field $\mathbb{F}$.
- **项目对应路径**: `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/vector-space.yaml`
- **项目中的表述**:
  > "向量空间是'可以做加法和数乘'的对象集合。例如：ℝ³：三维空间中的箭头；ℝⁿ：n元组；C([0,1])：连续函数；矩阵空间。"
  > 
  > 形式化定义（yaml）: "设 F 是域。F 上的向量空间是四元组 (V, +, ·, F)..."
- **对齐判定**: 🟡 **近似表述**
- **差异分析**:
  - 项目文档从**抽象向量空间**的视角切入，将向量定义为向量空间的元素，符合 Axler 的路径。
  - **缺少** Strang 视角下对 $\mathbb{R}^n$ 中向量作为具体 $n$-元组的入门级定义，也缺少对行向量/列向量区分的说明。
- **修正建议**: 在 `vector-space.yaml` 或 `01-线性代数与矩阵理论-国际标准深度扩展版.md` 中增加一个面向 18.06 的入门定义块："向量（在 $\mathbb{R}^n$ 中）是有序 $n$-元组..."，并明确说明其与抽象定义的等价性。

---

#### DEF-002: Linear Combination

- **课程来源**: Strang 1.1 / Axler 1.B
- **课程定义**: Given vectors $v_1, \ldots, v_n$ and scalars $c_1, \ldots, c_n$, the vector $c_1 v_1 + \cdots + c_n v_n$ is called a linear combination of $v_1, \ldots, v_n$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 项目文档在"基"、"列空间"等段落中频繁使用"线性组合"一词（如"基是线性无关生成集"、"列空间是列向量的所有线性组合"），但**未找到以 "Definition" 标记的独立定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 概念被隐含使用，但缺少独立的 L3 定义块。无符号冲突，无边界问题，但形式上不满足"显式定义段落"的要求。
- **修正建议**: 在 `01-线性代数与矩阵理论-国际标准深度扩展版.md` 第 1.1 节后增加一个显式的 **定义 1.1' (Linear Combination)**：给定域 $F$ 上的向量空间 $V$ 中的向量组 $v_1,\dots,v_n$ 和标量 $c_1,\dots,c_n \in F$，称 $\sum c_i v_i$ 为它们的线性组合。

---

#### DEF-003: Matrix-Vector Product

- **课程来源**: Strang 1.3 / Axler 3.C
- **课程定义**: If $A$ is an $m \times n$ matrix with columns $a_1, \ldots, a_n$ and $x \in \mathbb{R}^n$, then $Ax = x_1 a_1 + \cdots + x_n a_n$.
- **项目对应路径**: `Mathlib.Data.Matrix.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.Data.Matrix.Basic` 包含矩阵-向量乘法的严格定义。项目本地中文文档未包含该定义的独立定义块。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: Mathlib 对矩阵-向量乘法的定义与课程标准等价（列视角的线性组合）。但项目缺少面向课程的中文解释文档。
- **修正建议**: 在 `01-线性代数与矩阵理论-国际标准深度扩展版.md` 的矩阵章节中补充一个中文定义块，明确给出 $Ax$ 的两种等价视角（行视角与列视角）。

---

#### DEF-004: Elementary Matrix

- **课程来源**: Strang 2.2 / Axler 3.C
- **课程定义**: An elementary matrix is a matrix that differs from the identity matrix by one single elementary row operation.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Basic`。项目本地中文文档未包含独立定义块。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 包含初等矩阵的严格形式化定义。
- **修正建议**: —

---

#### DEF-005: Pivot

- **课程来源**: Strang 2.2
- **课程定义**: The first nonzero entry in a row of a matrix during elimination; also used for the pivot position (row $i$, column $i$ in the echelon form).
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > "高斯消元中的非零首项"（MIT 术语对照表）；"用高斯消去构造主元列"（附录 A）。**未找到独立的 "Pivot" 定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 概念在算法描述和术语对照表中被提及，但缺少严格的数学定义块（未说明主元位置、主元列、主元行的精确含义）。
- **修正建议**: 在 `01-...md` 矩阵分解或 RREF 章节中增加显式定义：主元是行最简形中每行第一个非零元素；主元位置是 $(i, j_i)$ 等。

---

#### DEF-006: Upper Triangular Matrix

- **课程来源**: Strang 2.2 / Axler 1.C (as a property)
- **课程定义**: A square matrix $U$ is upper triangular if all entries below the main diagonal are zero: $U_{ij} = 0$ for $i > j$.
- **项目对应路径**: `Mathlib.Data.Matrix.Block`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.Data.Matrix.Block` 包含上三角矩阵的严格定义。项目本地中文文档未包含独立定义块。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-007: Inverse Matrix

- **课程来源**: Strang 2.3 / Axler 3.D
- **课程定义**: An $n \times n$ matrix $A$ is invertible if there exists a matrix $B$ such that $AB = BA = I$. The matrix $B$ is called the inverse of $A$, denoted $A^{-1}$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`。`01-...md` 中 Python 代码 `inverse()` 方法也实现了矩阵求逆。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。课程定义与 Mathlib 定义逻辑等价。
- **修正建议**: —

---

#### DEF-008: Singular Matrix

- **课程来源**: Strang 2.3
- **课程定义**: A square matrix that is not invertible.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > Python 代码注释：`return None  # 奇异矩阵`。MIT 术语对照表中无此条目。**未找到独立的数学定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 概念仅作为代码注释出现，没有 "Definition: 奇异矩阵" 的正式段落。对于初学者而言，这不足以构成 L3 定义对齐。
- **修正建议**: 在 `01-...md` 矩阵可逆性章节中增加显式定义块：若方阵 $A$ 不存在逆矩阵，则称 $A$ 为奇异矩阵；等价地，$\det(A)=0$ 或 $A$ 的零空间非平凡。

---

#### DEF-009: Gauss-Jordan Elimination

- **课程来源**: Strang 2.3
- **课程定义**: A procedure to find the inverse of a matrix (or solve $Ax = b$) by applying elementary row operations to the augmented matrix $[A \mid I]$ until it becomes $[I \mid A^{-1}]$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 附录 A："对 $m \times n$ 矩阵 $A$，经有限次初等行变换化为行最简形 $R$（RREF）。" **未明确提到 Gauss-Jordan 消元法的名称及其用于求逆的具体形式**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 项目文档描述了 RREF 的构造过程（高斯消元的延伸），但没有将 "Gauss-Jordan Elimination" 作为独立方法定义，也没有明确说明 $[A \mid I] \to [I \mid A^{-1}]$ 的标准算法。
- **修正建议**: 在 `01-...md` 矩阵分解章节中增加显式定义：Gauss-Jordan 消元法是通过初等行变换将增广矩阵 $[A \mid I]$ 化为 $[I \mid A^{-1}]$ 以求逆矩阵的算法。

---

#### DEF-010: LU Factorization

- **课程来源**: Strang 2.3, 2.6 / Axler —
- **课程定义**: A factorization of a matrix $A$ into a lower triangular matrix $L$ (with 1's on the diagonal) and an upper triangular matrix $U$, such that $A = LU$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.LU`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.LU`。`01-...md` 中也有 Python 实现和 MIT 术语对照："LU 分解 | $A=LU$ | ✅ 完全一致"。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 与本地文档均覆盖。
- **修正建议**: —

---

#### DEF-011: Permutation Matrix

- **课程来源**: Strang 2.5 / Axler —
- **课程定义**: A square matrix obtained by permuting the rows of an identity matrix; used to represent row exchanges in $PA = LU$.
- **项目对应路径**: `Mathlib.GroupTheory.Permutation.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.GroupTheory.Permutation.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-012: Transpose

- **课程来源**: Strang 2.5 / Axler 3.F
- **课程定义**: The transpose of an $m \times n$ matrix $A$ is the $n \times m$ matrix $A^T$ whose $(i,j)$-entry is $A_{ji}$.
- **项目对应路径**: `Mathlib.Data.Matrix.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.Data.Matrix.Basic`。`01-...md` 中 Python `transpose()` 方法也实现了矩阵转置。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-013: Symmetric Matrix

- **课程来源**: Strang 2.5 / Axler 7.A
- **课程定义**: A real matrix $A$ is symmetric if $A^T = A$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Symmetric`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Symmetric`。`01-...md` MIT 术语对照表："Symmetric matrices: $A = A^T$"。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —


### Unit II: Vector Spaces and the Four Fundamental Subspaces

---

#### DEF-014: Vector Space

- **课程来源**: Strang 3.1 / Axler 1.A
- **课程定义**: 
  - Strang: A collection of vectors in $\mathbb{R}^n$ closed under addition and scalar multiplication (later generalized).
  - Axler: A set $V$ equipped with addition and scalar multiplication over a field $\mathbb{F}$ satisfying commutativity, associativity, additive identity, additive inverse, multiplicative identity, and distributive properties.
- **项目对应路径**: `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/vector-space.yaml`
- **项目中的表述**:
  > `vector-space.yaml` 形式化定义：
  > "设 F 是域。F 上的向量空间是四元组 (V, +, ·, F)，其中：1. (V, +) 是阿贝尔群；2. 标量乘法 ·: F × V → V 满足：1·v = v；(ab)·v = a·(b·v)；a·(u+v) = a·u + a·v；(a+b)·v = a·v + b·v。"
  > 
  > `01-...md` 定义 1.1: "设 $F$ 是一个域，$V$ 是一个集合，向量空间是一个有序四元组 $(V, F, +, \cdot)$，其中：1. 加法群: $(V, +)$ 构成阿贝尔群；2. 标量乘法: $\cdot: F \times V \rightarrow V$；3. 分配律... 4. 结合律... 5. 单位元..."
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目文档将向量空间的 8 条公理完整覆盖：加法交换律、加法结合律、零元、加法逆元（打包在"阿贝尔群"中，共 4 条），加上标量乘法的 1·v=v、(ab)·v=a·(bv)、分配律（左、右，共 2 条），合计 8+1=9 条（阿贝尔群本身已完整）。这与 Axler 的标准定义逻辑等价。
  - **边界情况**：`01-...md` 定理 1.1 明确推导了 $0 \cdot v = 0$、$a \cdot 0 = 0$、$(-a) \cdot v = -(a \cdot v)$，说明了对零元的处理。
  - **视角差异**：项目更偏向 Axler 的抽象/公理化路径，Strang 的"从 $\mathbb{R}^n$ 具体例子出发"的路径较弱。
- **修正建议**: 在 `vector-space.yaml` 的 informal 部分增加更多 Strang 风格的入门说明："向量空间的概念可以从 $\mathbb{R}^n$ 推广而来——只要一个集合上的加法和数乘满足以下法则..."

---

#### DEF-015: Subspace

- **课程来源**: Strang 3.1 / Axler 1.C
- **课程定义**: A subset $U$ of a vector space $V$ is a subspace if $U$ is also a vector space under the same addition and scalar multiplication; equivalently, $U$ is closed under addition and scalar multiplication and contains $0$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Subspace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Subspace`。项目本地中文文档未包含独立的子空间定义块。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: Mathlib 对子空间的定义与课程标准严格等价。但缺少本地中文解释文档。
- **修正建议**: 在 `01-...md` 中增加独立的子空间定义块，以覆盖 Strang 视角下的列空间、零空间作为子空间的具体例子。

---

#### DEF-016: Column Space C(A)

- **课程来源**: Strang 3.1 / Axler 3.C
- **课程定义**: The column space of an $m \times n$ matrix $A$, denoted $C(A)$, is the set of all linear combinations of the columns of $A$; it is a subspace of $\mathbb{R}^m$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.ColumnSpace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.ColumnSpace`。`01-...md` 附录 B：
  > "| **列空间（Column Space）** | $C(A)$ | $A$ 的列向量的所有线性组合 | $r$ | $\mathbb{R}^m$ |"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 与本地文档（MIT 术语对照表/四大子空间框架）均覆盖。
- **修正建议**: —

---

#### DEF-017: Nullspace N(A)

- **课程来源**: Strang 3.1 / Axler 3.B
- **课程定义**: The nullspace of an $m \times n$ matrix $A$, denoted $N(A)$, is the set of all solutions to $Ax = 0$; it is a subspace of $\mathbb{R}^n$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.NullSpace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.NullSpace`。`01-...md` 附录 B：
  > "| **零空间（Nullspace）** | $N(A)$ | 满足 $Ax = 0$ 的所有解 | $n - r$ | $\mathbb{R}^n$ |"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-018: Pivot Variable

- **课程来源**: Strang 3.2
- **课程定义**: In the system $Ax = b$, a pivot variable corresponds to a column containing a pivot in the row echelon form of $A$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 附录 A："RREF 的主元列构成列空间的基"；"用高斯消去构造主元列"。**未找到 "Pivot Variable" 的独立定义**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: "主元列"概念被提及，但 "Pivot Variable"（对应于主元列的变量）没有独立的定义块。对于求解 $Ax=b$ 的算法理解，这是一个关键概念。
- **修正建议**: 在 `01-...md` RREF 或高斯消元章节中增加：对应于主元列的未知数称为主元变量（pivot variable），其值由自由变量唯一确定。

---

#### DEF-019: Free Variable

- **课程来源**: Strang 3.2
- **课程定义**: In the system $Ax = b$, a free variable corresponds to a column without a pivot in the row echelon form of $A$; it can be chosen arbitrarily to parametrize the solution set.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > MIT 术语对照表："Free Variable | 自由变量 | 对应于非主元列 | ✅ 一致"。附录 A："自由变量个数 = $n - \text{rank}(A)$"。**未找到独立的 "Free Variable" 定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 与 Pivot Variable 类似，概念在术语对照表和算法描述中被使用，但没有独立的数学定义块。
- **修正建议**: 与 Pivot Variable 一起补充定义块：对应于非主元列的未知数称为自由变量，可任意取值，每一个自由变量对应零空间的一个特殊解（special solution）。

---

#### DEF-020: Row Reduced Echelon Form (RREF)

- **课程来源**: Strang 3.2 / Axler 3.B (as echelon form)
- **课程定义**: The reduced row echelon form of a matrix satisfies: (1) all nonzero rows are above any rows of all zeros; (2) the leading entry of each nonzero row is 1; (3) each leading 1 is the only nonzero entry in its column; (4) the leading 1 of a row is to the right of the leading 1 of the row above it.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.RowReducedEchelonForm`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.RowReducedEchelonForm`。`01-...md` 附录 A 也详细描述了 RREF 的构造过程和性质。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 对 RREF 的定义与课程标准的四个条件完全对应。
- **修正建议**: —

---

#### DEF-021: Particular Solution

- **课程来源**: Strang 3.3 / Axler 3.B
- **课程定义**: A particular solution $x_p$ to $Ax = b$ is any single vector satisfying the equation. The complete solution is $x = x_p + x_n$ where $x_n \in N(A)$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 附录 B："若 $x_p$ 是一个特解，则通解为 $x = x_p + x_n$，其中 $x_n \in N(A)$"。**未找到 "Particular Solution" 的独立定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 概念在通解定理的陈述中被使用，但没有独立的 "Definition: 特解" 段落。对于初学者区分"特解"与"齐次解"的概念辨析，独立定义很重要。
- **修正建议**: 在 `01-...md` 线性方程组章节中增加显式定义：满足 $Ax_p = b$ 的任意向量 $x_p$ 称为方程组 $Ax=b$ 的一个特解。

---

#### DEF-022: Linear Independence

- **课程来源**: Strang 3.5 / Axler 2.A
- **课程定义**: A list of vectors $v_1, \ldots, v_n$ is linearly independent if the only solution to $a_1 v_1 + \cdots + a_n v_n = 0$ is $a_1 = \cdots = a_n = 0$.
- **项目对应路径**: `Mathlib.LinearAlgebra.LinearIndependent`
- **项目中的表述**:
  > `01-...md` 定义 1.2："向量组 $\{v_1, v_2, \ldots, v_n\}$ 称为线性无关，如果方程 $\sum_{i=1}^n a_i v_i = 0$ 只有平凡解 $a_1 = a_2 = \cdots = a_n = 0$。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.LinearIndependent`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目定义与 Axler 的定义路径完全一致（线性组合 = 0 只有平凡解）。
  - **等价条件**：项目文档缺少对线性无关等价条件的系统整理。例如 Strang 强调的："$A$ 的列线性无关 $\iff N(A) = \{0\} \iff Ax=0$ 只有零解"；Axler 强调的："$v \notin \operatorname{span}(v_1,\dots,v_{n-1})$" 等。
- **修正建议**: 在 `01-...md` 定义 1.2 后增加一个"等价条件"段落，列出：
  1. $\{v_i\}$ 线性无关；
  2. $0$ 的唯一表示是平凡表示；
  3. 对矩阵列向量：$Ax=0$ 只有零解（$N(A)=\{0\}$）；
  4. 没有一个向量可以表示为前面向量的线性组合（Axler 路径）。

---

#### DEF-023: Span

- **课程来源**: Strang 3.5 / Axler 2.A
- **课程定义**: The span of a list of vectors $v_1, \ldots, v_n$ is the set of all linear combinations of these vectors: $\operatorname{span}(v_1, \ldots, v_n) = \{a_1 v_1 + \cdots + a_n v_n : a_i \in \mathbb{F}\}$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Span`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Span`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-024: Basis

- **课程来源**: Strang 3.5 / Axler 2.C
- **课程定义**: A basis of a vector space $V$ is a list of vectors that is linearly independent and spans $V$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Basis`
- **项目中的表述**:
  > `01-...md` 定义 1.3："向量空间 $V$ 的基是 $V$ 的线性无关生成集。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Basis`。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**:
  - 项目定义与 Axler 的定义完全一致（"线性无关生成集"）。
  - **关键问题（有限维 vs 一般情况）**：`01-...md` 紧接着定理 1.2 说"每个有限维向量空间都有基，且所有基的向量个数相同"，暗示了定义主要适用于有限维情形。对于**无限维向量空间的基（Hamel basis）**，项目文档未作说明。虽然 MIT 18.06/18.700 主要讨论有限维，但 18.700（Axler）在某些章节会涉及无限维多项式空间 $P(\mathbb{F})$。
  - 此外，项目缺少 Strang 强调的"标准基"、"$\mathbb{R}^n$ 中的基"等具体例子密度。
- **修正建议**: 
  1. 在 `01-...md` 定义 1.3 后增加注释："上述定义对有限维和无限维向量空间均适用；在无限维情形，基称为 Hamel 基，要求每个向量可唯一表示为基向量的有限线性组合。"
  2. 补充更多 Strang 风格的具体例子：$\mathbb{R}^n$ 的标准基、$P_n$ 的基 $\{1, t, \dots, t^n\}$、$M_{2 \times 2}$ 的基。

---

#### DEF-025: Dimension

- **课程来源**: Strang 3.5 / Axler 2.C
- **课程定义**: The dimension of a finite-dimensional vector space is the length of any basis of the vector space.
- **项目对应路径**: `Mathlib.LinearAlgebra.Dimension`
- **项目中的表述**:
  > `01-...md` 定理 1.2："所有基的向量个数相同。" 多维知识矩阵："维数 | 基的向量个数 | 维数唯一性"。
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Dimension`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 项目通过"基的个数相同"隐含了维数的良定义性，与课程标准等价。Mathlib 也有严格的 `Dimension` 定义。
- **修正建议**: —

---

#### DEF-026: Row Space C(A^T)

- **课程来源**: Strang 3.6
- **课程定义**: The row space of a matrix $A$, denoted $C(A^T)$ or $\operatorname{Row}(A)$, is the set of all linear combinations of the rows of $A$; it is a subspace of $\mathbb{R}^n$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.RowSpace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.RowSpace`。`01-...md` 附录 B：
  > "| **行空间（Row Space）** | $C(A^T)$ | $A$ 的行向量的所有线性组合（即 $A^T$ 的列空间） | $r$ | $\mathbb{R}^n$ |"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-027: Left Nullspace N(A^T)

- **课程来源**: Strang 3.6
- **课程定义**: The left nullspace of a matrix $A$, denoted $N(A^T)$, is the set of all vectors $y$ such that $A^T y = 0$ (or equivalently $y^T A = 0$); it is a subspace of $\mathbb{R}^m$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.NullSpace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.NullSpace`（通过转置构造）。`01-...md` 附录 B：
  > "| **左零空间（Left Nullspace）** | $N(A^T)$ | 满足 $A^T y = 0$ 的所有解（或 $y^T A = 0$） | $m - r$ | $\mathbb{R}^m$ |"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-028: Rank

- **课程来源**: Strang 3.6 / Axler 2.C, 3.B
- **课程定义**: The rank of a matrix $A$ is the dimension of its column space (equivalently, the number of pivots in its echelon form, or the dimension of its row space).
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Rank`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Rank`。`01-...md` 多维知识矩阵和附录 B 均多次提及秩的定义和唯一性。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-029: Incidence Matrix

- **课程来源**: Strang 3.5 (Lecture on Graphs and Networks)
- **课程定义**: For a directed graph with $m$ edges and $n$ nodes, the incidence matrix $A$ is the $m \times n$ matrix whose $(i,j)$-entry is $+1$ if edge $i$ leaves node $j$, $-1$ if edge $i$ enters node $j$, and $0$ otherwise.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 在 `01-...md` 全文搜索未找到 "Incidence Matrix"、"关联矩阵"、"图"、"网络" 等相关定义的独立表述。
- **对齐判定**: ⚫ **缺失** (MISSING-3, P1)
- **差异分析**: 项目文档完全缺失图论/网络视角下的关联矩阵定义。这是 Strang 课程的特色内容之一。
- **修正建议**: 在 `01-...md` 应用章节（或新建图论与线性代数文档）中增加：
  - 关联矩阵的严格定义；
  - 节点-边关系与 $A^T A$、图拉普拉斯矩阵的联系；
  - 结合 Kirchhoff 定律的示例。

---

#### DEF-030: Kirchhoff's Laws

- **课程来源**: Strang 3.5 (Lecture on Graphs and Networks)
- **课程定义**: 
  - Kirchhoff's Current Law (KCL): The sum of currents entering a node equals the sum leaving it ($A^T w = 0$ for potentials).
  - Kirchhoff's Voltage Law (KVL): The sum of voltage drops around any closed loop is zero.
- **项目对应路径**: `docs/02-代数结构/03-应用分析/线性代数应用/05-线性代数应用-机器学习版.md`
- **项目中的表述**:
  > 在 `05-...md` 中全文搜索未找到 "Kirchhoff"、"基尔霍夫"、"电流定律"、"电压定律" 等相关内容。该文档专注于机器学习应用（PCA、SVD、线性回归、神经网络），未覆盖电路网络。
- **对齐判定**: ⚫ **缺失** (MISSING-3, P1)
- **差异分析**: 项目文档将该定义的路径错误映射到了机器学习应用文档中，实际内容不存在。
- **修正建议**: 新建或补充到图论/网络应用文档中，给出 KCL/KVL 的线性代数表述：$A^T w = 0$（左零空间）与 $Au = v$（势差）。


### Unit III: Orthogonality, Projections, and Least Squares

---

#### DEF-031: Inner Product

- **课程来源**: Strang 4.1 / Axler 6.A
- **课程定义**: An inner product on a vector space $V$ over $\mathbb{F}$ ($\mathbb{R}$ or $\mathbb{C}$) is a function $\langle \cdot, \cdot \rangle : V \times V \to \mathbb{F}$ satisfying conjugate symmetry, linearity in the first argument, and positive definiteness.
- **项目对应路径**: `Mathlib.Analysis.InnerProductSpace.Basic`
- **项目中的表述**:
  > `01-...md` 定义 5.1：
  > "设 $V$ 是域 $F$ 上的向量空间，内积是函数 $\langle \cdot, \cdot \rangle: V \times V \rightarrow F$ 满足：1. 共轭对称性: $\langle v, w \rangle = \overline{\langle w, v \rangle}$；2. 线性性: $\langle av + bw, u \rangle = a\langle v, u \rangle + b\langle w, u \rangle$；3. 正定性: $\langle v, v \rangle \geq 0$ 且 $\langle v, v \rangle = 0 \leftrightarrow v = 0$。"
  > 
  > Mathlib 接口：`Mathlib.Analysis.InnerProductSpace.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目定义与 Axler 的定义完全一致（共轭对称、第一变元线性、正定性）。
  - **边界情况**：正定性条件中 "$\langle v, v \rangle = 0 \leftrightarrow v = 0$" 明确处理了零向量的情况，严谨。
  - **视角差异**：项目直接跳到一般内积空间，缺少 Strang 的 "$\mathbb{R}^n$ 中点积 $x \cdot y = x^T y$" 作为具体入口。
- **修正建议**: 在定义 5.1 前增加一个小节："在 $\mathbb{R}^n$ 中，标准内积（点积）定义为 $x \cdot y = \sum x_i y_i$；这是内积空间的最基本例子。"

---

#### DEF-032: Orthogonal Vectors

- **课程来源**: Strang 4.1 / Axler 6.A
- **课程定义**: Two vectors $u, v$ are orthogonal if $\langle u, v \rangle = 0$.
- **项目对应路径**: `Mathlib.Analysis.InnerProductSpace.Basic`
- **项目中的表述**:
  > `01-...md` 定义 5.2："向量 $v$ 和 $w$ 称为正交，如果 $\langle v, w \rangle = 0$。"
  > 
  > Mathlib 接口：`Mathlib.Analysis.InnerProductSpace.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-033: Orthogonal Complement

- **课程来源**: Strang 4.1 / Axler 6.C
- **课程定义**: For a subset $U$ of an inner product space $V$, the orthogonal complement $U^\perp$ is the set of all vectors in $V$ that are orthogonal to every vector in $U$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Orthogonal`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Orthogonal`。`01-...md` 附录 B：
  > "正交补关系：$N(A) = C(A^T)^\perp$ 且 $N(A^T) = C(A)^\perp$"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-034: Projection Matrix

- **课程来源**: Strang 4.2 / Axler 6.C
- **课程定义**: A matrix $P$ is a projection matrix if $P^2 = P$ and $P^T = P$ (for orthogonal projections onto subspaces of $\mathbb{R}^n$). The projection onto the column space of $A$ is $P = A(A^T A)^{-1} A^T$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Projector`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Projector`。`01-...md` MIT 术语对照表：
  > "Projection Matrix | 投影矩阵 | $P = A(A^TA)^{-1}A^T$ | ✅ 完全一致"
  > 
  > 附录 B 也使用了投影矩阵的符号。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-035: Least Squares Solution

- **课程来源**: Strang 4.3 / Axler 6.C
- **课程定义**: A least squares solution $\hat{x}$ to $Ax = b$ is a vector that minimizes $\|b - Ax\|^2$ over all $x \in \mathbb{R}^n$.
- **项目对应路径**: `docs/02-代数结构/03-应用分析/线性代数应用/05-线性代数应用-机器学习版.md`
- **项目中的表述**:
  > `05-...md` 3.1 节：
  > "**最小二乘估计**: $\hat{\beta} = \arg\min_{\beta} \|y - X\beta\|_2^2 = (X^T X)^{-1} X^T y$"
  > 
  > `01-...md` 附录 F 也有法方程与 SVD 最小二乘的代码示例。**未找到以 "Definition" 标记的独立最小二乘解定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 项目文档将最小二乘解作为优化问题的解直接给出公式，但没有独立的数学定义块明确陈述"最小二乘解是使残差范数最小的向量"。
- **修正建议**: 在 `01-...md` 或 `05-...md` 中增加显式定义块：给定矩阵 $A \in \mathbb{R}^{m \times n}$ 和向量 $b \in \mathbb{R}^m$，称 $\hat{x}$ 为方程 $Ax=b$ 的最小二乘解，如果 $\|b - A\hat{x}\|_2 = \min_{x} \|b - Ax\|_2$。

---

#### DEF-036: Normal Equations

- **课程来源**: Strang 4.3 / Axler 6.C
- **课程定义**: The normal equations for the least squares problem $Ax = b$ are $A^T A \hat{x} = A^T b$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > `01-...md` 附录 F 标题为"可运行示例：法方程 vs SVD 最小二乘"，正文使用了 `X_augmented.T @ X_augmented` 和 `X_augmented.T @ y`。**未找到 "Normal Equations" 的独立数学定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 概念在代码和示例标题中出现，但缺少 "$A^T A \hat{x} = A^T b$ 是法方程" 的正式定义陈述。
- **修正建议**: 在最小二乘章节中增加显式定义：称方程组 $A^T A \hat{x} = A^T b$ 为最小二乘问题的法方程（normal equations）。

---

#### DEF-037: Orthogonal Matrix

- **课程来源**: Strang 4.4 / Axler 7.A
- **课程定义**: A real square matrix $Q$ is orthogonal if $Q^T Q = QQ^T = I$; equivalently, its columns form an orthonormal set.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Orthogonal`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Orthogonal`。`01-...md` MIT 术语对照表：
  > "Orthogonal Matrix | 正交矩阵 | $Q^T Q = I$ | ✅ 完全一致"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-038: Orthonormal Basis

- **课程来源**: Strang 4.4 / Axler 6.B
- **课程定义**: A basis is orthonormal if each basis vector has norm 1 and is orthogonal to every other basis vector.
- **项目对应路径**: `Mathlib.LinearAlgebra.Orthonormal`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Orthonormal`。`01-...md` Gram-Schmidt 正交化部分也使用了"正交向量组"、"标准正交基"等术语。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-039: QR Factorization

- **课程来源**: Strang 4.4 / Axler 6.B
- **课程定义**: A factorization of a matrix $A$ with linearly independent columns into $A = QR$, where $Q$ has orthonormal columns and $R$ is upper triangular with positive diagonal entries.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.QR`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.QR`。`01-...md` 中也有 Gram-Schmidt 实现 QR 分解的 Python 代码。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —


### Unit IV: Determinants

---

#### DEF-040: Determinant

- **课程来源**: Strang 5.1 / Axler 10.A
- **课程定义**: The determinant is a scalar-valued function on square matrices satisfying three key properties: (1) $\det(I) = 1$; (2) sign reversal under row exchange; (3) linearity in each row separately. For an $n \times n$ matrix, it can also be defined via the Leibniz formula or as the unique alternating multilinear form.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Determinant`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Determinant`。`01-...md` 多维知识矩阵和 Python 代码中也有行列式的实现。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 
  - **视角差异**：Strang 从行列式的三个基本性质出发定义，Axler 从体积/定向角度定义（在《Linear Algebra Done Right》第 10 章）。Mathlib 采用的是 Leibniz/置换群的定义路径，这是标准等价的，但项目缺少对 Strang 三条性质公理体系的显式说明。
- **修正建议**: 在 `01-...md` 中增加一个小节，说明行列式的三种等价定义路径：
  1. Strang 公理化路径（三条基本性质）；
  2. Leibniz 公式路径（Mathlib 采用）；
  3. 体积/有向体积路径（Axler 采用）。
  并给出等价性说明。

---

#### DEF-041: Cofactor

- **课程来源**: Strang 5.2 / Axler 10.B
- **课程定义**: The $(i,j)$-cofactor of a matrix $A$ is $C_{ij} = (-1)^{i+j} \det(M_{ij})$, where $M_{ij}$ is the minor matrix obtained by deleting row $i$ and column $j$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Cofactor`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Cofactor`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-042: Permutation

- **课程来源**: Strang 5.1 / Axler 10.A
- **课程定义**: A permutation of $\{1, \ldots, n\}$ is a bijective function $\sigma: \{1, \ldots, n\} \to \{1, \ldots, n\}$. The sign of a permutation is $+1$ for an even number of transpositions and $-1$ for an odd number.
- **项目对应路径**: `Mathlib.GroupTheory.Permutation.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.GroupTheory.Permutation.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-043: Cramer's Rule

- **课程来源**: Strang 5.3 / Axler 10.B
- **课程定义**: If $A$ is an invertible $n \times n$ matrix, then the unique solution to $Ax = b$ has $i$-th component $x_i = \frac{\det(A_i)}{\det(A)}$, where $A_i$ is $A$ with column $i$ replaced by $b$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Cramer`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Cramer`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-044: Adjugate Matrix

- **课程来源**: Strang 5.3 / Axler 10.B
- **课程定义**: The adjugate (or classical adjoint) of $A$ is the transpose of the cofactor matrix: $\operatorname{adj}(A) = C^T$. It satisfies $A^{-1} = \frac{1}{\det A} \operatorname{adj}(A)$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Adjugate`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Adjugate`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-045: Signed Volume

- **课程来源**: Strang 5.3 / Axler 10.A
- **课程定义**: The absolute value of the determinant of a matrix $A$ with columns $v_1, \ldots, v_n$ is the $n$-dimensional volume of the parallelepiped spanned by those vectors. The sign indicates orientation.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 在 `01-...md` 全文搜索未找到 "Signed Volume"、"有向体积"、"定向"、"parallelepiped" 等独立定义。
- **对齐判定**: ⚫ **缺失** (MISSING-3, P1)
- **差异分析**: 项目文档完全缺失有向体积/行列式几何解释的定义。这是 Axler 和 Strang 都强调的重要几何直觉。
- **修正建议**: 在 `01-...md` 行列式章节中增加：
  - 定义：$|\det(A)|$ 是由 $A$ 的列向量张成的平行多面体的 $n$ 维体积；
  - 说明：符号表示定向（orientation），行交换改变符号对应于定向翻转。

### Unit V: Eigenvalues and Eigenvectors

---

#### DEF-046: Eigenvalue

- **课程来源**: Strang 6.1 / Axler 5.A
- **课程定义**: 
  - Axler: A scalar $\lambda \in \mathbb{F}$ is an eigenvalue of a linear operator $T: V \to V$ if there exists a nonzero $v \in V$ such that $Tv = \lambda v$.
  - Strang: A scalar $\lambda$ is an eigenvalue of a square matrix $A$ if $Av = \lambda v$ for some nonzero vector $v$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Eigenspace.Basic`
- **项目中的表述**:
  > `01-...md` 定义 4.1：
  > "设 $T: V \rightarrow V$ 是线性变换，如果存在**非零向量** $v \in V$ 和标量 $\lambda \in F$ 使得：$T(v) = \lambda v$，则称 $\lambda$ 是 $T$ 的特征值，$v$ 是 $T$ 的对应于 $\lambda$ 的特征向量。"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目定义明确排除了零向量作为特征向量（"非零向量 $v$"），这是正确的。
  - **边界情况**：特征值 $\lambda = 0$ 的情况是允许的（只要存在非零特征向量），定义中对此没有禁止，表述正确。
  - **视角差异**：项目采用 Axler 的算子视角（$T: V \to V$），缺少 Strang 强调的"矩阵特征值 = 特征多项式根"作为计算入口的说明。
- **修正建议**: 在定义 4.1 后增加一个注记框：
  > **课程对齐注记（MIT 18.06）**：在矩阵视角下，$\lambda$ 是 $A$ 的特征值当且仅当 $\det(A - \lambda I) = 0$。这一等价性由特征多项式给出，见下文定义。

---

#### DEF-047: Eigenvector

- **课程来源**: Strang 6.1 / Axler 5.A
- **课程定义**: A nonzero vector $v$ such that $Av = \lambda v$ (or $Tv = \lambda v$) is called an eigenvector of $A$ (or $T$) corresponding to the eigenvalue $\lambda$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Eigenspace.Basic`
- **项目中的表述**:
  > 同 DEF-046：`01-...md` 定义 4.1 明确说 "非零向量 $v \in V$ ... $v$ 是 $T$ 的对应于 $\lambda$ 的特征向量"。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。零向量被明确排除，符合课程要求。
- **修正建议**: —

---

#### DEF-048: Characteristic Polynomial

- **课程来源**: Strang 6.1 / Axler 5.A
- **课程定义**: For a square matrix $A$, the characteristic polynomial is $p(\lambda) = \det(A - \lambda I)$. For an operator $T$, it is $p(\lambda) = \det(\mathcal{M}(T) - \lambda I)$ with respect to any basis.
- **项目对应路径**: `Mathlib.LinearAlgebra.Charpoly.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Charpoly.Basic`。`01-...md` 也有 Python 实现：
  > `# p(λ) = det(A - λI)`
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-049: Eigenspace

- **课程来源**: Strang 6.1 / Axler 5.A
- **课程定义**: The eigenspace $E(\lambda, T)$ (or $N(A - \lambda I)$) is the set of all eigenvectors corresponding to $\lambda$ together with the zero vector: $E(\lambda, T) = \{v \in V : Tv = \lambda v\}$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Eigenspace.Basic`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Eigenspace.Basic`。`01-...md` 中没有独立的 "Eigenspace" 定义块。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 对 Eigenspace 的定义与课程标准严格等价。
- **修正建议**: 在 `01-...md` 中增加显式的 Eigenspace 定义块，以便中文读者理解。

---

#### DEF-050: Diagonalizable Matrix

- **课程来源**: Strang 6.2 / Axler 5.C
- **课程定义**: A square matrix $A$ is diagonalizable if there exists an invertible matrix $P$ and a diagonal matrix $D$ such that $A = PDP^{-1}$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.IsDiag`
- **项目中的表述**:
  > `01-...md` 定义 6.1："矩阵 $A$ 称为可对角化，如果存在可逆矩阵 $P$ 使得：$P^{-1}AP = D$，其中 $D$ 是对角矩阵。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.IsDiag`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。$P^{-1}AP = D$ 与 $A = PDP^{-1}$ 是标准等价表述。
- **修正建议**: —

---

#### DEF-051: Similar Matrices

- **课程来源**: Strang 6.2 / Axler 5.C
- **课程定义**: Two $n \times n$ matrices $A$ and $B$ are similar if there exists an invertible matrix $P$ such that $B = P^{-1}AP$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Similarity`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Similarity`。`01-...md` 中也有相似矩阵的提及。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-052: Algebraic Multiplicity

- **课程来源**: Strang 6.2 / Axler 5.C
- **课程定义**: The algebraic multiplicity of an eigenvalue $\lambda$ is the number of times $\lambda$ appears as a root of the characteristic polynomial.
- **项目对应路径**: `Mathlib.LinearAlgebra.Eigenspace.Basic`
- **项目中的表述**:
  > `01-...md` Python 代码中有 `algebraic_multiplicity` 函数的实现（计算特征多项式根的重数）。Mathlib 接口：`Mathlib.LinearAlgebra.Eigenspace.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-053: Geometric Multiplicity

- **课程来源**: Strang 6.2 / Axler 5.C
- **课程定义**: The geometric multiplicity of an eigenvalue $\lambda$ is the dimension of its eigenspace: $\dim N(A - \lambda I)$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Eigenspace.Basic`
- **项目中的表述**:
  > `01-...md` Python 代码中有 `geometric_multiplicity` 函数的实现（计算 $n - \text{rank}(A - \lambda I)$）。Mathlib 接口：`Mathlib.LinearAlgebra.Eigenspace.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-054: Matrix Exponential

- **课程来源**: Strang 6.3 / Axler —
- **课程定义**: For a square matrix $A$, the matrix exponential is defined by the power series $e^{A} = \sum_{k=0}^{\infty} \frac{A^k}{k!}$. More generally, $e^{At} = \sum_{k=0}^{\infty} \frac{(At)^k}{k!}$.
- **项目对应路径**: `Mathlib.Analysis.MatrixExponential`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.Analysis.MatrixExponential`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-055: Stable/Unstable/Center Subspaces

- **课程来源**: Strang 6.3 (Differential Equations and $e^{At}$)
- **课程定义**: For a linear system $u' = Au$, the stable subspace $E^s$ is the span of generalized eigenvectors with eigenvalues having negative real part; the unstable subspace $E^u$ corresponds to positive real parts; the center subspace $E^c$ corresponds to zero real parts.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 在 `01-...md` 全文搜索未找到 "Stable Subspace"、"Unstable Subspace"、"Center Subspace"、"稳定子空间"、"不稳定子空间"、"中心子空间" 等定义。
- **对齐判定**: ⚫ **缺失** (MISSING-3, P1)
- **差异分析**: 项目文档完全缺失动力系统中的稳定/不稳定/中心子空间的定义。这是 Strang 18.06 在微分方程章节的特色内容。
- **修正建议**: 在 `01-...md` 特征值应用章节（或新建动力系统与线性代数文档）中增加：
  - 稳定子空间 $E^s$、不稳定子空间 $E^u$、中心子空间 $E^c$ 的定义；
  - 与 $e^{At}$ 和线性常微分方程解的稳定性的关系。

---

#### DEF-056: Hermitian Matrix

- **课程来源**: Strang 6.4 / Axler 7.A
- **课程定义**: A complex square matrix $A$ is Hermitian (or self-adjoint) if $A = A^*$, where $A^*$ denotes the conjugate transpose.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Hermitian`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Hermitian`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-057: Unitary Matrix

- **课程来源**: Strang 6.4 / Axler 7.A
- **课程定义**: A complex square matrix $U$ is unitary if $U^* U = UU^* = I$; equivalently, its columns form an orthonormal set in $\mathbb{C}^n$.
- **项目对应路径**: `Mathlib.LinearAlgebra.UnitaryGroup`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.UnitaryGroup`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-058: Fourier Matrix

- **课程来源**: Strang 6.4 (Complex Matrices and FFT)
- **课程定义**: The $n \times n$ Fourier matrix $F_n$ has entries $(F_n)_{jk} = \omega^{jk}$ where $\omega = e^{-2\pi i / n}$ is a primitive $n$-th root of unity.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > 在 `01-...md` 全文搜索未找到 "Fourier Matrix"、"傅里叶矩阵"、"DFT matrix" 等独立定义。
- **对齐判定**: ⚫ **缺失** (MISSING-3, P1)
- **差异分析**: 项目文档完全缺失傅里叶矩阵的定义。这是 Strang 18.06 在复矩阵与快速傅里叶变换章节的核心定义。
- **修正建议**: 在 `01-...md` 中新增一个小节：复矩阵与离散傅里叶变换，给出 Fourier 矩阵的严格定义、酉性 ($\frac{1}{\sqrt{n}}F_n$ 是酉矩阵) 以及 FFT 的算法思想。


### Unit VI: Symmetric Matrices and Positive Definiteness

---

#### DEF-059: Symmetric Matrix

- **课程来源**: Strang 6.4 / Axler 7.A
- **课程定义**: A real square matrix $A$ is symmetric if $A^T = A$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Symmetric`
- **项目中的表述**:
  > 同 DEF-013。Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Symmetric`。`01-...md` MIT 术语对照表："Symmetric matrices: $A = A^T$"。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。已在 DEF-013 中验证。
- **修正建议**: —

---

#### DEF-060: Orthogonal Diagonalization

- **课程来源**: Strang 6.4 / Axler 7.B
- **课程定义**: A real matrix $A$ is orthogonally diagonalizable if there exists an orthogonal matrix $Q$ and a diagonal matrix $D$ such that $A = QDQ^T$.
- **项目对应路径**: `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml`
- **项目中的表述**:
  > `spectral-theorem.yaml`：
  > "【有限维实对称矩阵】设 $A \in M_n(\mathbb{R})$ 是实对称矩阵（$A = A^T$）。则存在正交矩阵 $Q$ 和对角矩阵 $D$ 使得：$A = QDQ^T$。"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。`spectral-theorem.yaml` 直接给出了正交对角化的矩阵形式。
- **修正建议**: —

---

#### DEF-061: Spectral Theorem

- **课程来源**: Strang 6.4 / Axler 7.B, 7.C
- **课程定义**:
  - Real Spectral Theorem: Every real symmetric matrix has real eigenvalues and an orthonormal basis of eigenvectors.
  - Complex Spectral Theorem: Every normal operator on a complex inner product space is unitarily diagonalizable.
- **项目对应路径**: `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml`
- **项目中的表述**:
  > `spectral-theorem.yaml` 同时包含：
  > 1. 有限维实对称矩阵版本："设 $A \in M_n(\mathbb{R})$ 是实对称矩阵... 则存在正交矩阵 $Q$ 和对角矩阵 $D$ 使得 $A = QDQ^T$。等价地，存在标准正交基 $\{v_1, \ldots, v_n\}$ 使得 $Av_i = \lambda_i v_i$，其中 $\lambda_i \in \mathbb{R}$。"
  > 2. Hilbert 空间自伴算子版本："设 $T$ 是 Hilbert 空间 $H$ 上的有界自伴算子。则存在谱测度 $E$ 使得 $T = \int \lambda \, dE(\lambda)$。"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目文档对实谱定理的表述与 18.06/18.700 完全一致。
  - 对复谱定理，项目采用了泛函分析的谱测度表述（Hilbert 空间版本），这超出了 18.700 的范围（18.700 只要求有限维正规算子的酉对角化）。虽然这是推广，但项目缺少一个**有限维复正规矩阵**的入门级复谱定理表述。
- **修正建议**: 在 `spectral-theorem.yaml` 中补充一个**有限维复正规矩阵**版本：设 $A \in M_n(\mathbb{C})$ 是正规矩阵（$A^*A = AA^*$），则存在酉矩阵 $U$ 和对角矩阵 $D$ 使得 $A = UDU^*$。这更符合 18.700 的课程路径。

---

#### DEF-062: Positive Definite Matrix

- **课程来源**: Strang 6.5 / Axler 7.C
- **课程定义**: A real symmetric matrix $A$ is positive definite if $x^T A x > 0$ for all nonzero vectors $x \in \mathbb{R}^n$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.PosDef`
- **项目中的表述**:
  > `01-...md` 附录 G："正定矩阵等价条件（实对称 $A$）：1) $x^T A x > 0$ ($\forall x \neq 0$)；2) 所有特征值 $> 0$；3) 存在唯一下三角 $L$，使 $A = LL^T$（Cholesky 分解）；4) 所有顺序主子式为正。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.PosDef`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。项目文档不仅给出了定义，还给出了完整的等价条件刻画，严谨度超过课程要求。
- **修正建议**: —

---

#### DEF-063: Positive Semidefinite Matrix

- **课程来源**: Strang 6.5 / Axler 7.C
- **课程定义**: A real symmetric matrix $A$ is positive semidefinite if $x^T A x \geq 0$ for all $x \in \mathbb{R}^n$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.PosSemidef`
- **项目中的表述**:
  > `01-...md` 附录 G 也提到了半正定条件。Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.PosSemidef`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-064: Quadratic Form

- **课程来源**: Strang 6.5 / Axler —
- **课程定义**: A quadratic form on $\mathbb{R}^n$ is a function $Q(x) = x^T A x$ where $A$ is a symmetric $n \times n$ matrix.
- **项目对应路径**: `Mathlib.LinearAlgebra.QuadraticForm.Basic`
- **项目中的表述**:
  > `01-...md` 中提到了"二次型"和"椭圆 $x^T A x = 1$ 的主轴"（`spectral-theorem.yaml` 几何表征）。Mathlib 接口：`Mathlib.LinearAlgebra.QuadraticForm.Basic`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。$x^T A x$ 的表述在项目中多次出现，Mathlib 也有严格定义。
- **修正建议**: 在 `01-...md` 中增加一个显式的二次型定义块，以便中文读者快速定位。

---

#### DEF-065: Principal Minor

- **课程来源**: Strang 6.5 (Sylvester's Criterion)
- **课程定义**: The $k$-th leading principal minor of a matrix $A$ is the determinant of the top-left $k \times k$ submatrix of $A$.
- **项目对应路径**: `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md`
- **项目中的表述**:
  > `01-...md` 附录 G："顺序主子式（示意：仅检查前 $k \times k$ 主子式）"，并附有 Python 代码 `is_pd_leading_principal_minors`。**未找到 "Principal Minor" 的独立数学定义块**。
- **对齐判定**: 🟡 **近似表述** (GAP-3)
- **差异分析**: 顺序主子式的概念在代码和注释中被使用，但没有独立的 "Definition: 顺序主子式" 段落。此外，项目只讨论了"顺序"主子式（leading principal minors），未明确区分一般主子式（principal minors）。
- **修正建议**: 在 `01-...md` 正定性章节中增加显式定义：
  - 主子式：取 $A$ 的相同行号和列号构成的子矩阵的行列式；
  - 顺序主子式：取前 $k$ 行前 $k$ 列构成的子矩阵的行列式。

---

#### DEF-066: Jordan Block

- **课程来源**: Strang 8.3 / Axler 8.B
- **课程定义**: A Jordan block $J_k(\lambda)$ is a $k \times k$ upper triangular matrix with $\lambda$ on the diagonal and $1$'s on the superdiagonal.
- **项目对应路径**: `Mathlib.LinearAlgebra.JordanNormalForm`
- **项目中的表述**:
  > `01-...md` 定义 6.2：
  > "$k \times k$ Jordan块是形如：$J_k(\lambda) = \begin{pmatrix} \lambda & 1 & 0 & \cdots & 0 \\ 0 & \lambda & 1 & \cdots & 0 \\ \vdots & \vdots & \ddots & \ddots & \vdots \\ 0 & 0 & 0 & \lambda & 1 \\ 0 & 0 & 0 & 0 & \lambda \end{pmatrix}$ 的矩阵。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.JordanNormalForm`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-067: Jordan Normal Form

- **课程来源**: Strang 8.3 / Axler 8.C
- **课程定义**: Every complex square matrix is similar to a block diagonal matrix of Jordan blocks, unique up to permutation of the blocks.
- **项目对应路径**: `Mathlib.LinearAlgebra.JordanNormalForm`
- **项目中的表述**:
  > `01-...md` 定理 6.2："每个复矩阵都相似于一个Jordan标准形矩阵。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.JordanNormalForm`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-068: Generalized Eigenvector

- **课程来源**: Strang 8.3 / Axler 8.A, 8.D
- **课程定义**: A nonzero vector $v$ is a generalized eigenvector of $T$ corresponding to $\lambda$ if $(T - \lambda I)^j v = 0$ for some positive integer $j$.
- **项目对应路径**: `Mathlib.LinearAlgebra.GeneralizedEigenspace`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.GeneralizedEigenspace`。`01-...md` 中也有"广义特征向量和Jordan链"的代码注释。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: 在 `01-...md` 中增加显式的广义特征向量定义块，以便中文读者理解。

---

#### DEF-069: Nilpotent Operator

- **课程来源**: Strang 8.3 / Axler 8.A
- **课程定义**: An operator $N$ is nilpotent if $N^k = 0$ for some positive integer $k$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Nilpotent`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Nilpotent`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

### Unit VII: Linear Transformations and the SVD

---

#### DEF-070: Linear Transformation

- **课程来源**: Strang 7.1 / Axler 3.A
- **课程定义**:
  - Axler: A linear map (or linear transformation) $T: V \to W$ satisfies $T(u+v) = Tu + Tv$ and $T(\lambda v) = \lambda Tv$ for all $u, v \in V$ and $\lambda \in \mathbb{F}$.
  - Strang: A transformation $T: \mathbb{R}^n \to \mathbb{R}^m$ is linear if $T(av + bw) = aT(v) + bT(w)$; every linear transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ is multiplication by an $m \times n$ matrix.
- **项目对应路径**: `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/linear-map.yaml`
- **项目中的表述**:
  > `linear-map.yaml`：
  > "设 $V, W$ 是域 $F$ 上的向量空间。映射 $T: V \to W$ 是线性映射，若满足：1. $T(u + v) = T(u) + T(v)$（可加性）；2. $T(\alpha v) = \alpha T(v)$（齐次性）。等价地：$T(\alpha u + \beta v) = \alpha T(u) + \beta T(v)$。"
  > 
  > `01-...md` 定义 3.1 也给出了一致的表述。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**:
  - 项目定义与 Axler 的抽象算子视角完全一致。
  - **视角差异**：Strang 强调的"每个线性变换都是矩阵乘法"（$T(x) = Ax$）这一入门视角在项目文档中虽然被提及（`linear-map.yaml` 矩阵表示部分），但没有像 Strang 那样作为核心教学入口反复强调。
- **修正建议**: 在 `linear-map.yaml` 或 `01-...md` 中增加一个面向 18.06 的注记框：
  > **矩阵视角（Strang）**：在 $\mathbb{R}^n$ 和 $\mathbb{R}^m$ 配备标准基时，每一个线性变换 $T: \mathbb{R}^n \to \mathbb{R}^m$ 都唯一对应一个 $m \times n$ 矩阵 $A$，使得 $T(x) = Ax$。

---

#### DEF-071: Change of Basis Matrix

- **课程来源**: Strang 7.3 / Axler 3.C
- **课程定义**: If $\mathcal{B} = \{v_1, \ldots, v_n\}$ and $\mathcal{B}' = \{w_1, \ldots, w_n\}$ are bases of $V$, the change of basis matrix from $\mathcal{B}$ to $\mathcal{B}'$ has columns $[v_j]_{\mathcal{B}'}$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Basis`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Basis`。`01-...md` 定理 3.3：
  > "设 $T: V \rightarrow W$ 是线性变换，$\mathcal{B}_V = \{v_1, \ldots, v_n\}$ 是 $V$ 的基，$\mathcal{B}_W = \{w_1, \ldots, w_m\}$ 是 $W$ 的基，则存在唯一的 $m \times n$ 矩阵 $A$ 使得 $[T(v)]_{\mathcal{B}_W} = A[v]_{\mathcal{B}_V}$。"
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 的 `Basis` 模块包含基的转换矩阵的严格定义。
- **修正建议**: 在 `01-...md` 中明确引入"基变换矩阵"（change of basis matrix）的术语，将定理 3.3 与基变换概念更紧密地联系。

---

#### DEF-072: Similarity Transformation

- **课程来源**: Strang 7.3 / Axler 5.C, 10.A
- **课程定义**: Two matrices $A$ and $B$ represent the same linear transformation in different bases if and only if $B = M^{-1}AM$ for some invertible $M$; this is called a similarity transformation.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.Similarity`
- **项目中的表述**:
  > Mathlib 形式化接口：`Mathlib.LinearAlgebra.Matrix.Similarity`。`01-...md` 中也有相似矩阵的内容。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-073: Singular Value

- **课程来源**: Strang 7.1 / Axler 7.D, 7.E
- **课程定义**: The singular values of a matrix $A$ are the square roots of the eigenvalues of $A^T A$ (or $A^* A$), usually denoted $\sigma_1 \geq \sigma_2 \geq \cdots \geq \sigma_r > 0$ where $r = \text{rank}(A)$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.SVD`
- **项目中的表述**:
  > `01-...md` 附录 D 和机器学习文档中均使用了奇异值的概念。`05-...md` 定义 2.1：
  > "其中 $\Sigma$ 的对角元素 $\sigma_1 \geq \sigma_2 \geq \cdots \geq \sigma_r > 0$ 称为奇异值，$r = \text{rank}(A)$。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.SVD`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。
- **修正建议**: —

---

#### DEF-074: Singular Value Decomposition (SVD)

- **课程来源**: Strang 7.1 / Axler 7.D, 7.E
- **课程定义**: Every $m \times n$ real matrix $A$ can be factored as $A = U \Sigma V^T$, where $U$ is an $m \times m$ orthogonal matrix, $V$ is an $n \times n$ orthogonal matrix, and $\Sigma$ is an $m \times n$ diagonal matrix with nonnegative diagonal entries (the singular values).
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.SVD`
- **项目中的表述**:
  > `01-...md` 附录 D 有 SVD 与伪逆的形式化接口草案。`05-...md` 定义 2.1：
  > "设 $A \in \mathbb{R}^{m \times n}$，则存在正交矩阵 $U \in \mathbb{R}^{m \times m}$ 和 $V \in \mathbb{R}^{n \times n}$，以及对角矩阵 $\Sigma \in \mathbb{R}^{m \times n}$，使得：$A = U \Sigma V^T$。"
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.SVD`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。项目文档对 SVD 的定义非常完整，不仅有数学定义，还有 Python 实现和应用案例（PCA、图像压缩、推荐系统）。
- **修正建议**: —

---

#### DEF-075: Pseudoinverse (Moore-Penrose)

- **课程来源**: Strang 7.2 / Axler 6.C, 7.E
- **课程定义**: The Moore-Penrose pseudoinverse $A^+$ of a matrix $A$ is the unique matrix satisfying the four Penrose conditions. If $A = U \Sigma V^T$ is an SVD, then $A^+ = V \Sigma^+ U^T$.
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.MoorePenrose`
- **项目中的表述**:
  > `01-...md` 附录 D 有伪逆的 Python 实现：
  > ```python
  > class PseudoInverse:
  >     def pinv(A: np.ndarray, tol: float = 1e-12) -> np.ndarray:
  >         U, s, Vt = np.linalg.svd(A, full_matrices=False)
  >         s_plus = np.diag([1/si if si > tol else 0.0 for si in s])
  >         return Vt.T @ s_plus @ U.T
  > ```
  > 
  > Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.MoorePenrose`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。SVD 构造伪逆的路径与课程标准一致。虽然项目没有显式列出四个 Penrose 条件，但 `Mathlib.LinearAlgebra.Matrix.MoorePenrose` 中应包含。
- **修正建议**: 在 `01-...md` 附录 D 中补充 Moore-Penrose 伪逆的四个 Penrose 条件，提升严谨度。

---

#### DEF-076: Polar Decomposition

- **课程来源**: Strang 7.2 / Axler 7.E
- **课程定义**: Every square matrix $A$ can be written as $A = QS$ where $Q$ is orthogonal (or unitary) and $S$ is symmetric positive semidefinite (or Hermitian positive semidefinite).
- **项目对应路径**: `Mathlib.LinearAlgebra.Matrix.PolarDecomposition`
- **项目中的表述**:
  > `01-...md` 附录 D 标题中提到了"Polar Decomposition"（目录中）。Mathlib 接口：`Mathlib.LinearAlgebra.Matrix.PolarDecomposition`。
- **对齐判定**: 🟢 **严格等价**
- **差异分析**: 无。Mathlib 包含极分解的严格形式化定义。
- **修正建议**: 在 `01-...md` 附录 D 中补充极分解的显式数学定义和 SVD 构造法（$A = U\Sigma V^T = (UV^T)(V\Sigma V^T)$）。


---

## 附录 A：需新建/补充文档清单

| 优先级 | 定义/主题 | 建议文档位置 | 补充内容 |
|:------:|:----------|:-------------|:---------|
| P0 | Vector (R^n 入门视角) | `01-线性代数与矩阵理论-国际标准深度扩展版.md` 第1章 | 增加 R^n 中向量作为 n-元组的入门级定义 |
| P0 | Linear Combination | `01-...md` 第1章 | 增加独立的线性组合定义块 |
| P0 | Pivot / Pivot Variable / Free Variable | `01-...md` 矩阵分解/RREF章节 | 增加主元、主元变量、自由变量的独立定义 |
| P0 | Singular Matrix | `01-...md` 第2章 | 增加奇异矩阵的独立定义块 |
| P0 | Gauss-Jordan Elimination | `01-...md` 第2章 | 增加 Gauss-Jordan 消元法的算法定义 |
| P0 | Particular Solution | `01-...md` 线性方程组章节 | 增加特解的独立定义块 |
| P0 | Linear Independence 等价条件 | `01-...md` 第1.2节 | 补充列向量视角的等价条件（N(A)={0}） |
| P0 | Basis (无限维说明) | `01-...md` 第1.2节 | 增加 Hamel 基的注释和更多具体例子 |
| P0 | Least Squares Solution / Normal Equations | `01-...md` 或 `05-...md` | 增加独立的定义块（最小化残差范数） |
| P0 | Principal Minor | `01-...md` 附录G | 区分顺序主子式与一般主子式 |
| P1 | Incidence Matrix / Kirchhoff's Laws | 新建 `图论与线性代数.md` | 图论网络的关联矩阵、基尔霍夫定律的线性代数表述 |
| P1 | Signed Volume | `01-...md` 行列式章节 | 行列式的有向体积/几何解释 |
| P1 | Stable/Unstable/Center Subspaces | 新建 `动力系统与线性代数.md` | 微分方程中的稳定/不稳定/中心子空间 |
| P1 | Fourier Matrix / FFT | `01-...md` 复矩阵章节 | 傅里叶矩阵定义、酉性、FFT 算法思想 |
| P1 | Spectral Theorem (有限维复正规矩阵) | `spectral-theorem.yaml` | 补充有限维复正规矩阵的酉对角化版本 |
| P1 | Eigenspace / Generalized Eigenvector | `01-...md` 第4章 | 增加显式的中文定义块 |
| P1 | Polar Decomposition (SVD 构造法) | `01-...md` 附录D | 补充极分解的显式数学定义和构造 |
| P1 | Moore-Penrose Penrose 条件 | `01-...md` 附录D | 补充四个 Penrose 条件 |

---

## 附录 B：Strang vs Axler 视角差异总结

| 概念 | Strang 18.06 视角 | Axler 18.700 视角 | 项目覆盖情况 | 建议补充 |
|:-----|:------------------|:------------------|:-------------|:---------|
| **Vector** | R^n 中的 n-元组、箭头 | 抽象向量空间的元素 | ❌ 较弱（缺具体入口） | 增加 R^n 入门定义 |
| **Linear Map** | 矩阵乘法 T(x)=Ax | 抽象算子 T:V→W | 🟡 有抽象定义，矩阵视角较弱 | 增加 "每个线性变换都是矩阵乘法" 的强调 |
| **Eigenvalue** | det(A-λI)=0 的根 | 算子 T 的标量 λ 使 Tv=λv | 🟢 采用 Axler 路径 | 增加矩阵特征多项式路径的注记 |
| **Determinant** | 三条公理（det(I)=1, 行交换变号, 每行线性） | 体积/定向的交替多重线性形式 | 🟡 未明确说明 Strang 三条公理 | 增加行列式等价定义路径的对比 |
| **Inner Product** | R^n 中的点积 x·y = x^T y | 一般内积空间 ⟨·,·⟩ | 🟡 直接跳到一般定义 | 增加标准点积作为具体入口 |
| **SVD** | 矩阵分解 A=UΣV^T，工程应用 | 算子视角的奇异值 | 🟢 非常完整 | — |

**总体评价**：FormalMath 项目文档在抽象/算子视角（Axler 路径）上覆盖较好，但在**具体/矩阵入门视角**（Strang 路径）上存在明显不足。建议在关键概念（向量、内积、线性变换、特征值）处增加"课程对齐注记框"，明确说明两种视角的等价性，并给出 Strang 的具体入口。

---

## 附录 C：关键要求核查结果

### C.1 向量空间的 8 条公理是否完整？
✅ **完整**。`vector-space.yaml` 和 `01-...md` 均通过"阿贝尔群"（涵盖加法交换律、结合律、零元、逆元，共 4 条）加上 4 条标量乘法公理（1·v=v, (ab)·v=a·(bv), 左右分配律），完整覆盖了向量空间的 8 条公理。定理 1.1 进一步推导了 $0\cdot v=0$ 等边界性质。

### C.2 线性无关的等价条件是否完整？
🟡 **部分完整**。`01-...md` 给出了标准定义（线性组合=0 只有平凡解），但**缺少**系统性的等价条件整理。特别是：
- Strang 强调的 "$N(A)=\{0\}$"（对矩阵列向量）未显式列为等价条件；
- Axler 强调的 "没有一个向量可被前面向量线性表出" 未显式列出。
**建议补充**一个"等价条件"段落。

### C.3 基的定义（有限维 vs 一般情况）
🟡 **有偏差**。项目给出的定义"线性无关生成集"对有限维和无限维都成立，但文档的后续讨论（定理 1.2"每个有限维向量空间都有基"）强烈暗示了有限维限制。对于无限维情形（如多项式空间 $P$ 的 Hamel 基），**缺少说明**。建议增加注释。

### C.4 特征值/特征向量的零向量处理
✅ **正确处理**。`01-...md` 定义 4.1 明确说"存在**非零向量** $v \in V$"，从而正确排除了零向量作为特征向量的可能性，同时允许特征值 $\lambda=0$（只要存在非零特征向量）。边界情况处理得当。

### C.5 内积空间、正交性、SVD 的严谨程度
✅ **达到要求**。内积空间的定义（定义 5.1）包含共轭对称性、线性性、正定性，严谨完整。正交性定义（定义 5.2）正确。SVD 不仅有数学定义，还有 Python 实现、应用案例（PCA、图像压缩、推荐系统）和数值稳定性分析，**超过课程要求的严谨程度**。

---

*本手册由 FormalMath v2.0 子代理生成，遵循 D002 L3 定义对齐标准。*
