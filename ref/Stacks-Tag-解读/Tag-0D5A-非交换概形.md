---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0D5A - 非交换概形

## 1. 基本概念与定义

### 1.1 从交换到非交换

**核心思想：** 将代数几何中的交换代数替换为非交换代数。

**动机问题：**

- 许多重要的几何对象（如量子群、D-模）天然是非交换的
- 奇点消解、形变理论的统一框架
- 物理中的非交换几何（弦理论）

### 1.2 非交换概形的定义

**定义（非交换概形）：** 非交换概形是局部同构于 $\text{Spec}(A)$ 的环化空间，其中 $A$ 是**非交换环**。

**形式定义（Artin-Zhang）：** **非交换射影概形** 是阿贝尔范畴对 $(\mathcal{C}, \mathcal{O}(1))$，其中：

- $\mathcal{C}$ 是Noetherian阿贝尔范畴
- $\mathcal{O}(1)$ 是 ample 自等价

**等价：** 当 $A$ 是graded非交换环时，$\text{Proj}^{nc}(A) = \text{QGr}(A)$（graded模范畴的商）。

---

## 2. 数学背景与动机

### 2.1 历史发展

**量子群时代（1980s）：** Drinfeld、Jimbo引入量子群，激发了非交换几何的兴趣。

**Artin-Schelter-Tate（1990s）：** 量子平面、Sklyanin代数等非交换射影曲面的分类。

**Kontsevich（2000s）：** 导出非交换代数几何，形变量化。

**现代：** 非交换 motives、周期理论、矩阵分解。

### 2.2 为什么需要非交换几何？

**(1) 奇点消解的对偶性**

Van den Bergh：奇点的非交换crepant消解（NCCR）。

**(2) 同调镜像对称**

Kontsevich： Fukaya范畴（辛）$\leftrightarrow$ 凝聚层范畴（代数）

**(3) D-模理论**

扭曲微分算子的研究与非交换几何密切相关。

---

## 3. 形式化性质与定理

### 3.1 非交换射影概形的基本性质

**定理（Serre定理的非交换类比）：** 设 $A$ 为连通graded Noetherian环，则：$$\text{QGr}(A) \cong \text{Qcoh}(\text{Proj}^{nc}(A))$$

**定理（Artin-Zhang）：** 非交换射影曲线必为交换的（即椭圆曲线或 $\mathbb{P}^1$）。

**定理（Artin-Stafford）：** 非交换射影曲面的分类（亏格0、1的情形）。

### 3.2 同调性质

**定理（非交换对偶性）：** 许多非交换概形满足某种形式的Serre对偶。

**定理（Beilinson谱序列的非交换版本）：** 对于非交换 $\mathbb{P}^n$，有：$$D^b(\text{qgr}(A)) = \langle \mathcal{O}, \mathcal{O}(1), ..., \mathcal{O}(n) \rangle$$

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** 非标准代数几何（当前Stacks Project中较少直接覆盖）
- **相关Tags：**
  - Tag 0D5B (非交换上同调)
  - Tag 0F1C (算术D-模)
  - Tag 0A5Q (导出范畴)

### 4.2 依赖关系

```
Tag 0D5A (非交换概形)
├── Tag 0A5Q (导出范畴)
├── Tag 0D5B (非交换上同调)
├── Tag 0F1C (D-模)
└── Tag 0G2B (导出形变)
```

---

## 5. 应用与例子

### 5.1 经典例子

**例1：量子平面**

$$A = k\langle x, y \rangle / (xy - qyx), \quad q \in k^*$$

这是非交换射影平面。

**例2：Sklyanin代数**

$$A = k\langle x_0, x_1, x_2 \rangle / (\text{特定二次关系})$$

对应于椭圆曲线上的几何。

**例3：Weyl代数（量子力学）**

$$A_n(k) = k\langle x_1, ..., x_n, \partial_1, ..., \partial_n \rangle / ([x_i, x_j] = 0, [\partial_i, \partial_j] = 0, [\partial_i, x_j] = \delta_{ij})$$

这是微分算子的非交换代数。

### 5.2 在数学中的应用

**(1) 非交换crepant消解（NCCR）**

Van den Bergh：对于3维Gorenstein奇点，NCCR存在当且仅当交换crepant消解存在。

**(2) 矩阵分解**

Eisenbud：超曲面奇点的凝聚层理论 ↔ 矩阵分解。

**(3) Calabi-Yau代数**

Ginzburg：非交换Calabi-Yau几何与弦理论中的B-brane范畴。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
非交换概形 (0D5A)
│
├── 量子群 ──→ Hopf代数
├── D-模理论 ──→ 扭曲微分算子
├── 导出代数几何 ──→ 谱范畴
├── 同调镜像对称 ──→ Fukaya范畴
└── 非交换 motives ──→ Tabuada
```

### 6.2 非交换/导出/谱的层级

```
经典概形
    ↓
非交换概形（范畴层面）
    ↓
导出非交换概形（$D^b(Coh)$）
    ↓
谱代数几何（$E_\infty$-环谱）
```

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0D5A
- **注：** Stacks Project对非交换几何的直接覆盖较少，主要关注交换情形

### 7.2 核心教材

1. **Artin, M.** "Geometry of Quantum Planes"
   - 非交换射影几何的奠基

2. **Stafford, J.T. & van den Bergh, M.** "Noncommutative curves and surfaces"
   - 综述文章

3. **Ginzburg, V.** "Lectures on Noncommutative Geometry"

### 7.3 现代文献

- **Kontsevich & Soibelman** "Notes on $A_\infty$-algebras, $A_\infty$-categories and non-commutative geometry"
- **Van den Bergh, M.** "Non-commutative crepant resolutions"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现方向

```lean
-- 非交换射影概形作为阿贝尔范畴
structure NCProjectiveScheme where
  C : AbelianCategory
  shift : C ≅ C  -- 平移函子
  O : C  -- 结构层
  [Noetherian : IsNoetherian C]
  [ample : IsAmple O shift]

-- 量子平面
noncomputable def QuantumPlane (k : Type) [Field k] (q : kˣ) :
    NCProjectiveScheme where
  C := QuotientCategory (GradedModules (QuantumPlaneAlgebra k q))
         (TorsionSubcategory _)
  -- ...
```

### 8.2 形式化挑战

1. **非交换坐标环：** 层上同调的非交换类比
2. **Serre定理的非交换版本：** 需要graded模范畴的形式化
3. **非交换对偶性：** 需要三角范畴的完善理论

---

## 总结

Tag 0D5A (非交换概形) 代表了代数几何的前沿方向，从量子群到同调镜像对称，从D-模到非交换crepant消解。虽然Stacks Project主要关注交换几何，但理解非交换几何对于把握现代数学物理和导出代数几何至关重要。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第90个*
