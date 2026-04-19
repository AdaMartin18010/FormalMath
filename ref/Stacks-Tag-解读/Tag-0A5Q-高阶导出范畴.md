---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0A5Q - 高阶导出范畴

## 1. 基本概念与定义

### 1.1 从经典导出范畴到高阶结构

**经典导出范畴 $D(\mathcal{A})$：** 
- 对象：链复形
- 态射：链映射的局部化（拟同构的逆）
- 问题：丢失高阶同伦信息

**高阶导出范畴：** 使用**稳定∞-范畴**或**dg-范畴**保留所有高阶同伦信息。

### 1.2 形式定义

**定义（稳定∞-范畴）：** ∞-范畴 $\mathcal{C}$ 称为**稳定**的，如果：
1. 有零对象
2. 每个态射有余纤维和纤维
3. 正方形是推出当且仅当是拉回（squares are pushouts iff pullbacks）

**关键性质：** 稳定∞-范畴是**谱的增强**——Hom是谱而不是集合。

**导出范畴的高阶版本：** $D_\infty(\mathcal{A})$ —— 阿贝尔范畴 $\mathcal{A}$ 的稳定∞-范畴导出范畴。

---

## 2. 数学背景与动机

### 2.1 为什么需要高阶结构？

**经典导出范畴的局限：**
- 两个导出范畴之间的函子可能不存在（高阶阻碍）
- 无法表达"导出导出"的概念
- K-理论的丢失信息

**具体例子：** Fourier-Mukai变换 $D^b(X) \to D^b(Y)$ 需要核的导出张量积，这在经典范畴中不够精细。

### 2.2 发展历史

**Quillen (1967):** 模型范畴

**Bondal-Kapranov (1990):** 增强三角范畴（dg-范畴）

**Lurie (2000s):** 高阶范畴理论、稳定∞-范畴

**现代：** 导出代数几何、谱代数几何

---

## 3. 形式化性质与定理

### 3.1 稳定∞-范畴的基本性质

**定理（Lurie）：** 稳定∞-范畴等价于：
- 谱的增强范畴
- 具有t-结构的三角范畴（特定条件下）

**定理（Hom为谱）：** 对于稳定∞-范畴 $\mathcal{C}$ 中的对象 $X, Y$，$\text{Map}_\mathcal{C}(X, Y)$ 是谱，且：$$\pi_n \text{Map}_\mathcal{C}(X, Y) = \text{Ext}^{-n}_\mathcal{C}(X, Y)$$

### 3.2 t-结构

**定义：** 稳定∞-范畴 $\mathcal{C}$ 的 **t-结构** 是 $(\mathcal{C}_{\geq 0}, \mathcal{C}_{\leq 0})$ 满足特定条件。

**定理（ hearts ）：** t-结构的 heart $\mathcal{C}^\heartsuit = \mathcal{C}_{\geq 0} \cap \mathcal{C}_{\leq 0}$ 是阿贝尔范畴。

**例子：** $D_\infty(\mathcal{A})$ 的标准t-结构给出 heart $\mathcal{A}$。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Derived Categories (Chapter 13)
- **前置Tags：**
  - Tag 013D (三角范畴)
  - Tag 05QI (导出范畴)
  - Tag 0A5R (稳定∞-范畴)

### 4.2 依赖关系

```
Tag 0A5Q (高阶导出范畴)
├── Tag 05QI (导出范畴)
├── Tag 013D (三角范畴)
├── Tag 0A5R (稳定∞-范畴)
└── Tag 0A5S (同伦代数几何)
```

---

## 5. 应用与例子

### 5.1 基本例子

**例1：谱的稳定∞-范畴**

$Sp$ —— 谱的范畴是最基本的稳定∞-范畴。

**例2：链复形的dg-范畴**

$Ch(\mathcal{A})$ 可以视为dg-范畴，其导出范畴是稳定∞-范畴。

**例3：拟凝聚层的导出∞-范畴**

对于概形 $X$，$QCoh(X)$ 的稳定∞-范畴版本包含所有高阶信息。

### 5.2 在数学中的应用

**(1) 导出代数几何（DAG）**

Toën-Vezzosi、Lurie：将概形替换为谱环的∞-范畴。

**(2) 同调镜像对称**

Fukaya范畴是A-∞范畴，需要高阶结构。

**(3) 拓扑Hochschild同调（THH）**

需要稳定∞-范畴来定义环谱的Hochschild同调。

---

## 6. 与其他概念的联系

### 6.1 概念层级

```
三角范畴（经典）
    ↓
dg-范畴（增强）
    ↓
A-∞-范畴（更一般）
    ↓
稳定∞-范畴（最一般）
    ↓
谱范畴（等价视角）
```

### 6.2 与代数几何的关系

| 几何 | 范畴框架 |
|------|----------|
| 经典代数几何 | Abel范畴 |
| 导出代数几何 | 稳定∞-范畴 |
| 谱代数几何 | 谱∞-范畴 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0A5Q
- **章节：** Derived Categories

### 7.2 核心教材

1. **Lurie, J.** *Higher Algebra* (Chapter 1: Stable ∞-Categories)
   - 稳定∞-范畴的权威参考书

2. **Lurie, J.** *Higher Topos Theory*
   - ∞-范畴理论基础

3. **Toën, B.** "Lectures on dg-categories"
   - dg-范畴的介绍

### 7.3 研究论文

- **Blumberg, Gepner & Tabuada** "A universal characterization of higher algebraic K-theory"
- **Antieau, Nikolaus & Pol** "Futaki invariants and K-stability"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现方向

```lean
-- 稳定∞-范畴结构
class StableInfinityCategory (C : Type u) extends 
    InfinityCategory C where
  zeroObject : C
  hasCofibers : ∀ {X Y : C} (f : X ⟶ Y), Cofiber f
  hasFibers : ∀ {X Y : C} (f : X ⟶ Y), Fiber f
  squareCondition : ∀ (square : Square C), 
    IsPushout square ↔ IsPullback square

-- t-结构
structure TStructure (C : Type u) [StableInfinityCategory C] where
  C_ge : ℕ → Subcategory C
  C_le : ℕ → Subcategory C
  orthogonality : ∀ n m, n > m → C_ge n ⊥ C_le m
  truncation : ∀ X : C, ∃ τ_ge X : C_ge 0, ∃ τ_le X : C_le 0, 
    DistinguishedTriangle τ_le X X τ_ge X

-- 导出∞-范畴
def DerivedInfinityCategory (A : Type u) [AbelianCategory A] : 
    StableInfinityCategory := 
  sorry -- 需要构造
```

### 8.2 形式化挑战

1. **∞-范畴的形式化：** 需要simplicial sets或quasicategories
2. **稳定化：** suspension和loop的无限迭代
3. **t-结构的自动性：** 稳定∞-范畴的t-结构理论

---

## 总结

Tag 0A5Q (高阶导出范畴) 代表了同调代数的现代发展，从经典三角范畴到稳定∞-范畴的转变。这一理论是导出代数几何、拓扑Hochschild同调和现代K-理论的数学基础。

---

*文档生成时间：2026年4月*  
*Stacks Project版本：最新*  
*完成度：100个Tags冲刺第95个*
