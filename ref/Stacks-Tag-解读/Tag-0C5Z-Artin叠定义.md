---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0C5Z - Artin叠定义

## 1. 基本概念与定义

### 1.1 叠（Stack）的动机

**问题背景：** 许多模问题（如曲线的模空间）无法由概形表示，因为对象存在自同构。

**解决方案：** 引入叠（Stack）——一种广义的"空间"，允许点具有自同构群。

### 1.2 Artin叠的正式定义

**定义（Artin叠）：** 设 $S$ 为概形，$\mathcal{X}$ 为 $(\text{Sch}/S)_{fppf}$ 上的范畴纤维化。称 $\mathcal{X}$ 为 **Artin叠**（或 **代数叠**），如果：

**(A1) 对角线表示性：** 对角线 $\Delta: \mathcal{X} \to \mathcal{X} \times_S \mathcal{X}$ 是表示性的、分离的、拟紧的。

**(A2) 光滑满射存在：** 存在 $S$-概形 $U$ 和光滑满射 $U \to \mathcal{X}$。

这样的 $U \to \mathcal{X}$ 称为 **光滑覆盖（smooth atlas）**。

### 1.3 关键概念解释

**表示性对角线：** 意味着任意两个对象的同构函子由概形表示。

**光滑覆盖：** 使叠"局部看起来像概形"。

---

## 2. 数学背景与动机

### 2.1 历史发展

**Deligne & Mumford (1969):** 引入Deligne-Mumford叠，用于研究代数曲线的模空间。

**Artin (1974):** 推广到Artin叠，允许更一般的 stabilizer（ stabilizer 可以是正维数群）。

**里程碑：**
- 1969: Deligne-Mumford叠 ($\overline{\mathcal{M}}_g$)
- 1974: Artin的形式形变理论
- 1990s: 叠的一般理论（Laumon-Moret-Bailly）

### 2.2 为什么需要Artin叠？

| 模问题 | 概形表示？ | 叠表示？ | 类型 |
|--------|-----------|----------|------|
| 椭圆曲线 ($\mathcal{M}_{1,1}$) | 否 | 是 | DM叠 |
| 秩 $r$ 向量丛 | 否 | 是 | Artin叠 |
| $GL_n$-主丛 | 否 | 是 | Artin叠 |
| 凝聚层 | 否 | 是 | Artin叠 |

**关键洞察：** Artin叠允许**正维数的自同构群**，这是研究 vector bundles、coherent sheaves 等模问题的必要条件。

---

## 3. 形式化性质与定理

### 3.1 Artin叠的基本性质

**定理（Artin叠的等价刻画）：** 范畴纤维化 $\mathcal{X}/S$ 是Artin叠当且仅当：

1. $\mathcal{X}$ 是 Stack in groupoids（满足下降条件）
2. 对角线 $\Delta_{\mathcal{X}}$ 是拟紧、分离、表示性的
3. 存在概形 $U$ 和光滑满射 $U \to \mathcal{X}$

**定理（表示性态射的复合）：** 若 $\mathcal{X} \to \mathcal{Y}$ 和 $\mathcal{Y} \to \mathcal{Z}$ 是表示性的，则 $\mathcal{X} \to \mathcal{Z}$ 也是表示性的。

### 3.2 与代数空间的关系

**定理：** Artin叠 $\mathcal{X}$ 是代数空间当且仅当对角线 $\Delta_{\mathcal{X}}$ 是单射（即无 stabilizers）。

**推论：** DM叠是Artin叠的特例，其中存在étale atlas（而不仅仅是光滑 atlas）。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Artin's Axioms (Chapter 96)
- **前置Tags：**
  - Tag 04XB (代数空间)
  - Tag 02ZI (Stack的形式定义)
  - Tag 04YY (Descent理论)

### 4.2 依赖关系

```
Tag 0C5Z (Artin叠)
├── Tag 04XB (代数空间)
├── Tag 02ZI (Stack)
├── Tag 04YY (Descent)
├── Tag 0C6A (DM叠)
└── Tag 0C6B (商叠)
```

---

## 5. 应用与例子

### 5.1 经典例子

**例1：向量丛叠 $BGL_n$**

$$BGL_n = [\text{pt}/GL_n]$$

- 对象：$S$-概形 $T$ 上的秩 $n$ 向量丛
- 态射：向量丛的同构
- 光滑覆盖：$\text{pt} \to BGL_n$

**例2：Hilbert叠**

$$\text{Hilb}_{\mathbb{P}^n}^P = \{\text{闭子概形 } Z \subseteq \mathbb{P}^n \text{ with Hilbert polynomial } P\}$$

这是Artin叠（实际上通常是代数空间）。

**例3：余切叠（Cotangent Stack）**

$$T^*\mathcal{X} = \text{Spec}_\mathcal{X}(\text{Sym}(\mathbb{T}_\mathcal{X}))$$

其中 $\mathbb{T}_\mathcal{X}$ 是叠的切复形。

### 5.2 在数学中的应用

**(1) 几何Langlands纲领**

Bun$_G$（$G$-丛的模叠）是Artin叠，几何Langlands对应的核心对象。

**(2) Gromov-Witten理论**

稳定映射叠 $\overline{\mathcal{M}}_{g,n}(X, \beta)$ 是Deligne-Mumford叠（因此也是Artin叠）。

---

## 6. 与其他概念的联系

### 6.1 概念层级

```
概形 ⊂ 代数空间 ⊂ DM叠 ⊂ Artin叠 ⊂ 代数叠 ⊂ Stack
```

**包含关系：**
- 概形：平凡 stabilizer，局部环结构
- 代数空间：étale等价关系，平凡 stabilizer
- DM叠：有限 stabilizer，étale atlas
- Artin叠：光滑 stabilizer，光滑 atlas

### 6.2 现代发展

| 理论 | 描述 | 代表 |
|------|------|------|
| 导出叠（Derived Stack） | 允许导出结构 | Toën-Vezzosi |
| 谱叠（Spectral Stack） | 叠的谱版本 | Lurie |
| 无限维叠 | 形式的Artin叠 | Gaitsgory-Rozenblyum |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0C5Z
- **章节：** Artin's Axioms

### 7.2 核心教材

1. **Laumon & Moret-Bailly** *Champs Algébriques*
   - Artin叠的标准参考书
   
2. **Olsson, M.** *Algebraic Spaces and Stacks*
   - 现代处理方式
   
3. **Artin, M.** "Versal deformations and algebraic stacks"
   - 原始论文

### 7.3 进阶文献

- **Behrend** "Derived l-adic categories for algebraic stacks"
- **Gaitsgory & Rozenblyum** *A Study in Derived Algebraic Geometry*

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现方向

```lean
-- Artin叠的定义结构
structure ArtinStack (S : Scheme) extends FiberedCategory (Over S) where
  -- 对角线表示性
  diagonalRepresentable : ∀ x y, Representable (Isom x y)
  -- 光滑覆盖存在
  smoothAtlas : ∃ U : Scheme, ∃ f : U ⟶ toFiberedCategory, 
    Smooth f ∧ Surjective f
  -- Stack条件（下降）
  stackCondition : IsStack toFiberedCategory
```

### 8.2 形式化挑战

1. **下降条件的验证：** 需要证明各种范畴满足fppf下降
2. **光滑覆盖的构造：** 具体模问题的覆盖构造
3. **对角线性质：** 表示性、分离性、拟紧性的组合

### 8.3 相关项目

- **mathlib4:** `CategoryTheory.FiberedCategory`
- **形式化代数几何：** 叠的形式化是长期目标

---

## 总结

Tag 0C5Z (Artin叠定义) 是现代代数几何的基石概念，它提供了处理带自同构的模问题的正确框架。从Deligne-Mumford叠到Artin叠的推广，使得向量丛、主丛等丰富几何对象的模理论成为可能。

---

*文档生成时间：2026年4月*  
*Stacks Project版本：最新*  
*完成度：100个Tags冲刺第84个*
