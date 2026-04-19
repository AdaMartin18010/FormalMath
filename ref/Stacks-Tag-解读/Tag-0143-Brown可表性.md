---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0143 - Brown可表性（Brown representability）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0143 |
| **英文名称** | Brown representability |
| **中文名称** | Brown可表性定理 |
| **所属章节** | Chapter 13: Derived Categories (导出范畴) |
| **数学领域** | 同调代数、范畴论、三角范畴 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息

- **URL**: https://stacks.math.columbia.edu/tag/0143
- **章节**: 13.19 Brown可表性
- **前置Tags**: 013Z (K-内射复形), 013M (导出范畴), 05Q2 (三角范畴)

---

## 2. 定理/定义原文

### 2.1 Brown可表性定理（Theorem 13.19.2）

**定理陈述**:

设 $\mathcal{D}$ 是紧生成三角范畴（compactly generated triangulated category），$H: \mathcal{D}^{\text{op}} \to \text{Ab}$ 是一个上同调函子（cohomological functor）。

则 $H$ 是可表的，即存在对象 $X \in \mathcal{D}$ 使得：

$$H(Y) \cong \text{Hom}_{\mathcal{D}}(Y, X)$$

对所有 $Y \in \mathcal{D}$ 自然成立。

### 2.2 关键定义

**定义 13.19.1 - 紧对象（Compact Object）**:

对象 $C \in \mathcal{D}$ 称为**紧的**，如果函子 $\text{Hom}_{\mathcal{D}}(C, -)$ 与任意直和交换：

$$\text{Hom}_{\mathcal{D}}\left(C, \bigoplus_{i \in I} X_i\right) \cong \bigoplus_{i \in I} \text{Hom}_{\mathcal{D}}(C, X_i)$$

**定义 - 紧生成（Compactly Generated）**:

三角范畴 $\mathcal{D}$ 称为**紧生成**的，如果：

1. $\mathcal{D}$ 有任意直和
2. 存在紧对象的小集合 $\mathcal{E}$，使得若 $\text{Hom}(E, X) = 0$ 对所有 $E \in \mathcal{E}$，则 $X = 0$

**定义 - 上同调函子**:

函子 $H: \mathcal{D}^{\text{op}} \to \text{Ab}$ 称为**上同调**的，如果对任意三角 $X \to Y \to Z \to X[1]$，序列

$$H(Z) \to H(Y) \to H(X)$$

是正合的。

### 2.3 导出范畴版本

**命题 13.19.3**:

设 $\mathcal{A}$ 是有足够内射元的Grothendieck Abel范畴。则导出范畴 $D(\mathcal{A})$ 是紧生成的。

特别地，对于上同调函子 $H: D(\mathcal{A})^{\text{op}} \to \text{Ab}$，存在 $K \in D(\mathcal{A})$ 使得：

$$H(M^\bullet) \cong \text{Hom}_{D(\mathcal{A})}(M^\bullet, K)$$

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │   三角范畴      │
                    │  (Triangulated) │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │  平移函子   │ │  正合三角   │ │  上同调    │
       │   [1]     │ │           │ │  函子      │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   紧对象       │
                    │ Compact Obj   │
                    │ Hom(C,-)保直和│
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │ 紧生成范畴     │
                    │Compactly Gen. │
                    │ ∃生成集ℰ     │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │ Brown可表性   │◄────────────┐
                    │ 定理          │             │
                    │ H ≅ Hom(-,X) │             │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ K-内射   │  │ 右伴随   │  │ 导出内射  │   │
       │ 复形     │  │ 存在性   │  │ 对象      │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                                                  │
                    ┌─────────────────┐           │
                    │ D(𝒜)紧生成性    │───────────┘
                    │ Grothendieck    │
                    │ 范畴导出范畴    │
                    └─────────────────┘
```

### 3.1 依赖链详细

```
Abel范畴 𝒜
    ↓
有足够内射元 → Grothendieck范畴
    ↓
导出范畴 D(𝒜)
    ↓
三角范畴结构（平移[1] + 正合三角）
    ↓
紧对象定义（Hom(C,-)与直和交换）
    ↓
紧生成性（存在生成紧对象的集合）
    ↓
Brown可表性定理 ←──── 上同调函子概念
    ↓
应用：K-内射复形存在性、右伴随存在性
```

---

## 4. 证明概要

### 4.1 Brown可表性定理证明

**核心思想**: 通过逐步逼近来构造表示对象

**证明步骤**:

1. **设定**:
   - 设 $\mathcal{E}$ 是紧对象的生成集
   - $H: \mathcal{D}^{\text{op}} \to \text{Ab}$ 是上同调函子

2. **构造表示对象**:

   a) **初始逼近**: 对 $E \in \mathcal{E}$，$H(E)$ 是Abel群，令：
   $$X_0 = \bigoplus_{E \in \mathcal{E}} \bigoplus_{h \in H(E)} E$$

   由Yoneda引理，存在 $h_0: H \to \text{Hom}(-, X_0)$

   b) **迭代构造**: 构造序列 $X_0 \to X_1 \to X_2 \to \cdots$ 使得：
      - Cone($X_n \to X_{n+1}$) 消除上同调
      - $H(X_n) \to H(X_{n+1})$ 逐步逼近

3. **同伦余极限**: 令 $X = \text{hocolim}\, X_n$

4. **验证**: 证明 $H(Y) \cong \text{Hom}(Y, X)$ 对所有 $Y$

### 4.2 导出范畴紧生成性证明

**命题 13.19.3 的证明**:

1. **紧对象识别**: 在 $D(\mathcal{A})$ 中，完美复形（perfect complexes）是紧的

2. **生成集构造**:
   - 取 $\mathcal{A}$ 的生成元集合 $\{G_i\}$
   - 对应复形 $\{G_i[0]\}$ 生成 $D(\mathcal{A})$

3. **验证**: 若 $\text{Hom}(G_i[n], M^\bullet) = 0$ 对所有 $i, n$，则 $M^\bullet \cong 0$

### 4.3 关键引理

**引理 13.19.4**: 设 $H: \mathcal{D}^{\text{op}} \to \text{Ab}$ 是可表上同调函子，则表示对象在相差同构下唯一。

**证明**: 由Yoneda引理直接得到。

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 三角范畴 | 三角范畴 | `concept/同调代数/三角范畴.md` |
| 紧对象 | 紧对象 | `concept/范畴论/紧对象.md` |
| 导出范畴 | 导出范畴 | `concept/同调代数/导出范畴.md` |
| 上同调函子 | 上同调函子 | `concept/同调代数/上同调函子.md` |
| Grothendieck范畴 | Grothendieck范畴 | `concept/范畴论/Grothendieck范畴.md` |

### 5.2 Lean4形式化概念

```lean4
-- 紧对象的Lean4可能形式化
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Basic

-- 紧对象定义
class CompactObject {C : Type u} [Category.{v} C] [HasCoproducts C]
    (X : C) : Prop where
  /-- Hom(X, -) 保持余积（直和）-/
  preserves_coproducts : ∀ {I : Type w} (Y : I → C),
    IsIso (coproductComparison (coyoneda.obj (op X)) Y)

-- 上同调函子定义
structure CohomologicalFunctor (C : Type u) [Category.{v} C]
    [Preadditive C] [HasShift C ℤ] [Pretriangulated C] where
  F : Cᵒᵖ ⥤ Ab
  cohomological : ∀ (T : Triangle C) (hT : T ∈ distTriang C),
    (F.map T.mor₃.op) ≫ (F.map T.mor₂.op) ≫ (F.map T.mor₁.op) = 0
```

### 5.3 在知识体系中的位置

```
代数几何/导出几何
    ├── 同调代数
    │       ├── 三角范畴
    │       │       ├── 正合三角
    │       │       ├── 平移函子
    │       │       └── Brown可表性 ◄── 本Tag
    │       └── 导出范畴
    │               ├── 紧生成性
    │               └── K-内射复形
    └── 代数几何应用
            ├── 导出像函子
            └── 对偶性理论
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **K-内射复形存在性**
   - 通过Brown可表性证明Grothendieck范畴中K-内射分解存在
   - 这是导出函子理论的基础

2. **右伴随存在性**
   - 三角函子存在右伴随的判定准则
   - 在导出范畴中自动给出各种导出函子

3. **导出内射对象**
   - 存在"导出内射"对象分类上同调函子
   - 类似经典内射对象的导出版本

### 6.2 代数几何应用

| 应用场景 | 说明 |
|----------|------|
| **上同调与基变换** | Brown可表性构造导出版本 |
| **对偶性理论** | Grothendieck对偶的存在性证明 |
| **Fourier-Mukai变换** | 核对象的存在性 |
| **稳定性条件** | Bridgeland稳定性中的Heart构造 |

### 6.3 历史背景

- **E.H. Brown (1962)**: 原始版本（拓扑学中谱的可表性）
- **A. Neeman (1996)**: 三角范畴推广，"The Grothendieck duality theorem..."
- **重要性**: 从拓扑学到代数几何的桥梁定理

### 6.4 现代发展

- **∞-范畴**: 高阶范畴中的可表性
- **导出代数几何**: 非交换几何中的应用
- **矩阵因子范畴**: 奇点理论中的应用

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 013Z | K-内射复形 | 主要应用 |
| 013M | 导出范畴 | 基础范畴 |
| 05Q2 | 三角范畴 | 基础概念 |
| 01YC | 形式函数定理 | 间接应用 |
| 08H4 | 导出Hom (RHom) | 导出函子构造 |

### 7.2 外部资源

**教科书**:

- Neeman: "Triangulated Categories" (核心参考书)
- Gelfand-Manin: "Methods of Homological Algebra" (附录)
- Kashiwara-Schapira: "Sheaves on Manifolds"

**原始论文**:

- Brown, E.H. "Cohomology theories", Ann. of Math. 75 (1962)
- Neeman, A. "The Grothendieck duality theorem via Bousfield's techniques...", J. Alg. Geom. (1996)

**现代综述**:

- Krause: "Localization theory for triangulated categories"
- Porta: "The Popescu-Gabriel theorem for triangulated categories"

### 7.3 相关软件

- **TriangulatedCategories (M2)**: Macaulay2包
- **DerivedCategories (Sage)**: 实验性实现

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 基础范畴论 (极限、余极限)
✅ 预三角范畴结构
🔄 三角范畴 (部分实现)
⬜ 紧生成范畴
⬜ Brown可表性定理
```

### 8.2 形式化路线图

**阶段1: 三角范畴完善** (预计6个月)

```lean4
-- 完整的三角范畴公理体系
class TriangulatedCategory (C : Type u) [Category.{v} C]
    [Preadditive C] [HasShift C ℤ] extends Pretriangulated C where
  -- 需要补充的公理
```

**阶段2: 紧对象理论** (预计6个月)

```lean4
-- 紧对象与紧生成性
structure CompactlyGenerated (C : Type u) [Category.{v} C]
    [HasCoproducts C] [Preadditive C] [HasShift C ℤ]
    [TriangulatedCategory C] where
  generators : Set C
  isCompact : ∀ c ∈ generators, CompactObject c
  generates : ∀ (X : C), (∀ c ∈ generators, ∀ n : ℤ,
    (c⟦n⟧ ⟶ X) = 0) → X = 0
```

**阶段3: Brown可表性** (预计12个月)

```lean4
-- Brown可表性定理
theorem brown_representability {C : Type u} [Category.{v} C]
    [HasCoproducts C] [Preadditive C] [HasShift C ℤ]
    [TriangulatedCategory C] [CompactlyGenerated C]
    (H : Cᵒᵖ ⥤ Ab) [H.IsCohomological] :
    ∃ (X : C), H ≅ yoneda.obj X := by
  -- 构造性证明
```

### 8.3 技术挑战

1. **大范畴问题**: 三角范畴通常涉及真类
2. **同伦余极限**: 需要发展三角范畴中的同伦理论
3. **集合论假设**: 可能需要选择公理或大基数假设

### 8.4 与其他形式化项目关联

- **Condensed Mathematics**: 凝聚数学中的导出范畴
- **Liquid Tensor Experiment**: 相关同调技术
- **Sphere Eversion**: 稳定同伦论联系

---

## 附录: 关键概念速查

| 概念 | 定义要点 |
|------|----------|
| **紧对象** | $\text{Hom}(C, \bigoplus X_i) \cong \bigoplus \text{Hom}(C, X_i)$ |
| **紧生成** | 紧对象集合 $\mathcal{E}$，$\text{Hom}(E, X) = 0 \forall E \Rightarrow X = 0$ |
| **上同调函子** | 将正合三角映到长正合列 |
| **可表性** | $H(Y) \cong \text{Hom}(Y, X)$ 自然同构 |
| **hocolim** | 同伦余极限，三角范畴中的构造 |

---

**文档版本**: 1.0
**创建日期**: 2026-04-10
**最后更新**: 2026-04-10
**作者**: FormalMath Knowledge System
