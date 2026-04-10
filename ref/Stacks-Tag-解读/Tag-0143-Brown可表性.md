# Stacks Project Tag 0143 - Brown可表性

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0143 |
| **定理名称** | Brown可表性定理 (Brown Representability) |
| **所属章节** | Section 13.14 - Brown可表性 (Derived Categories) |
| **数学领域** | 同调代数、三角范畴、代数几何 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/0143 |

## 2. 定理/定义原文

**Brown可表性定理 (Tag 0143):**

设 $\mathcal{D}$ 是紧生成三角范畴，$H: \mathcal{D}^{\text{opp}} \to \text{Ab}$ 是上同调函子（即：将三角变为长正合列，且与直和交换）。

则 $H$ 是可表的：存在对象 $X \in \mathcal{D}$ 使得 $H \cong \text{Hom}_{\mathcal{D}}(-, X)$。

**关键条件:**

1. **上同调函子 (Cohomological Functor):**
   - 将 distinguished triangle $A \to B \to C \to A[1]$ 变为长正合列
   - 保持直和：$H(\bigoplus X_i) = \prod H(X_i)$

2. **紧生成 (Compactly Generated):**
   - 存在紧对象集 $\{G_i\}$ 生成分类
   - 紧对象：$\text{Hom}(G, -)$ 与直和交换

**历史背景:**
- 原始版本由 **Edgar Brown** (1962) 在拓扑学中证明
- Neeman将其推广到三角范畴框架

## 3. 概念依赖图

```
Brown可表性 (Tag 0143)
│
├── 核心前置概念
│   ├── 三角范畴 (Tag 0144)
│   ├── 紧对象 (Tag 09SI)
│   ├── 上同调函子 (Tag 0142)
│   ├── 可表函子 (Tag 005O)
│   └── Yoneda引理 (Tag 001P)
│
├── 范畴论基础
│   ├── 加法范畴 (Tag 0013)
│   ├── Abel范畴 (Tag 0019)
│   ├── 导出范畴 D(𝒜) (Tag 05QI)
│   └── 直和/余积 (Tag 002P)
│
└── 后继应用
    ├── 伴随函子存在性 (Tag 0145)
    ├── 导出函子构造
    ├── Fourier-Mukai变换
    └── dg-范畴理论
```

## 4. 证明概要

**证明策略 (基于Neeman的方法):**

**Step 1: 构造近似对象**
- 令 $U = \bigoplus_i G_i$（所有生成元的直和）
- 构造递增的子对象序列 $X_0 \subset X_1 \subset X_2 \subset \cdots$

**Step 2: 归纳构造**
- **Base:** 从 $X_0 = 0$ 开始
- **Inductive Step:** 给定 $X_n$，构造 $X_{n+1}$
  - 考虑 $H(X_n) \to \prod_{f: G_i \to X_n} H(G_i)$
  - 添加"killers"来处理非零元素

**Step 3: 取直余极限**
- 定义 $X = \text{hocolim} X_n$
- 利用紧性证明 $H(X) = \text{colim} H(X_n)$

**Step 4: 验证可表性**
- 证明自然变换 $H \to \text{Hom}(-, X)$ 是同构
- 关键：在生成元上验证，然后延拓

**技术要点:**
- 使用 homotopy colimit (hocolim) 而非普通直余极限
- 紧性条件确保 $\text{Hom}(G, \text{hocolim} X_n) = \text{colim} \text{Hom}(G, X_n)$

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 三角范畴 | 范畴论/三角范畴 | `concept/category_theory/triangulated_category.md` |
| 紧对象 | 范畴论/紧对象 | `concept/category_theory/compact_object.md` |
| 可表函子 | 范畴论/可表函子 | `concept/category_theory/representable_functor.md` |
| 上同调函子 | 同调代数/上同调函子 | `concept/homological_algebra/cohomological_functor.md` |

**当前对齐状态:**
- ⚠️ **理论基础对齐** - 核心概念在文档中有描述
- 🔴 **形式化缺失** - 定理的完整证明细节待补充

**建议补充内容:**
```markdown
## Brown可表性详解

### 定理陈述
设 $\mathcal{D}$ 为紧生成三角范畴，$H: \mathcal{D}^{\text{opp}} \to \text{Ab}$ 满足：
1. $H$ 是上同调函子（保持三角）
2. $H$ 将直和变为直积

则存在 $X \in \mathcal{D}$ 使得 $H \cong h_X = \text{Hom}_{\mathcal{D}}(-, X)$。

### 紧生成条件
称 $\mathcal{D}$ 是**紧生成**的，如果存在紧对象集 $\mathcal{G}$ 使得：
$$\forall G \in \mathcal{G}: \text{Hom}(G, Y) = 0 \implies Y = 0$$

### 证明思想
1. 从生成元直和 $U$ 出发
2. 归纳构造逼近序列
3. 利用紧性保证极限行为良好
4. 验证泛性质

### 对偶形式
左可表性版本：对反变上同调函子 $H: \mathcal{D} \to \text{Ab}$
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 右伴随存在性 (Tag 0145)
- Brown可表性的直接推论：
- **定理:** 三角函子 $F: \mathcal{D} \to \mathcal{D}'$ 有右伴随当且仅当保持直和

### 2. 导出函子的右伴随
- 在代数几何中，$Rf_*$ 的右伴随（ exceptional inverse image ）存在性
- 这是Grothendieck对偶的基础

### 3. Fourier-Mukai变换
- 导出范畴间的等价性判定
- 通过可表性构造 kernel

### 4. t-结构的心 (Heart of t-structure)
- 判断子范畴是否为 Grothendieck 范畴
- 凝聚层范畴的可表性结果

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

Brown可表性是三角范畴理论的中心定理，是构造伴随函子和导出等价的基本工具。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 0144 | 三角范畴的定义 |
| Tag 0145 | 右伴随存在性推论 |
| Tag 09SI | 紧对象 |
| Tag 0142 | 上同调函子 |
| Tag 05QI | 导出范畴 |

### 外部资源

**原始文献:**
1. **Brown, E.** "Cohomology theories" (1962)
   - 拓扑学中的原始版本

2. **Neeman, A.** "The Grothendieck duality theorem via Bousfield's techniques..." (1996)
   - 三角范畴推广

**标准教材:**
1. **Neeman, A.** "Triangulated Categories"
   - 第8章系统阐述Brown可表性
   
2. **Huybrechts, D.** "Fourier-Mukai Transforms in Algebraic Geometry"
   - 第4章应用讨论

3. **Kashiwara & Schapira** "Sheaves on Manifolds"
   - 紧生成条件的验证技术

### 相关概念
- **Bousfield localization**: 紧密相关技术
- **Compactly generated triangulated categories**: Neeman的系统研究
- **Dg-categories**: 更一般的框架

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐⭐ (5/5)

**主要挑战:**
1. **三角范畴公理** - 复杂的octahedron axiom
2. **紧对象的无限直和交换性** - 涉及滤过余极限
3. **Homotopy colimit** - 高阶范畴构造
4. **Yoneda嵌入的延拓** - 稠密子范畴技术

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 紧对象的定义
class IsCompact {𝒞 : Type*} [Category 𝒞] [HasCoproducts 𝒞] (G : 𝒞) : Prop where
  -- Hom(G, -) 保持直和
  preserves_coproducts : ∀ {I : Type} (F : I → 𝒞),
    IsIso (coproductComparison G F)

-- 紧生成三角范畴
class CompactlyGenerated (𝒟 : Type*) [Category 𝒟] [TriangulatedCategory 𝒟] where
  -- 紧对象生成集
  generators : Set 𝒟
  isCompact : ∀ G ∈ generators, IsCompact G
  -- 生成条件
  generates : ∀ (Y : 𝒟), (∀ G ∈ generators, (G ⟶ Y) → False) → IsZero Y

-- 上同调函子
structure CohomologicalFunctor (𝒟 : Type*) [Category 𝒟] [TriangulatedCategory 𝒟]
    (H : 𝒟ᵒᵖ ⥤ Ab) : Prop where
  -- 将 distinguished triangle 变为长正合列
  distinguished_exact : ∀ (T : DistinguishedTriangle 𝒟),
    ExactSequence (H.map T.mor₁.op) (H.map T.mor₂.op)
  -- 与直和交换
  commutes_with_sum : ∀ {I : Type} (F : I → 𝒟),
    H.obj (⨁ F) ≅ ∏ (fun i => H.obj (F i))

-- Brown可表性定理
theorem brown_representability {𝒟 : Type*} [Category 𝒟] [TriangulatedCategory 𝒟]
    [CompactlyGenerated 𝒟] {H : 𝒟ᵒᵖ ⥤ Ab} (hH : CohomologicalFunctor 𝒟 H) :
    ∃ (X : 𝒟), H ≅ yoneda.obj X := by
  sorry -- 需要复杂的构造性证明
```

**Mathlib现状:**
- `TriangulatedCategory` 类型类正在开发中
- `IsCompact` 定义需要建立
- Homotopy colimit 尚无现成实现

**形式化优先级:** MEDIUM-HIGH
- 是高级同调代数的核心
- 建议在三角范畴基础稳固后推进
- 可考虑先形式化简化版本

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
