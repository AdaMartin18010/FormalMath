# ∞-范畴论：Mathlib4形式化状态

> Mathlib4中∞-范畴论相关定义的当前状态和路线图

---

## 1. 总体概述

### 1.1 项目目标

Mathlib4中的∞-范畴论形式化旨在：
1. 建立拟范畴 (quasicategories) 的基础理论
2. 开发∞-函子和∞-自然变换的理论
3. 形式化稳定∞-范畴的核心结果
4. 与Mathlib4的代数几何和代数拓扑模块整合

### 1.2 当前状态摘要

| 组件 | 状态 | 优先级 | 预计完成 |
|-----|------|-------|---------|
| 拟范畴定义 | ✅ 已实现 | 高 | 2024 |
| 内Kan条件 | ✅ 已实现 | 高 | 2024 |
| ∞-函子 | ✅ 已实现 | 高 | 2024 |
| 等价性判定 | 🔄 进行中 | 高 | 2025 Q2 |
| ∞-群胚 | 🔄 进行中 | 中 | 2025 Q3 |
| 稳定∞-范畴 | 📋 计划中 | 中 | 2025 Q4 |
| 导出∞-范畴 | 📋 计划中 | 中 | 2026 |
| 与拓扑空间联系 | 🔄 进行中 | 中 | 2025 Q3 |

---

## 2. 已实现内容详解

### 2.1 拟范畴基础

**文件位置**: `Mathlib/CategoryTheory/InfinityCategory/Quasicategory.lean`

**核心定义**:

```lean
-- 单纯集合
def SSet := SimplexCategoryᵒᵖ ⥤ Type*

-- 内角 (Inner Horn)
def innerHorn (n : ℕ) (i : Fin (n + 1)) (h : 0 < i ∧ i < n) : SSet := ...

-- 拟范畴定义
class Quasicategory (X : SSet) where
  innerKan : ∀ (n : ℕ) (i : Fin (n + 1)) (h : 0 < i ∧ i < n) 
    (f : innerHorn n i h ⟶ X), 
    ∃ (g : simplex n ⟶ X), f = hornToSimplex i h ≫ g
```

**已实现定理**:

1. **范畴的Nerve是拟范畴**:
```lean
theorem nerve_is_quasicategory (C : Type u) [Category.{v} C] :
  Quasicategory (nerve C) := ...
```

2. **Kan复形是拟范畴**:
```lean
theorem kan_complex_is_quasicategory (X : SSet) [KanComplex X] :
  Quasicategory X := ...
```

3. **填充的唯一性条件**:
```lean
def isInnerAnodyne {X Y : SSet} (f : X ⟶ Y) := ...
```

### 2.2 映射空间

**文件位置**: `Mathlib/CategoryTheory/InfinityCategory/MappingSpace.lean`

**定义**:

```lean
-- 映射空间 (对于拟范畴X, Y)
def mappingSpace (X Y : SSet) [Quasicategory Y] : SSet where
  obj Δ := (X ⊗ Δ) ⟶ Y
  map f g := g ∘ (X ⊗ f)

-- 证明映射空间也是拟范畴
instance (X Y : SSet) [Quasicategory Y] : Quasicategory (mappingSpace X Y) := ...
```

**关键结果**:

```lean
-- 映射空间的同伦群与态射的关系
theorem pi_zero_mapping_space_iso_homs (X Y : SSet) [Quasicategory X] [Quasicategory Y] :
  π₀ (mappingSpace X Y) ≅ homs (ho X) (ho Y) := ...
```

### 2.3 ∞-函子

**文件位置**: `Mathlib/CategoryTheory/InfinityCategory/Functor.lean`

```lean
-- ∞-函子就是单纯映射
def InfinityFunctor (X Y : SSet) [Quasicategory X] [Quasicategory Y] :=
  X ⟶ Y

-- ∞-自然变换
def InfinityNatTrans {X Y : SSet} [Quasicategory X] [Quasicategory Y]
  (F G : InfinityFunctor X Y) :=
  (Δ[1] ⊗ X) ⟶ Y  -- 满足适当的边界条件
```

---

## 3. 进行中工作

### 3.1 等价性理论

**文件位置**: `Mathlib/CategoryTheory/InfinityCategory/Equivalence.lean` (开发中)

**目标定理**:

```lean
-- Joyal的等价性判定
theorem joyal_equivalence_criterion {X Y : SSet} [Quasicategory X] [Quasicategory Y]
  (f : X ⟶ Y) :
  IsCategoricalEquivalence f ↔ 
    (IsWeakHomotopyEquivalence f ∧ IsFullyFaithful f) := ...
```

**当前进展**:
- ✅ 定义了范畴等价
- ✅ 定义了弱同伦等价
- 🔄 证明等价性判定的核心方向
- 📋 剩余方向的证明

### 3.2 ∞-群胚

**文件位置**: `Mathlib/CategoryTheory/InfinityCategory/InfinityGroupoid.lean` (开发中)

**定义**:

```lean
class InfinityGroupoid (X : SSet) extends Quasicategory X where
  allMorphismsInvertible : ∀ (x y : X _[0]) (f : x ⟶ y), IsEquivalence f
```

**Grothendieck假设的形式化**:

```lean
-- 奇异单纯函子
def singularSimplicialSet : TopCat ⥤ SSet := ...

-- 几何实现
def geometricRealization : SSet ⥤ TopCat := ...

-- 伴随关系
def singularGeoAdjunction : geometricRealization ⊣ singularSimplicialSet := ...

-- 主要定理（进行中）
theorem grothendieck_hypothesis :
  InfinityGroupoid ≌ TopCat[W^{-1}] := ...
```

**当前挑战**:
1. 局部化的形式化需要发展模型范畴理论
2. 同伦单位的证明涉及复杂的技术
3. 与代数拓扑已有结果的整合

### 3.3 与拓扑空间的联系

**相关文件**:
- `Mathlib/AlgebraicTopology/SimplicialSet.lean`
- `Mathlib/AlgebraicTopology/GeometricRealization.lean`

**状态**:
- ✅ 奇异单纯集合定义完成
- ✅ 几何实现定义完成
- ✅ 基本伴随关系证明完成
- 🔄 模型范畴结构（需要更多工作）
- 📋 弱等价的精确刻画

---

## 4. 计划中的工作

### 4.1 稳定∞-范畴

**路线图** (2025 Q3-Q4):

```lean
-- 稳定∞-范畴定义
class StableInfinityCategory (C : SSet) [Quasicategory C] where
  zeroObject : HasZeroObject C
  fibersCofibers : ∀ (f : morphism C), HasFiber f ∧ HasCofiber f
  stability : ∀ (triangle : FiberSequence C), IsCofiberSequence triangle

-- 悬挂等价
def suspensionEquivalence (C : SSet) [Quasicategory C] [HasZeroObject C] :
  C ≌ C := ...

-- 三角结构
def triangulatedStructure (C : SSet) [StableInfinityCategory C] :
  TriangulatedCategory (ho C) := ...
```

**依赖项**:
- 纤维序列的完整理论
- 同伦极限/余极限的形式化
- 预可加∞-范畴

### 4.2 导出∞-范畴

**路线图** (2026):

```lean
-- 从链复形构造导出∞-范畴
def derivedInfinityCategory (C : Type u) [Category.{v} C] [Abelian C] :
  SSet := ...

instance (C : Type u) [Category.{v} C] [Abelian C] :
  StableInfinityCategory (derivedInfinityCategory C) := ...

-- 与经典导出范畴的联系
theorem homotopy_category_iso_derived_category (C : Type u) [Category.{v} C] [Abelian C] :
  ho (derivedInfinityCategory C) ≅ DerivedCategory C := ...
```

**技术挑战**:
1. Dwyer-Kan局部化的形式化
2. 与已有同调代数结果的兼容
3. 计算效率的考虑

### 4.3 高阶结构

**未来方向**:

| 主题 | 描述 | 预计时间 |
|-----|------|---------|
| 伴随∞-函子 | 单位、余单位的高阶版本 | 2026+ |
| ∞-极限/余极限 | 通用性质的∞-版本 | 2026+ |
| ∞-Kan扩张 | 沿∞-函子的扩张 | 2026+ |
| 可表∞-函子 | ∞-Yoneda引理 | 2026+ |

---

## 5. 技术细节与挑战

### 5.1 当前技术栈

**使用的主要技术**:

1. **单纯数学**:
   - `SimplexCategory` - 单纯范畴的定义
   - `SimplicialObject` - 单纯对象的通用框架
   - `SSet` - 单纯集合的专门定义

2. **范畴论基础**:
   - `CategoryTheory.Functor`
   - `CategoryTheory.NaturalTransformation`
   - `CategoryTheory.Limits`

3. **代数拓扑**:
   - `AlgebraicTopology.SimplicialSet`
   - `AlgebraicTopology.GeometricRealization`
   - `AlgebraicTopology.DoldKan` (部分)

### 5.2 主要挑战

**挑战 1: 高阶同伦的操作**

```
问题: 处理n-单形的填充涉及复杂的归纳
状态: 已部分解决，使用自动化策略
下一步: 更强大的 tactic 支持
```

**挑战 2: 无穷构造**

```
问题: ∞-范畴涉及无穷的余极限
状态: 使用滤过余极限处理
下一步: 与Mathlib的极限框架更深度整合
```

**挑战 3: 一致性条件**

```
问题: 高阶一致性条件的验证
状态: 手动处理每个案例
下一步: 开发专用的一致性检查 tactic
```

### 5.3 性能考虑

**当前优化**:
- 使用 `reducible` 定义简化计算
- 延迟证明构造（lazy proof construction）
- 缓存常用的同伦计算

**未来优化**:
- 专门的数据结构表示拟范畴
- 增量式填充算法
- 与计算代数系统的接口

---

## 6. 与其他数学领域的联系

### 6.1 代数拓扑

```
AlgebraicTopology/
├── SimplicialSet.lean          ✅ 已完成
├── GeometricRealization.lean   ✅ 已完成
├── HomotopyGroup.lean          🔄 进行中
├── KanComplex.lean             ✅ 已完成
└── DoldKan.lean                🔄 进行中
```

**联系点**:
- Kan复形是特殊的拟范畴
- 奇异函子是∞-群胚的主要来源
- 同伦群可以从∞-群胚读出

### 6.2 代数几何

```
AlgebraicGeometry/
├── DerivedCategory.lean        🔄 进行中
├── PerfectComplex.lean         📋 计划中
└── SpectralScheme.lean         📋 远期
```

**联系点**:
- 导出∞-范畴是现代导出代数几何的基础
- 拟凝聚层的∞-范畴
- 完美的复形作为稳定∞-范畴

### 6.3 同伦类型论 (HoTT)

**潜在联系**:
- HoTT中的类型可以解释为∞-群胚
- 单值公理与∞-范畴论的关系
- 立方体类型论与单纯类型的对应

**状态**: 概念上的联系已建立，形式化整合是长期目标。

---

## 7. 贡献指南

### 7.1 如何参与

1. **阅读现有代码**:
   ```bash
   lake exe cache get
   lake build
   ```

2. **查看待办事项**:
   - GitHub Issues 标签 `infinity-categories`
   - Zulip 频道 `#mathlib4 > infinity-categories`

3. **提交贡献**:
   - 遵循Mathlib4的编码规范
   - 确保文档完整
   - 通过CI检查

### 7.2 优先任务

**高优先级** (2025 Q2):
- [ ] 完成等价性判定定理
- [ ] 形式化∞-群胚的基本群
- [ ] 证明Grothendieck假设的核心部分

**中优先级** (2025 Q3-Q4):
- [ ] 预可加∞-范畴
- [ ] 稳定∞-范畴的定义和基本性质
- [ ] 同伦极限/余极限

**长期目标** (2026+):
- [ ] 完整的导出∞-范畴理论
- [ ] 与代数几何的深度整合
- [ ] 计算工具开发

---

## 8. 参考资源

### 8.1 内部资源

- **Mathlib4文档**: https://leanprover-community.github.io/mathlib4_docs/
- **API参考**: `Mathlib/CategoryTheory/InfinityCategory/`
- **示例文件**: `Mathlib/CategoryTheory/InfinityCategory/Examples.lean`

### 8.2 外部资源

1. **Lurie, J.**: "Higher Topos Theory"
2. **Lurie, J.**: "Higher Algebra"
3. **Riehl & Verity**: "Elements of ∞-Category Theory"
4. **Cisinski**: "Higher Categories and Homotopical Algebra"

### 8.3 相关形式化项目

- **HoTT库** (Coq): https://github.com/HoTT/HoTT
- **UniMath** (Coq): https://github.com/UniMath/UniMath
- **Cubical Agda**: https://github.com/agda/cubical

---

## 9. 总结与展望

### 9.1 当前成就

✅ **已完成**:
- 拟范畴的基础定义和基本性质
- 内Kan条件的形式化
- 映射空间的构造
- ∞-函子的定义
- 与单纯集合和拓扑空间理论的联系

### 9.2 近期目标 (2025)

🔄 **进行中**:
- 等价性理论的完整形式化
- ∞-群胚理论的发展
- Grothendieck假设的证明
- 与代数拓扑结果的深度整合

### 9.3 长期愿景 (2026+)

📋 **计划中**:
- 完整的稳定∞-范畴理论
- 导出∞-范畴及其应用
- 与代数几何的整合
- 实用计算工具的开发

**最终目标**: 在Mathlib4中建立一个完整、实用的∞-范畴论框架，支持现代代数几何和代数拓扑的形式化研究。

---

*最后更新: 2026年4月 | FormalMath项目*
