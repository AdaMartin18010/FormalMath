---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 01W7 - 固有态射（Proper Morphisms）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01W7 |
| **章节** | Chapter 29: Morphisms of Schemes, Section 29.41 |
| **类型** | 定义 (Definition) |
| **重要性** | ★★★★★ (核心概念) |
| **位置** | Schemes, Definition 29.41.1 |

## 2. 定理/定义原文

### 英文原文

**Definition 29.41.1.** Let $f : X \to S$ be a morphism of schemes. We say $f$ is **proper** if $f$ is separated, finite type, and universally closed.

### 中文翻译

**定义 29.41.1.** 设 $f : X \to S$ 是概形态射。称 $f$ 是**固有的**（proper），如果 $f$ 满足：
1. 分离的（separated）
2. 有限型的（finite type）
3. 泛闭的（universally closed）

## 3. 概念依赖图

```
                    固有态射 (Proper Morphism)
                           |
          +----------------+----------------+
          |                |                |
       分离性           有限型           泛闭性
    (Separated)      (Finite Type)   (Universally
          |                |            Closed)
          |                |                |
          +----------------+----------------+
                           |
            核心动机：紧致性的代数类比
                           |
       +-------------------+-------------------+
       |                   |                   |
   射影态射            有限态射          Chow引理
   (Projective)       (Finite)         (Chow's Lemma)
       |                   |                   |
       +-------------------+-------------------+
                           |
                    典型应用：
                • 凝聚层的整体截面有限
                • 高阶直像凝聚
                • 模空间的紧化
```

**前置概念：**
- Tag 01T6: 分离态射（Separated Morphisms）
- Tag 01R0: 有限型态射（Finite Type Morphisms）
- Tag 01W0: 泛闭态射（Universally Closed Morphisms）

**依赖此概念：**
- 射影态射（Projective Morphisms）
- 平坦下降理论
- 凝聚层上同调
- 相交理论

## 4. 证明概要

### 4.1 基本性质的证明

**引理 29.41.4:** 固有态射的复合是固有的。

**证明：** 分别验证三个条件：
1. 分离性的复合保持（Schemes, Lemma 26.21.12）
2. 有限型的复合保持（Lemma 29.15.3）
3. 泛闭性的复合保持：闭映射的复合是闭的

**引理 29.41.5:** 固有态射的基变换是固有的。

**证明：** 分别验证三个条件在基变换下保持。

### 4.2 与射影态射的关系

**引理 29.41.7:** 设 $Y$ 在 $S$ 上分离，若有交换图：
```
X → Y
↓   ↓
  S
```
则 $X \to Y$ 是固有的当且仅当 $X \to S$ 是固有的。

**应用：** 这给出了验证固有性的有效方法——将态射分解为已知固有态射的复合。

### 4.3 Chow引理

**定理（Chow Lemma）:** 设 $S$ 是诺特概形，$f : X \to S$ 固有。则存在：
- 射影概形 $P$ 和 $S$-态射 $g : P \to X$
- $g$ 是满的、固有的，且在某个稠密开集上是同构

**意义：** 所有固有态射都是射影态射的"商"。

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `Separated` | 分离性 | `IsSeparated` ✓ |
| `FiniteType` | 有限型 | `LocallyOfFiniteType` ✓ |
| `UniversallyClosed` | 泛闭性 | 待形式化 |
| `Proper` | 固有态射 | `IsProper` (部分) |
| `Projective` | 射影态射 | 待形式化 |

**mathlib4对应代码：**
```lean
-- 固有态射的定义（计划中）
class IsProper {X Y : Scheme} (f : X ⟶ Y) : Prop where
  separated : IsSeparated f
  finiteType : LocallyOfFiniteType f
  universallyClosed : UniversallyClosed f

-- 射影态射蕴含固有（计划中）
instance {X Y : Scheme} (f : X ⟶ Y) [IsProjective f] : IsProper f := by
  -- 证明：射影空间是固有的，闭浸入是固有的
  sorry
```

## 6. 应用与重要性

### 6.1 与紧致性的类比

| 复几何/拓扑 | 代数几何 |
|------------|---------|
| 紧致复流形 | 固有概形（Proper over $\mathbb{C}$）
| 周炜良定理 | 固有性的代数定义
| 整体截面有限 | $H^0(X, \mathcal{F})$ 有限维（$\mathcal{F}$凝聚）

**关键区别：** 代数几何中，"紧致性"需要额外条件（分离性+泛闭性+有限型）。

### 6.2 凝聚层上同调

**定理（Grothendieck）:** 设 $f : X \to Y$ 固有，$\mathcal{F}$ 是 $X$ 上的凝聚层。则：
1. $R^i f_* \mathcal{F}$ 是 $Y$ 上的凝聚层
2. 若 $Y$ 是仿射的，$H^i(X, \mathcal{F})$ 是有限 $\mathcal{O}_Y(Y)$-模

这是代数几何中最重要的定理之一。

### 6.3 重要例子

| 态射 | 是否固有 | 说明 |
|------|---------|------|
| $\mathbb{P}^n_S \to S$ | ✓ | 射影空间是固有的 |
| 闭浸入 | ✓ | 闭子概形 |
| 有限态射 | ✓ | 有限⇒固有 |
| $\mathbb{A}^n_S \to S$ ($n > 0$) | ✗ | 仿射空间非固有 |
|  blow-up | ✓ | 双有理固有态射 |

### 6.4 valuative criterion

**定理:** $f : X \to S$ 是分离的且有限型的。则 $f$ 是固有的当且仅当满足：

对于任意 valuation ring $R$ 及其分式域 $K$，以及交换图：
```
Spec(K) → X
   ↓       ↓
Spec(R) → S
```
存在唯一的提升 $Spec(R) \to X$。

**直观：** 曲线上的有理映射可以唯一延拓到整点。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | II.4 | 固有态射的定义与性质 |
| Hartshorne | II.7 | 射影态射是固有的 |
| Hartshorne | III.8 | 高阶直像的凝聚性 |
| Vakil | 11.3 | 固有性的直观解释 |
| EGA II | §5 | 完整技术处理 |
| Liu | 3.3 | 中国背景教材 |

**Stacks Project交叉引用：**
- Tag 01T6: 分离态射
- Tag 01R0: 有限型态射
- Tag 01W0: 泛闭态射
- Tag 01W8: valuative criterion
- Tag 0205: Chow引理

## 8. Lean4形式化展望

### 8.1 当前挑战

```lean
-- 挑战1: 泛闭性的形式化
class UniversallyClosed (f : X ⟶ Y) : Prop where
  -- 所有基变换后都是闭映射
  baseChange_closed : ∀ {Z : Scheme} (g : Z ⟶ Y), 
    IsClosedMap (pullback.fst f g)

-- 挑战2: valuative criterion的形式化
theorem valuativeCriterion_proper {f : X ⟶ Y} 
    [IsSeparated f] [LocallyOfFiniteType f] :
    IsProper f ↔ ValuativeCriterion f := sorry
```

### 8.2 形式化路线图

```
阶段1: 前置概念 (进行中)
  ├── 分离性 ✓
  ├── 有限型 ✓
  └── 泛闭性 (待开发)

阶段2: 固有态射定义 (计划中)
  └── IsProper类型类

阶段3: 基本性质 (计划中)
  ├── 复合封闭性
  ├── 基变换封闭性
  └── valuative criterion

阶段4: 应用定理 (远期)
  ├── Chow引理
  ├── 凝聚层上同调
  └── Hilbert-Samuel理论
```

### 8.3 建议优先形式化

1. **分离性** - 已有基础 ✓
2. **有限型** - 已有基础 ✓
3. **闭映射** - 相对独立
4. **valuation ring** - 代数基础
5. **Chow引理** - 核心应用

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
