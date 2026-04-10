# Stacks Project Tag 01YB - 上同调与基变换

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YB |
| **定理名称** | 上同调与基变换 (Cohomology and Base Change) |
| **所属章节** | Section 30.9 - Cohomology and Base Change (Divisors) |
| **数学领域** | 代数几何、层上同调 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01YB |

## 2. 定理/定义原文

**定理 (Tag 01YB):**

设 $f: X \to S$ 是概形的拟紧分离态射，$\mathcal{F}$ 是 $X$ 上的拟凝聚层。考虑基变换图：

$$
\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S
}
$$

则存在**基变换映射**（canonical base change map）：

$$g^* R^pf_* \mathcal{F} \longrightarrow R^p f'_* (g')^* \mathcal{F}$$

**构造方法:**
该映射由以下泛性质给出：
1. $R^pf_*\mathcal{F}$ 是 $R^0f_*$ 的右导出函子
2. 由 $(g')^* \dashv R^0f'_*$ 的伴随性
3. 结合Leray谱序列或直接用导出范畴技术

**自然性:**
基变换映射是函子性的，且与连接同态兼容（在 long exact sequence 中）。

## 3. 概念依赖图

```
上同调与基变换 (Tag 01YB)
│
├── 核心前置概念
│   ├── 拟紧分离态射 (Tag 01KU)
│   ├── 拟凝聚层 (Tag 01LA)
│   ├── 高直像 R^pf_* (Tag 01E4)
│   ├── 层上同调 (Tag 01E1)
│   └── 基变换图/拉回图 (Tag 01JV)
│
├── 导出函子技术
│   ├── 导出范畴 (Tag 05QI)
│   ├── 导出函子 (Tag 05R1)
│   ├── 导出像 Rf_* (Tag 06YZ)
│   └── 拟同构 (Tag 05QR)
│
└── 后继应用
    ├── 形式函数定理 (Tag 01YC)
    ├── 平坦基变换 (Tag 01YS)
    ├── 半连续性定理 (Tag 0CCM)
    └── 可表函子的判别
```

## 4. 证明概要

**证明方法 (基于导出范畴):**

**Step 1: 导出层面的基变换**
在导出范畴 $D(X)$ 和 $D(S)$ 中，构造：
$$Lg^* Rf_* \mathcal{F}^\bullet \longrightarrow Rf'_* L(g')^* \mathcal{F}^\bullet$$

**Step 2: 定义构造**
- 利用伴随对 $(L(g')^*, R(g')_*)$ 和 $(Lf^*, Rf_*)$
- 由 $g \circ f' = f \circ g'$ 的自然同构诱导

**Step 3: 提取上同调映射**
- 对 $\mathcal{F}$（看作集中在0次的复形）
- 取 $R^pf_*$ 即 $H^p(Rf_*)$
- 基变换映射是上同调层面的诱导映射

**技术细节:**

**引理 (Tag 01YC前序):**
若 $S' \to S$ 是平坦的，则基变换映射是同构（平坦基变换定理）。

**证明要点:**
- 平坦性保证 $Lg^* = g^*$
- 利用K-内射消解计算 $Rf_*$
- 平坦拉回保持K-内射性（在适当条件下）

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 高直像 $R^pf_*$ | 代数几何/高直像 | `concept/algebraic_geometry/higher_direct_image.md` |
| 拟凝聚层 | 代数几何/拟凝聚层 | `concept/algebraic_geometry/quasi_coherent_sheaf.md` |
| 基变换图 | 范畴论/纤维积 | `concept/category_theory/fiber_product.md` |
| 导出像 $Rf_*$ | 代数几何/导出范畴 | `concept/algebraic_geometry/derived_direct_image.md` |

**当前对齐状态:**
- 🟡 **部分对齐** - 层上同调基础已建立，高阶导出函子技术待完善

**建议补充内容:**
```markdown
## 基变换映射详解

### 定义
对于基变换图：
```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```

**基变换映射**是典范态射：
$$g^* R^p f_* \mathcal{F} \to R^p f'_* (g')^* \mathcal{F}$$

### 构造方法
1. **层论方法**: 利用Cech上同调或Godement消解
2. **导出范畴方法**: 在 $D(X)$ 中构造 $Lg^* Rf_* \to Rf'_* L(g')^*$

### 平坦基变换定理
若 $g$ 平坦，则基变换映射是同构。

**证明要点:**
- 平坦拉回 $g^*$ 是正合的
- 与内射消解交换
- 保持上同调计算

### 应用: 半连续性
基变换映射的同构性是证明Grauert半连续性定理的关键。
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 形式函数定理 (Tag 01YC)
- 基变换映射是证明形式函数定理的核心工具
- 处理完备化与上同调的交换性

### 2. 半连续性定理
- **Grauert定理:** 高直像的秩的半连续性
- 构造模空间时的关键工具

### 3. 形变理论
- 研究概形族的上同调变化
- Kodaira-Spencer理论的代数版本

### 4. 平坦判别准则
- 通过基变换映射的行为判断平坦性
- **Hilbert多项式的稳定性**

### 5. 可表函子
- 构造Picard概形、Hilbert概形时的上同调技术

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

基变换定理是代数几何中应用最广泛的技术性定理之一，几乎在所有涉及族的构造中都不可或缺。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 01YC | 形式函数定理（直接应用） |
| Tag 01YS | 平坦基变换（特殊情形） |
| Tag 01E4 | 高直像的定义 |
| Tag 06YZ | 导出像 $Rf_*$ |
| Tag 0CCM | 半连续性定理 |
| Tag 01E1 | 层上同调基础 |

### 外部资源

**经典文献:**
1. **Grothendieck, A.** "Éléments de Géométrie Algébrique III"
   - 第7节系统阐述基变换理论

2. **Mumford, O.** "Abelian Varieties"
   - §5讨论上同调与基变换

**现代教材:**
1. **Hartshorne, R.** "Algebraic Geometry"
   - 第三章§12讨论平坦基变换

2. **Vakil, R.** "The Rising Sea: Foundations of Algebraic Geometry"
   - 第28章详述cohomology and base change

3. **Lazarsfeld, R.** "Positivity in Algebraic Geometry I"
   - 第一章回顾相关技术

### 相关技术
- **Leray谱序列**: 计算基变换的另一种方法
- **Formal functions**: 完备化技巧
- **Castelnuovo-Mumford正则性**: 相关的上同调消失技术

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐☆ (4/5)

**主要挑战:**
1. **导出层范畴** - 需要概形上的导出范畴
2. **高直像函子** - $Rf_*$ 的构造涉及K-内射消解
3. **平坦性条件** - 与基变换同构的关联
4. **层上同调** - 拟凝聚层的上同调理论

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 基变换图
structure BaseChangeDiagram where
  X S X' S' : Scheme
  f : X ⟶ S
  f' : X' ⟶ S'
  g : S' ⟶ S
  g' : X' ⟶ X
  comm : f' ≫ g = g' ≫ f
  isPullback : IsPullback f' g' f g

-- 基变换映射（层论版本）
def baseChangeMap {D : BaseChangeDiagram} (p : ℕ)
    (F : QCohSheaf D.X) :
    D.g^* (R p D.f_* F) ⟶ R p D.f'_* (D.g'^* F) := by
  sorry
  -- 构造基于导出范畴的伴随性

-- 平坦基变换定理
theorem flat_base_change_iso {D : BaseChangeDiagram} (p : ℕ)
    (F : QCohSheaf D.X) [Flat D.g] :
    IsIso (baseChangeMap p F) := by
  sorry
  -- 证明需要：
  -- 1. 平坦拉回的正合性
  -- 2. K-内射消解的拉回保持性
  -- 3. 谱序列论证
```

**Mathlib现状:**
- `Mathlib.AlgebraicGeometry` 已有概形基本理论
- `QCohSheaf` 类型正在发展中
- 导出层范畴尚未建立

**形式化优先级:** HIGH
- 是代数几何形式化的核心组件
- 建议在层上同调基础完成后重点推进
- 可先形式化平坦基变换的特殊情形

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
