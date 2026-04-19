---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 01YC - 形式函数定理（Theorem on formal functions）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YC |
| **英文名称** | Theorem on formal functions |
| **中文名称** | 形式函数定理 |
| **所属章节** | Chapter 30: Cohomology of Sheaves (层的上同调) |
| **数学领域** | 代数几何、形式几何、层上同调 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息
- **URL**: https://stacks.math.columbia.edu/tag/01YC
- **章节**: 30.21 Theorem on formal functions
- **前置Tags**: 01YB (上同调与基变换), 01YA (高阶直像), 01X8 (完备化)

---

## 2. 定理/定义原文

### 2.1 形式函数定理（Theorem 30.21.1）

**设定**:
- f: X → S 是紧合态射（proper morphism）
- S 是局部Noether概形
- F 是 X 上的凝聚层（coherent sheaf）
- I ⊂ O_S 是理想层
- S_n = Spec(O_S/I^{n+1}) 是第 n 个无穷小邻域
- X_n = X ×_S S_n 是相应的无穷小形变

**定理陈述**:

对任意 i ≥ 0，存在典范同构：

widehat{(R^i f_* F)_s} ≅ lim_n H^i(X_n, F_n)

其中：
- 左边是 R^i f_* F 在点 s 处关于理想 m_s 的完备化
- 右边是纤维上同调的射影极限
- F_n 是 F 在 X_n 上的拉回

### 2.2 推论

**推论 30.21.2（Stein分解定理的代数版本）**:

若 f_* O_X = O_S，则对所有 s ∈ S，纤维 X_s 是连通的。

**推论 30.21.3（Zariski连通性原理）**:

设 f: X → S 是紧合态射，S 局部Noether。若 O_S → f_* O_X 是同构，则纤维的连通分支数是上半连续的。

### 2.3 导出版本

**命题 30.21.4**:

在导出范畴框架下，形式函数定理可以表述为：对 K ∈ D_{coh}^b(X)，有：

widehat{(Rf_* K)_s} ≅ Rlim_n RΓ(X_n, K|_{X_n})

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │  概形 X/S       │
                    │  紧合态射 f     │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 凝聚层 F   │ │ 理想层 I  │ │ 高阶直像  │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  无穷小形变   │
                    │  X_n = X ×_S S_n│
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  完备化       │
                    │  形式概形     │
                    │  Spf(Ô_{S,s})│
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │ 形式函数定理  │◄────────────┐
                    │              │             │
                    │ (R^i f_* F)_s^∧            │
                    │  ≅ lim H^i(X_n, F_n)       │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ Zariski │  │ Stein   │  │ 形变    │   │
       │ 连通性  │  │ 分解    │  │ 理论    │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │  形式完备化     │───────────┘
                    │  理论           │
                    └─────────────────┘
```

### 3.1 详细依赖链

```
概形理论基础
    ├── 紧合态射 f: X → S
    ├── 凝聚层理论
    │       ├── 凝聚层 F
    │       └── 凝聚层的上推 f_* F
    └── 形式几何
            ├── 完备化构造
            ├── 形式概形
            └── 无穷小形变

上同调理论
    ├── 高阶直像层 R^i f_*
    ├── 层上同调 H^i(X, F)
    └── Čech上同调

形式函数定理 ◄── 本Tag
    ├── 主定理：完备化 ≅ 射影极限
    ├── Stein分解推论
    └── Zariski连通性原理
```

---

## 4. 证明概要

### 4.1 形式函数定理证明

**核心策略**: 结合Čech上同调与射影极限的交换性

**证明步骤**:

1. **局部化**: 设 S = Spec(A)，I 对应理想 I ⊂ A

2. **Čech复形**: 选取 X 的有限仿射覆盖 U = {U_i}
   - 由于 f 紧合，纤维有限型，有限覆盖存在

3. **Čech复形计算**:
   H^i(X, F) = H^i(Čech^•(U, F))

4. **完备化与极限交换**:
   - 关键观察: Čech复形由 A-模组成
   - 完备化函子 ^∧ = lim_n (-)/I^{n+1}(-)
   
5. **有限性条件**:
   - 由Grothendieck的凝聚定理，H^i(X, F) 是有限 A-模
   - 对有限模，完备化与Čech上同调交换

6. **归纳论证**: 对 n 归纳，证明：
   (R^i f_* F) ⊗_A A/I^{n+1} ≅ H^i(X_n, F_n)

7. **取射影极限**: 得到形式函数定理

### 4.2 Stein分解推论证明

**推论 30.21.2 的证明**:

1. **假设**: f_* O_X = O_S

2. **应用形式函数定理** (i = 0):
   widehat{O_{S,s}} ≅ lim_n H^0(X_n, O_{X_n})

3. **纤维分析**: 若 X_s 不连通，则 H^0(X_s, O_{X_s}) 是非平凡的直积

4. **矛盾**: 与 widehat{O_{S,s}} 是局部环矛盾

### 4.3 Zariski连通性原理证明

**推论 30.21.3 的证明**:

1. **Stein分解**: 分解 f 为 X → S' → S
   - π_* O_X = O_{S'}
   - g 有限态射

2. **纤维连通性**: 由Stein分解，π 的纤维连通

3. **上半连续性**: g 的纤维数上半连续

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 紧合态射 | 紧合态射 | `concept/代数几何/紧合态射.md` |
| 凝聚层 | 凝聚层 | `concept/代数几何/凝聚层.md` |
| 高阶直像 | 高阶直像层 | `concept/代数几何/高阶直像层.md` |
| 完备化 | 完备化 | `concept/交换代数/完备化.md` |
| 形式概形 | 形式概形 | `concept/代数几何/形式概形.md` |
| 无穷小形变 | 无穷小形变 | `concept/代数几何/形变理论.md` |

### 5.2 Lean4形式化方向

```lean4
-- 形式函数定理的Lean4可能形式
import Mathlib.AlgebraicGeometry.FormalGeometry

-- 形式函数定理
theorem theorem_on_formal_functions {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S]
    (F : CoherentSheaf X) (s : S) (i : ℕ) :
    let I := s.asIdeal;
    Completion I ((R i f_* F).stalk s) ≅
    lim functor ⋙ (fun n ↦ 
      Scheme.cohomology i (X.infinitesimalNeighborhoood s n)
        (F.restrict (X.infinitesimalNeighborhoood s n))) := by
  sorry

-- Stein分解推论
theorem stein_factorization_connected_fibers {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S]
    (h : f_* (structureSheaf X) = structureSheaf S) :
    ∀ (s : S), IsConnected (f.fiber s) := by
  sorry
```

### 5.3 在知识体系中的位置

```
代数几何/概形理论
    ├── 紧合态射理论
    │       ├── 紧合态射定义
    │       ├── 高阶直像层
    │       └── 形式函数定理 ◄── 本Tag
    ├── 形式几何
    │       ├── 完备化构造
    │       ├── 形式概形
    │       └── 形式形变
    └── 复几何类比
            ├── Stein空间
            └── 复解析形式函数定理
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **连通性原理**
   - Zariski连通性定理
   - 纤维连通性的判定
   - 代数簇族的连通性

2. **Stein分解**
   - 紧合态射的典范分解
   - 双有理几何中的应用
   - 连通纤维的结构分析

3. **形变理论**
   - 形式形变的控制
   - 无穷小提升准则
   - 障碍理论

### 6.2 具体应用实例

| 应用领域 | 具体结果 | 定理引用 |
|----------|----------|----------|
| **双有理几何** | 例外轨迹的连通性 | Zariski主定理 |
| **模空间** | 模空间的紧化 | Deligne-Mumford紧化 |
| **Abel簇** | 对偶理论 | 对偶Abel簇的构造 |
| **曲面分类** | 收缩定理 | Castelnuovo-Enriques |

### 6.3 历史发展

- **O. Zariski (1950s)**: 代数曲面的连通性原理
- **J.-P. Serre (1956)**: GAGA原理中的形式函数
- **A. Grothendieck (EGA III)**: 一般形式的形式函数定理
- **H. Hironaka**: 奇点消解中的应用

### 6.4 现代发展

- **p-进Hodge理论**: 完美oid空间中的形式函数
- **非Archimedean几何**: Berkovich空间的应用
- **导出代数几何**: 高阶形式函数定理

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 01YB | 上同调与基变换 | 密切相关 |
| 01YA | 高阶直像 | 基础概念 |
| 01X8 | 完备化 | 基础构造 |
| 01XS | 平坦态射 | 相关概念 |
| 013Z | K-内射复形 | 导出范畴工具 |

### 7.2 外部资源

**教科书**:
- Hartshorne: "Algebraic Geometry" (第三章, §11)
- Vakil: "The Rising Sea" (第29章)
- Bosch-Lütkebohmert-Raynaud: "Néron Models" (形式几何)

**原始文献**:
- Grothendieck: EGA III.4, §4
- Zariski: "Theory and applications of holomorphic functions..."
- Serre: "Géométrie algébrique et géométrie analytique"

**现代综述**:
- Illusie: "Topics in algebraic geometry"
- Conrad: "Formal GAGA"

### 7.3 计算工具

- **Macaulay2**: 形式幂级数计算
- **SageMath**: 形式形变计算
- **Magma**: 代数形变理论

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 概形基础
✅ 层论基础
✅ 完备化构造
🔄 形式概形 (进行中)
⬜ 形式函数定理
⬜ 无穷小形变理论
```

### 8.2 形式化路线图

**阶段1: 形式几何基础** (预计12个月)
```lean4
-- 形式概形的定义
structure FormalScheme where
  underlyingTopologicalSpace : TopologicalSpace
  structureSheaf : SheafOfTopologicalRings
  -- 形式完备化条件
```

**阶段2: 无穷小形变** (预计18个月)
```lean4
-- 无穷小邻域
def infinitesimalNeighborhood {X S : Scheme} (f : X ⟶ S)
    (s : S) (n : ℕ) : Scheme :=
  pullback f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (s.asIdeal ^ (n + 1)))))
```

**阶段3: 形式函数定理** (预计30个月)
```lean4
-- 形式函数定理完整形式化
theorem formal_functions_theorem {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S] (F : CoherentSheaf X) :
    ∀ (s : S) (i : ℕ),
    Completion (R i f_* F).stalk s ≅
      limit (infinitesimalCohomologyFunctor f F s i) := by
  -- 基于Čech上同调的证明
```

### 8.3 技术挑战

1. **完备化函子**: 处理非Noether情形
2. **射影极限**: 阿贝尔范畴中的可表性
3. **Čech上同调**: 非仿射覆盖的一般理论

### 8.4 相关形式化项目

- **mathlib4#formal-schemes**: 形式概形理论
- **mathlib4#deformation**: 形变理论
- **Condensed Mathematics**: 形式完备化

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **形式函数定理** | widehat{(R^i f_* F)_s} ≅ lim_n H^i(X_n, F_n) |
| **无穷小邻域** | X_n = X ×_S Spec(O_S/I^{n+1}) |
| **完备化** | widehat{M} = lim_n M/I^{n+1}M |
| **Čech上同调** | H^i(X, F) = H^i(Čech^•(U, F)) |
| **Stein条件** | f_* O_X = O_S |

---

**文档版本**: 1.0  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10  
**作者**: FormalMath Knowledge System
