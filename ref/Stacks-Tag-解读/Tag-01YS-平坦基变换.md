# Stacks Project Tag 01YS - 平坦基变换（Flat base change）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YS |
| **英文名称** | Flat base change |
| **中文名称** | 平坦基变换 |
| **所属章节** | Chapter 30: Cohomology of Sheaves (层的上同调) |
| **数学领域** | 代数几何、交换代数、层上同调 |
| **难度等级** | 研究生水平 |

### 1.1 位置信息

- **URL**: https://stacks.math.columbia.edu/tag/01YS
- **章节**: 30.18 Flat base change
- **前置Tags**: 01XS (平坦态射), 01XA (高阶直像), 01XB (Čech上同调)

---

## 2. 定理/定义原文

### 2.1 平坦基变换定理（Lemma 30.18.1）

**设定**:
考虑Cartesian图表（拉回图表）：

```
X' ──g'──► X
│          │
f'         f
▼          ▼
S' ──g───► S
```

其中：

- $f: X \to S$ 是概形态射
- $g: S' \to S$ 是**平坦**态射
- $X' = X \times_S S'$ 是纤维积
- $f': X' \to S'$ 是基变换后的态射

**定理陈述**:

对于 $X$ 上的任意拟凝聚层（quasi-coherent sheaf）$\mathcal{F}$，存在典范同构：

$$g^* R^i f_* \mathcal{F} \cong R^i f'_* (g')^* \mathcal{F}$$

对所有 $i \geq 0$ 成立。

等价表述：基变换映射
$$g^* R^i f_* \mathcal{F} \longrightarrow R^i f'_* (g')^* \mathcal{F}$$

在 $g$ 平坦时是同构。

### 2.2 导出范畴版本

**引理 30.18.2**:

设 $g: S' \to S$ 平坦，$f: X \to S$ 任意，则对 $K \in D_{\text{qc}}(X)$，基变换映射

$$Lg^* Rf_* K \longrightarrow Rf'_* L(g')^* K$$

是同构。

### 2.3 特殊情况

**情形1: 仿射态射**

若 $f$ 是仿射的，则 $R^i f_* \mathcal{F} = 0$ 对 $i > 0$，且：
$$g^* f_* \mathcal{F} \cong f'_* (g')^* \mathcal{F}$$

这是层条件（sheaf condition）的直接推论。

**情形2: 开浸入**

若 $g$ 是开浸入，则平坦基变换反映了上同调的局部性质。

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │   概形态射      │
                    │    f: X→S      │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 拟凝聚层   │ │ 平坦态射   │ │ 纤维积    │
       │    ℱ      │ │    g       │ │  X×_S S'  │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   高阶直像    │
                    │  R^i f_* ℱ   │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   拉回层      │
                    │  g^* R^i f_* ℱ│
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  平坦基变换   │◄────────────┐
                    │   定理        │             │
                    │  g^* R^i f_* ℱ              │
                    │  ≅ R^i f'_* g'^* ℱ          │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ 导出范畴 │  │ 层上同调 │  │ 上同调   │   │
       │ 版本     │  │ 与基变换 │  │ 维数不变 │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │  平坦性条件     │───────────┘
                    │  g flat over S │
                    └─────────────────┘
```

### 3.1 详细依赖链

```
交换代数基础
    ├── 平坦模 (Flat Module)
    ├── 平坦环同态
    └── 张量积正合性
        ↓
概形理论
    ├── 平坦态射定义
    ├── 拟凝聚层
    └── 纤维积构造
        ↓
层上同调
    ├── 高阶直像层 R^i f_*
    ├── Čech上同调
    └── 层拉回 g^*
        ↓
平坦基变换定理 ◄── 本Tag
    ├── 核心同构: g^* R^i f_* ≅ R^i f'_* g'^*
    ├── 导出范畴推广
    └── 上同调与基变换的基础
```

---

## 4. 证明概要

### 4.1 经典证明（Čech方法）

**证明步骤**:

1. **仿射化**: 可假设 $S = \text{Spec}(A)$，$S' = \text{Spec}(B)$
   - $g$ 平坦对应 $A \to B$ 平坦环同态

2. **Čech复形**: 选取 $X$ 的仿射开覆盖 $\mathcal{U} = \{U_i\}$

3. **关键观察**: Čech上同调计算
   $$H^i(X, \mathcal{F}) = H^i(\check{C}^\bullet(\mathcal{U}, \mathcal{F}))$$

4. **平坦性与张量积**:
   - 由于 $B$ 在 $A$ 上平坦，张量积 $-\otimes_A B$ 是正合函子
   - Čech复形与平坦基变换交换

5. **具体计算**:

   ```
   g^* R^i f_* ℱ = H^i(X, ℱ) ⊗_A B
                 ≅ H^i(Čech复形 ⊗_A B)
                 = H^i(Čech复形 of X')
                 = R^i f'_* g'^* ℱ
   ```

6. **层化**: 局部构造整体粘合成层同构

### 4.2 导出范畴证明

**引理 30.18.2 的证明**:

1. **基变换映射构造**: 由伴随函子的单位态射

2. **局部验证**: 对仿射概形验证是同构

3. **关键点**: $g$ 平坦意味着 $Lg^* = g^*$（无需导出）

4. **Čech-to-导出**: 证明Čech实现与导出函子一致

### 4.3 与上同调维数的关系

**推论**: 若 $g$ 平坦，则上同调维数满足：
$$\text{cd}(f') \leq \text{cd}(f)$$

其中 $\text{cd}(f)$ 是 $f$ 的上同调维数。

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 平坦态射 | 平坦态射 | `concept/代数几何/平坦态射.md` |
| 平坦模 | 平坦模 | `concept/交换代数/平坦模.md` |
| 拟凝聚层 | 拟凝聚层 | `concept/代数几何/拟凝聚层.md` |
| 高阶直像 | 高阶直像层 | `concept/代数几何/高阶直像层.md` |
| 纤维积 | 纤维积/拉回 | `concept/范畴论/纤维积.md` |
| Čech上同调 | Čech上同调 | `concept/代数拓扑/Čech上同调.md` |

### 5.2 Lean4形式化方向

```lean4
-- 平坦基变换的Lean4可能形式
import Mathlib.AlgebraicGeometry.Cohomology

-- 平坦基变换定理
theorem flat_base_change {X S S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] (F : QuasiCoherentSheaf X) (i : ℕ) :
    g ^* (R i f_* F) ≅ (R i (pullback.fst f g).pushforward)
                        ((pullback.snd f g) ^* F) := by
  -- 应用Čech上同调方法
  sorry

-- 导出范畴版本
noncomputable def flatBaseChangeIso {X S S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] (K : DerivedCategory.QuasiCoherent X) :
    g ^* ⋙ f.rightDerivedPushforward K ≅
    (pullback.fst f g).rightDerivedPushforward ⋙ (pullback.snd f g) ^* K := by
  sorry
```

### 5.3 在知识体系中的位置

```
代数几何/层上同调
    ├── 基础层论
    │       ├── 拟凝聚层
    │       ├── 层拉回与推出
    │       └── 平坦态射
    ├── 上同调理论
    │       ├── 层上同调 H^i
    │       ├── 高阶直像层 R^i f_*
    │       └── Čech上同调
    └── 基变换理论
            ├── 平坦基变换 ◄── 本Tag
            ├── 一般基变换映射
            └── 上同调与基变换
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **上同调计算简化**
   - 通过基变换简化问题到更简单的基概形
   - 计算相对上同调

2. **层平坦性判定**
   - 判定 $R^i f_* \mathcal{F}$ 的平坦性
   - 与上同调与基变换定理结合

3. **导出范畴理论**
   - 导出像函子的基变换
   - 六函子形式体系的基础

### 6.2 具体应用场景

| 应用场景 | 说明 |
|----------|------|
| **概形的平坦形变** | 研究形变中的上同调不变性 |
| **族的上同调** | 代数簇族的相对上同调计算 |
| **平展上同调** | 平展基变换的基本工具 |
| **fppf拓扑** | fppf下降理论的层论基础 |

### 6.3 历史背景

- **A. Grothendieck (EGA)**: 系统发展了平坦基变换理论
- **J.-P. Serre**: 层上同调的奠基工作
- **H. Cartan**: Čech上同调与层上同调的关系

### 6.4 现代发展

- **导出代数几何**: 高阶平坦基变换
- **刚性解析几何**: 刚性空间中的基变换
- **完美oid空间**: p-进几何中的推广

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 01YB | 上同调与基变换 | 推广版本 |
| 01YU | 上同调与平坦性 | 相关定理 |
| 01XS | 平坦态射 | 基础概念 |
| 01XA | 高阶直像 | 基础概念 |
| 01XB | Čech上同调 | 证明工具 |

### 7.2 外部资源

**教科书**:

- Hartshorne: "Algebraic Geometry" (第三章, §9)
- Vakil: "The Rising Sea" (第24章)
- Liu: "Algebraic Geometry and Arithmetic Curves" (第五章)

**EGA参考文献**:

- EGA III, 1.4: 平坦基变换
- EGA IV, 2: 平坦性与局部化

**研究论文**:

- Illusie: "Complexe cotangent et déformations"
- Conrad: "Grothendieck Duality and Base Change"

### 7.3 相关课程与讲义

- **Stanford Math 245C**: 层上同调与基变换
- **Harvard Math 260X**: 代数几何进阶
- **MIT 18.726**: 代数几何II

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 平坦模理论
✅ 平坦环同态
✅ 拟凝聚层基础
🔄 层上同调计算 (进行中)
⬜ 高阶直像层
⬜ 平坦基变换定理
```

### 8.2 形式化路线图

**阶段1: 层上同调基础** (预计12个月)

```lean4
-- 高阶直像层的完整定义
def higherDirectImage {X Y : Scheme} (f : X ⟶ Y)
    (F : Sheaf Ab X) (i : ℕ) : Sheaf Ab Y :=
  (presheafToSheaf _ (λ U ↦
    (CochainComplex.homology (Γ (f ⁻¹ᵁ U) F) i)))
```

**阶段2: Čech上同调** (预计18个月)

- Čech复形的形式化
- Čech上同调与导出函子的等价性

**阶段3: 平坦基变换** (预计24个月)

```lean4
-- 平坦基变换定理
theorem flatBaseChangeTheorem {X S S' : Scheme}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    (F : QuasiCoherentSheaf X) (i : ℕ) :
    g.pullback (R i f.directImage F) ≅
      R i (pullback.fst f g).directImage ((pullback.snd f g).pullback F) :=
  by
  -- 基于Čech方法的证明
  apply Čech_cohomology_base_change
  -- 验证Čech复形与平坦基变换交换
  apply flat_preserves_Čech_complex
```

### 8.3 技术挑战

1. **层上同调计算**: 一般概形上的有效计算
2. **Čech-导出等价**: 严格的形式化证明
3. **平坦性判定**: 算法化判定方法

### 8.4 相关形式化项目

- **mathlib4#schemes**: 概形理论
- **mathlib4#sheaf-cohomology**: 层上同调
- **Liquid Tensor Experiment**: 相关技术

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **平坦基变换** | $g^* R^i f_* \mathcal{F} \cong R^i f'_* (g')^* \mathcal{F}$ |
| **导出版本** | $Lg^* Rf_* K \cong Rf'_* L(g')^* K$ |
| **Čech复形** | $\check{C}^p(\mathcal{U}, \mathcal{F}) = \prod_{i_0 < \cdots < i_p} \mathcal{F}(U_{i_0} \cap \cdots \cap U_{i_p})$ |
| **平坦性条件** | $-\otimes_A B$ 正合，当 $A \to B$ 平坦 |

---

**文档版本**: 1.0
**创建日期**: 2026-04-10
**最后更新**: 2026-04-10
**作者**: FormalMath Knowledge System
