# Stacks Project Tag 01YB - 上同调与基变换（Cohomology and base change）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YB |
| **英文名称** | Cohomology and base change |
| **中文名称** | 上同调与基变换 |
| **所属章节** | Chapter 30: Cohomology of Sheaves (层的上同调) |
| **数学领域** | 代数几何、层上同调 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息
- **URL**: https://stacks.math.columbia.edu/tag/01YB
- **章节**: 30.20 Cohomology and base change
- **前置Tags**: 01XA (高阶直像), 01XS (平坦态射), 01YS (平坦基变换)

---

## 2. 定理/定义原文

### 2.1 基变换映射（Base Change Map）

**设定**:
考虑Cartesian图表：
```
X' ──► X
│      │
▼      ▼
S' ──► S
```

即 X' = X ×_S S'，设 f: X → S 是概形态射，f': X' → S' 是基变换后的态射。

**定义 - 基变换映射**:

对于 K ∈ D(O_X)，存在**基变换映射**（base change map）：

Lg^* Rf_* K → Rf'_* L(g')^* K

其中 g: S' → S 和 g': X' → X 是投影映射。

### 2.2 上同调与基变换定理

**定理 30.20.1（Cohomology and Base Change）**:

设 f: X → S 是紧合（proper）态射，S 是局部Noether概形，F 是 X 上的凝聚层。则：

**情形1**: 若 F 在 S 上平坦，则对 i ≥ 0，函数
s ↦ dim_{κ(s)} H^i(X_s, F_s)
是上半连续的。

**情形2**: 若基变换映射在某点 s ∈ S 是同构，则它在 s 的某个邻域上是同构。

**情形3（Grauert定理）**: 若 R^i f_* F 是局部自由的，则自然映射
(R^i f_* F)_s ⊗_{O_{S,s}} κ(s) → H^i(X_s, F_s)
是同构。

### 2.3 导出版本

**命题 30.20.2**:

设 f: X → S 是紧合且平坦的概形态射，S 局部Noether。则对于 K ∈ D_{coh}^b(X)，基变换映射在适当条件下是同构。

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │    概形 X/S     │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 凝聚层 O_X │ │  态射 f    │ │ 凝聚层 F  │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  导出范畴     │
                    │ D^b_{coh}(X) │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  高阶直像     │
                    │ R^i f_* F    │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  基变换图表   │
                    │  X'→X, S'→S │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │ 基变换映射    │◄────────────┐
                    │ Lg^* Rf_* K  │             │
                    │  → Rf'_* Lg'^* K            │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ 上半连续 │  │ Grauert  │  │ 形式函数 │   │
       │ 性定理   │  │ 定理     │  │ 定理     │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │ 平坦性条件      │───────────┘
                    │ F flat over S │
                    └─────────────────┘
```

### 3.1 依赖链详细

```
概形理论
    ├── 态射性质
    │       ├── 紧合态射 (Proper)
    │       ├── 平坦态射 (Flat)
    │       └── 有限展示态射
    └── 凝聚层理论
            ├── 凝聚层定义
            ├── 层的平坦性
            └── 纤维上同调 H^i(X_s, F_s)

导出范畴
    ├── 有界导出范畴 D^b_{coh}
    ├── 导出像函子 Rf_*
    └── 导出拉回 Lg^*

基变换理论
    ├── 基变换映射构造
    ├── 上同调与基变换定理 ◄── 本Tag
    └── Grauert半连续性定理
```

---

## 4. 证明概要

### 4.1 基变换映射的构造

**步骤1: 导出伴随**:
L(g')^* ⊣ R(g')_*

**步骤2: 单位态射**:
id → R(g')_* L(g')^*

**步骤3: 复合映射**:
Rf_* → Rf_* R(g')_* L(g')^* ≅ Rg'_* Rf'_* L(g')^*

**步骤4: 由伴随得到**:
Lg^* Rf_* → Rf'_* L(g')^*

### 4.2 上同调与基变换定理证明

**定理30.20.1 的证明策略**:

1. **局部化**: 可设 S = Spec(A)，S' = Spec(B)

2. **Čech上同调**: 用Čech复形计算上同调

3. **关键引理**: 若 C^• 是平坦 A-模的有界复形，则
   H^i(C^• ⊗_A B) ≅ H^i(C^•) ⊗_A B
   在某些条件下成立

4. **上半连续性**: 
   - 利用 R^i f_* F 是凝聚层
   - 纤维维数 dim H^i(X_s, F_s) 依赖于秩

5. **Grauert定理**: 
   - 若 R^i f_* F 局部自由，则基变换映射是同构
   -  Nakayama引理的应用

### 4.3 形式函数定理的联系

形式函数定理提供了基变换映射在完备化下的信息：

widehat{(R^i f_* F)_s} ≅ lim_n H^i(X_n, F_n)

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 紧合态射 | 紧合态射 | `concept/代数几何/紧合态射.md` |
| 平坦态射 | 平坦态射 | `concept/交换代数/平坦模.md` |
| 凝聚层 | 凝聚层 | `concept/代数几何/凝聚层.md` |
| 导出范畴 | 导出范畴 | `concept/同调代数/导出范畴.md` |
| 高阶直像 | 高阶直像层 | `concept/代数几何/高阶直像层.md` |
| 基变换 | 纤维积 | `concept/范畴论/纤维积.md` |

### 5.2 Lean4形式化方向

```lean4
-- 基变换映射的Lean4可能形式
import Mathlib.AlgebraicGeometry.DerivedCategory

-- 基变换映射
noncomputable def baseChangeMap {X S S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)
    (K : DerivedCategory X) :
    (g ^* ⋙ f.rightDerivedPushforward) K ⟶
    (f.baseChange g).rightDerivedPushforward ⋙ (pullback.snd f g) ^* K := by
  -- 构造基变换映射
  sorry

-- 上同调与基变换定理
theorem cohomology_and_base_change {X S : Scheme} [IsProper f] [LocallyNoetherian S]
    (F : CoherentSheaf X) [F.FlatOver S] :
    ∀ (s : S), IsIso (baseChangeMap f (Spec.map (CommRingCat.ofHom 
      (algebraMap Γ(S, ⊤) (Localization.AtPrime s.asIdeal))))) := by
  sorry
```

### 5.3 在知识体系中的位置

```
代数几何/概形上同调
    ├── 层上同调基础
    │       ├── 导出像函子 Rf_*
    │       ├── 高阶直像层 R^i f_*
    │       └── 基变换映射
    ├── 上同调与基变换 ◄── 本Tag
    │       ├── 紧合态射情形
    │       ├── 平坦性条件
    │       └── Grauert定理
    └── 形变理论应用
            ├── Kodaira-Spencer映射
            └── 模空间理论
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **Grauert半连续性定理**
   - 纤维维数的上半连续性
   - 复几何中重要工具

2. **形变理论**
   - 研究代数簇的形变
   - Kodaira-Spencer理论

3. **模空间理论**
   - Hilbert概形的性质
   - Picard概形的构造

### 6.2 具体定理应用

| 应用场景 | 定理/结果 | 说明 |
|----------|-----------|------|
| **Zariski主定理** | 双有理几何 | 紧合态射的纤维结构 |
| **Stein分解** | 复几何 | 紧合态射的分解 |
| **Riemann-Roch** | 曲线理论 | 相对版本的关键工具 |
| **Noether公式** | 曲面理论 | 示性类的计算 |

### 6.3 历史发展

- **H. Grauert (1960)**: 复解析情形的半连续性定理
- **A. Grothendieck (EGA III)**: 代数几何推广
- **M. Artin**: 代数空间中的应用

### 6.4 现代发展

- **导出代数几何**: 高阶版本的上同调与基变换
- **p-进Hodge理论**: 完美oid空间中的应用
- **对数几何**: 边界情形的推广

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 01YC | 形式函数定理 | 密切相关 |
| 01YS | 平坦基变换 | 基础定理 |
| 01YU | 上同调与平坦性 | 技术准备 |
| 01XA | 高阶直像 | 基础概念 |
| 013Z | K-内射复形 | 导出范畴工具 |
| 01XS | 平坦态射 | 基础概念 |

### 7.2 外部资源

**教科书**:
- Hartshorne: "Algebraic Geometry" (第三章, §12)
- Vakil: "The Rising Sea" (第30章)
- Liu: "Algebraic Geometry and Arithmetic Curves" (第五章)

**EGA参考文献**:
- EGA III, 7.7: 上同调与基变换
- EGA IV, 6: 平坦性与构造性质

**研究论文**:
- Grauert, H. "Ein Theorem der analytischen Garbentheorie..."
- Mumford: "Abelian Varieties" (应用实例)

### 7.3 计算工具

- **Macaulay2**: 上同调计算
- **SageMath**: 层上同调
- **Lean4/Mathlib4**: 形式化发展中

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 概形基础理论
✅ 层论基础
✅ 导出范畴框架
🔄 凝聚层理论 (进行中)
⬜ 紧合态射理论
⬜ 层上同调计算
⬜ 基变换理论
```

### 8.2 形式化路线图

**阶段1: 基础准备** (预计18个月)
```lean4
-- 紧合态射的形式化
class IsProper {X Y : Scheme} (f : X ⟶ Y) : Prop where
  universally_closed : ∀ (Z : Scheme) (g : Z ⟶ Y),
    IsClosedMap (pullback.fst f g)
  separated : IsSeparated f
  finite_type : LocallyOfFiniteType f
```

**阶段2: 层上同调** (预计24个月)
- 导出像函子的完整理论
- Čech上同调的等价性

**阶段3: 基变换理论** (预计30个月)
```lean4
-- 上同调与基变换定理
theorem cohomology_base_change {X Y Y' : Scheme} (f : X ⟶ Y)
    [IsProper f] [LocallyNoetherian Y] (g : Y' ⟶ Y)
    (F : CoherentSheaf X) [F.FlatOver Y] :
    IsIso (baseChangeMap f g F) := by
  -- Grauert证明策略
```

### 8.3 技术挑战

1. **Noether条件**: 局部Noether概形的处理
2. **非仿射覆盖**: 一般紧合态射的计算
3. **平坦性检验**: 平坦层的判定算法

### 8.4 相关项目

- **mathlib4#schemes**: 概形理论形式化
- **Liquid Tensor Experiment**: 相关同调技术
- **Condensed Mathematics**: 凝聚层上同调

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **基变换映射** | Lg^* Rf_* K → Rf'_* L(g')^* K |
| **纤维上同调** | H^i(X_s, F_s) = H^i(X ×_S Spec(κ(s)), F|_{X_s}) |
| **Grauert映射** | (R^i f_* F)_s ⊗ κ(s) → H^i(X_s, F_s) |
| **上半连续性** | {s | dim H^i(X_s, F_s) ≥ n} 是闭集 |

---

**文档版本**: 1.0  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10  
**作者**: FormalMath Knowledge System
