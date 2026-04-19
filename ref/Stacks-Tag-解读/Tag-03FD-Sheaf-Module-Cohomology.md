---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 03FD - 层上同调与模上同调等价

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 03FD |
| **章节** | Chapter 21: Cohomology of Sheaves, Section 21.12 |
| **类型** | 引理 (Lemma) |
| **重要性** | ★★★★☆ (重要工具) |
| **位置** | Cohomology of Sheaves, Lemma 21.12.4 |

## 2. 定理/定义原文

### 英文原文

**Lemma 21.12.4.** Let $\mathcal{C}$ be a site. Let $\mathcal{O}$ be a sheaf of rings on $\mathcal{C}$. Let $\mathcal{F}$ be an $\mathcal{O}$-module, and denote $\mathcal{F}_{ab}$ the underlying sheaf of abelian groups. Then we have

$$H^i(\mathcal{C}, \mathcal{F}_{ab}) = H^i(\mathcal{C}, \mathcal{F})$$

and for any object $U$ of $\mathcal{C}$ we also have

$$H^i(U, \mathcal{F}_{ab}) = H^i(U, \mathcal{F}).$$

Here the left hand side is cohomology computed in $\textit{Ab}(\mathcal{C})$ and the right hand side is cohomology computed in $\textit{Mod}(\mathcal{O})$.

### 中文翻译

**引理 21.12.4.** 设 $\mathcal{C}$ 是景（site），$\mathcal{O}$ 是 $\mathcal{C}$ 上的环层，$\mathcal{F}$ 是 $\mathcal{O}$-模，记 $\mathcal{F}_{ab}$ 为其底层的Abel群层。则我们有

$$H^i(\mathcal{C}, \mathcal{F}_{ab}) = H^i(\mathcal{C}, \mathcal{F})$$

且对 $\mathcal{C}$ 的任意对象 $U$ 也有

$$H^i(U, \mathcal{F}_{ab}) = H^i(U, \mathcal{F}).$$

这里左边是在 $\textit{Ab}(\mathcal{C})$ 中计算的上同调，右边是在 $\textit{Mod}(\mathcal{O})$ 中计算的上同调。

## 3. 概念依赖图

```
              层上同调与模上同调等价
           (Sheaf vs Module Cohomology)
                           |
          +----------------+----------------+
          |                |                |
      环层 O           O-模范畴         Abel群层
      (Ring Sheaf)    (Mod(O))       (Ab(C))
          |                |                |
          +----------------+----------------+
                           |
                    遗忘函子 (Forgetful Functor)
                           |
       +-------------------+-------------------+
       |                   |                   |
   正合性保持           δ-函子理论         泛性质
   (Exactness        (δ-functor         (Universal
    Preservation)      Theory)           Property)
```

**前置概念：**
- 景与层（Sites and Sheaves）
- Abel范畴的上同调
- δ-函子（δ-functors）
- 环层与模层

**依赖此概念：**
- 凝聚层上同调
- 平展上同调
- 结晶上同调
- 导出范畴中的等价性

## 4. 证明概要

### 4.1 核心思想

证明基于**泛δ-函子理论**：

1. 两个上同调理论都是**泛δ-函子**
2. 它们在0次上相同：$H^0(\mathcal{C}, \mathcal{F}_{ab}) = \Gamma(\mathcal{C}, \mathcal{F}) = H^0(\mathcal{C}, \mathcal{F})$
3. 泛性质保证它们在所有次数上同构

### 4.2 详细证明步骤

**步骤1：** 验证 $(\mathcal{F} \mapsto H^p(U, \mathcal{F}))_{p \geq 0}$ 是 $\textit{Mod}(\mathcal{O})$ 上的泛δ-函子

- 由导出范畴理论（Derived Categories, Lemma 13.20.4），这个δ-函子是泛的
- 因为 $\textit{Mod}(\mathcal{O})$ 有足够内射对象

**步骤2：** 验证 $(\mathcal{F} \mapsto H^p(U, \mathcal{F}_{ab}))_{p \geq 0}$ 也是泛δ-函子

- 遗忘函子 $\textit{Mod}(\mathcal{O}) \to \textit{Ab}(\mathcal{C})$ 是正合的
- 因此上述序列也是δ-函子
- 由泛性质的唯一性，两者同构

**步骤3：** 验证关键条件——内射对象的上同调消失

由 Homology, Lemma 12.12.4，只需证明：

若 $\mathcal{I}$ 是 $\textit{Mod}(\mathcal{O})$ 中的内射对象，则 $H^i(U, \mathcal{I}_{ab}) = 0$ 对所有 $i > 0$。

**关键引理 21.12.3：** 若 $\mathcal{I}$ 是内射 $\mathcal{O}$-模，则 $\mathcal{I}$ 是flasque的，因此 $H^i(U, \mathcal{I}) = 0$。

### 4.3 技术细节

**引理 21.12.3 的证明思路：**

1. 对于 $\mathcal{O}$-模的内射对象 $\mathcal{I}$，证明它是flasque的
2. 使用 flasque sheaf 的上同调消失性质
3. 这依赖于内射对象的特殊性质和限制映射的满射性

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `Site` | 景 $\mathcal{C}$ | `GrothendieckTopology` ✓ |
| `SheafOfRings` | 环层 $\mathcal{O}$ | `SheafOfRings` |
| `ModuleSheaf` | $\mathcal{O}$-模 $\mathcal{F}$ | `ModuleSheaf` |
| `AbelianSheaf` | Abel群层 | `SheafOfTypes` ✓ |
| `SheafCohomology` | $H^i(\mathcal{C}, -)$ | `SheafCohomology` |
| `DeltaFunctor` | δ-函子 | `DeltaFunctor` |

**mathlib4对应代码：**
```lean
-- 上同调函子
def sheafCohomology (C : Type*) [Category C] [GrothendieckTopology C]
    (F : SheafOfTypes C) (n : ℕ) : Type _ := ...

-- 环层上的上同调
def moduleSheafCohomology {C : Type*} [Category C] [GrothendieckTopology C]
    (O : SheafOfRings C) (F : ModuleSheaf O) (n : ℕ) : Type _ := ...

-- 等价定理（计划形式化）
theorem cohomology_forget_iso {C : Type*} [Category C] [GrothendieckTopology C]
    (O : SheafOfRings C) (F : ModuleSheaf O) (n : ℕ) :
    sheafCohomology C (F.forget) n ≅ moduleSheafCohomology O F n := by
  -- 使用泛δ-函子理论
  sorry
```

## 6. 应用与重要性

### 6.1 统一上同调理论

这个等价性意味着：

- **计算层面：** 可以使用Abel层上同调的工具计算模层上同调
- **理论层面：** 许多关于Abel层上同调的定理自动适用于模层
- **简化：** 避免了重复证明相同的结果

### 6.2 层化与预层上同调

**推论：** 预层上同调与层上同调的关系可以类似处理。

对于预层 $\mathcal{F}$，有谱序列：
$$E_2^{p,q} = H^p(\mathcal{C}, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(\mathcal{C}, \mathcal{F})$$

其中 $\mathcal{H}^q(\mathcal{F})$ 是上同调预层。

### 6.3 应用实例

**例1：凝聚层上同调**

在概形 $X$ 上，凝聚层 $\mathcal{F}$ 的上同调可以用：
- Abel层方法（Čech上同调）
- 或 $\mathcal{O}_X$-模方法（导出函子）

两种方法结果相同。

**例2：平展上同调**

对于平展拓扑，$
abla$-模的平展上同调可以用Abel群层计算。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | III.2 | 上同调的基本理论 |
| Grothendieck | Tohoku论文 | δ-函子的原始理论 |
| Godement | 层论 | flasque sheaf的理论 |
| Stacks | Tag 01F3 | 导出范畴基础 |
| Stacks | Tag 05T6 | 泛δ-函子 |

**Stacks Project交叉引用：**
- Tag 01F3: 导出范畴
- Tag 05T6: 泛δ-函子
- Tag 05TB: 同调中的δ-函子
- Tag 03OY: 层上同调基础

## 8. Lean4形式化展望

### 8.1 形式化策略

这个引理的形式化需要组合多个理论：

```lean
-- 关键组件1: 泛δ-函子的唯一性
theorem universal_delta_functor_unique {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F G : DeltaFunctor C D)
    (h0 : F 0 ≅ G 0) : ∀ n, F n ≅ G n := by
  -- 泛性质的推导
  sorry

-- 关键组件2: 模层上同调的泛性
instance sheafCohomology_universal {C : Type*} [Category C] [GrothendieckTopology C] :
    UniversalDeltaFunctor (sheafCohomology C) := by
  sorry

-- 关键组件3: 遗忘函子保持泛性
instance forget_universal {O : SheafOfRings C} :
    UniversalDeltaFunctor (fun F => sheafCohomology C (F.forget)) := by
  sorry
```

### 8.2 技术挑战

1. **δ-函子的范畴论**
   - 需要形式化δ-函子的范畴
   - 泛性质的表达

2. **内射对象的存在性**
   - 证明 $\textit{Mod}(\mathcal{O})$ 有足够内射对象
   - Grothendieck范畴的性质

3. **flasque层的技术**
   - 内射⇒flasque的证明
   - flasque层的上同调消失

### 8.3 建议路线图

```
阶段1: δ-函子理论 (进行中)
  └── DeltaFunctor类型类
  └── Universal性质
  └── 唯一性定理

阶段2: 层上同调基础 ✓
  └── sheafCohomology定义
  └── 基本性质

阶段3: 环层上同调 (计划中)
  └── moduleSheafCohomology定义
  └── 泛性证明

阶段4: 等价定理 (计划中)
  └── 遗忘函子的泛性
  └── 同构的构造
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
