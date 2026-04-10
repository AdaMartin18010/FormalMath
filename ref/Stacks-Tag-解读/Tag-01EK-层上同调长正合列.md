# Stacks Project Tag 01EK - 层上同调的长正合列

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/01EK)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01EK |
| **英文名称** | Long Exact Sequence of Čech Cohomology |
| **中文名称** | 层上同调的长正合列 |
| **数学分支** | 层上同调 / 同调代数 |
| **所属章节** | Cohomology of Sheaves |
| **难度等级** | 中等 |

**前置知识要求**：短正合列、Čech复形、连接同态、蛇引理

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Lemma 01EK.** Let $X$ be a topological space. Let $\mathcal{U} : U = \bigcup_{i \in I} U_i$ be an open covering. Let

$$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$$

be a short exact sequence of abelian sheaves on $X$. Then there is a long exact sequence of Čech cohomology groups:

$$0 \to \check{H}^0(\mathcal{U}, \mathcal{F}) \to \check{H}^0(\mathcal{U}, \mathcal{G}) \to \check{H}^0(\mathcal{U}, \mathcal{H}) \to \check{H}^1(\mathcal{U}, \mathcal{F}) \to \check{H}^1(\mathcal{U}, \mathcal{G}) \to \cdots$$

### 中文翻译

**引理 01EK.** 设 $X$ 为拓扑空间，$\mathcal{U} : U = \bigcup_{i \in I} U_i$ 为一开覆盖。设

$$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$$

为 $X$ 上阿贝尔层的短正合列。则存在Čech上同调群的长正合列：

$$0 \to \check{H}^0(\mathcal{U}, \mathcal{F}) \to \check{H}^0(\mathcal{U}, \mathcal{G}) \to \check{H}^0(\mathcal{U}, \mathcal{H}) \to \check{H}^1(\mathcal{U}, \mathcal{F}) \to \check{H}^1(\mathcal{U}, \mathcal{G}) \to \cdots$$

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │    短正合列         │
                    │ 0→ℱ→𝒢→ℋ→0         │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │ Čech复形   │  │ Čech复形   │  │ Čech复形   │
       │ Ĉ^•(𝒰,ℱ)  │  │ Ĉ^•(𝒰,𝒢)  │  │ Ĉ^•(𝒰,ℋ)  │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │ 复形的短正合列   │
                    │ 0→Ĉ^•(ℱ)→      │
                    │   Ĉ^•(𝒢)→      │
                    │   Ĉ^•(ℋ)→0     │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   蛇引理        │
                    │ Snake Lemma     │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │  长正合列   │ │ 连接同态 δ │ │ 同调群同态  │
       │ Ĥ^p(𝒰,-)   │ │ Ĥ^p→Ĥ^{p+1}│ │ 自然性     │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **短正合列**：$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$，其中每处正合
- **Čech复形**：基于覆盖的上链复形
- **蛇引理 (Snake Lemma)**：从复形的短正合列导出长正合列的核心工具
- **连接同态**：$\delta: \check{H}^p(\mathcal{U}, \mathcal{H}) \to \check{H}^{p+1}(\mathcal{U}, \mathcal{F})$

---

## 4. 证明概要

### 核心命题

短正合列 $0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$ 诱导Čech复形的短正合列，进而导出上同调的长正合列。

### 证明步骤

**Step 1: 层的短正合列诱导Čech复形的短正合列**

对于每个 $p \geq 0$，层短正合列在每个交集 $U_{i_0} \cap \cdots \cap U_{i_p}$ 上限制仍正合：

$$0 \to \mathcal{F}(U_{i_0} \cap \cdots \cap U_{i_p}) \to \mathcal{G}(U_{i_0} \cap \cdots \cap U_{i_p}) \to \mathcal{H}(U_{i_0} \cap \cdots \cap U_{i_p}) \to 0$$

由于积保持正合性，得到Čech复形的短正合列：

$$0 \to \check{C}^\bullet(\mathcal{U}, \mathcal{F}) \to \check{C}^\bullet(\mathcal{U}, \mathcal{G}) \to \check{C}^\bullet(\mathcal{U}, \mathcal{H}) \to 0$$

**Step 2: 应用蛇引理**

对于复形的短正合列，蛇引理给出连接同态：

$$\delta^p : H^p(\check{C}^\bullet(\mathcal{U}, \mathcal{H})) \to H^{p+1}(\check{C}^\bullet(\mathcal{U}, \mathcal{F}))$$

**Step 3: 构造长正合列**

结合自然映射和连接同态，得到长正合序列：

$$\cdots \to \check{H}^p(\mathcal{U}, \mathcal{F}) \to \check{H}^p(\mathcal{U}, \mathcal{G}) \to \check{H}^p(\mathcal{U}, \mathcal{H}) \xrightarrow{\delta^p} \check{H}^{p+1}(\mathcal{U}, \mathcal{F}) \to \cdots$$

**Step 4: 验证正合性**

在每一度验证正合性：
- $\text{Im} \to \text{Ker}$：由复形映射的相容性
- $\text{Ker} \to \text{Im}$：由蛇引理的构造

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 短正合列 | `docs/homological-algebra/exact-sequences.md` |
| Čech复形 | `docs/cohomology/sheaf-cohomology.md` |
| 蛇引理 | `docs/homological-algebra/snake-lemma.md` |
| 长正合列 | `concept/homology_cohomology.md` 同调代数 |

**推荐学习路径**：
1. 复习短正合列的定义与基本性质
2. 理解蛇引理的构造与证明
3. 掌握Čech复形的函子性
4. 学习连接同态的几何意义

---

## 6. 应用与重要性

### 实际应用

1. **维数计算**
   - 利用长正合列递推计算上同调维数
   - 从已知层推断未知层的上同调

2. **消失定理**
   - 通过短正合列导出上同调消失结果
   - 证明Kodaira消失定理的基础

3. **具体计算**
   - 研究理想层序列 $0 \to \mathcal{I}_Z \to \mathcal{O}_X \to \mathcal{O}_Z \to 0$
   - 计算子概形的上同调

### 重要性

- **函子性核心**：层上同调作为导出函子的标志性性质
- **计算工具**：将全局不变量与局部数据联系
- **理论框架**：Grothendieck导出范畴理论的基础

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Weibel《同调代数导论》1.3节 | ⭐⭐⭐⭐⭐ |
| **教材** | Rotman《同调代数导论》蛇引理章节 | ⭐⭐⭐⭐⭐ |
| **讲义** | Vakil《代数几何基础》1.6节 | ⭐⭐⭐⭐ |
| **论文** | Grothendieck Tôhoku论文 | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 01ED**：Čech复形（基础定义）
- **Tag 01EM**：Čech上同调的函子性
- **Tag 010H**：阿贝尔范畴中的蛇引理
- **Tag 0131**：导出函子的长正合列

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中已包含蛇引理的形式化：

```lean4
-- mathlib4中Snake Lemma的实现
import Mathlib.Algebra.Homology.ShortComplex

-- 短正合列诱导长正合列的框架
variable {C : Type*} [Category C] [Abelian C]

-- 层的短正合列
def ShortExactSequence (ℱ 𝒢 ℋ : Sheaf Ab X) :=
  ∃ (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ), 
    Mono f ∧ Epi g ∧ Exact f g

-- 长正合列定理的结构
theorem longExactSequence_Cech {ℱ 𝒢 ℋ : Sheaf Ab X}
    (h : ShortExactSequence ℱ 𝒢 ℋ) (𝒰 : ι → Opens X) :
    ∃ (δ : ∀ p, CechCohomology 𝒰 ℋ p ⟶ CechCohomology 𝒰 ℱ (p+1)),
    ExactSequence [
      CechCohomology 𝒰 ℱ 0 ⟶ CechCohomology 𝒰 𝒢 0,
      CechCohomology 𝒰 𝒢 0 ⟶ CechCohomology 𝒰 ℋ 0,
      δ 0,
      CechCohomology 𝒰 ℱ 1 ⟶ CechCohomology 𝒰 𝒢 1,
      ...
    ] := by
  -- 证明使用蛇引理
  sorry
```

### 形式化挑战

1. **连接同态的显式构造**：需要明确定义 $\delta$ 映射
2. **正合性的逐点验证**：每度的正合性证明
3. **自然性**：长正合列在层同态下的自然性

### 推荐形式化路径

```
Phase 1: 蛇引理的应用
  └── 验证Čech复形构成短正合列
  └── 应用已有Snake Lemma
  
Phase 2: 连接同态的具体构造
  └── 定义δ映射
  └── 验证良好定义性
  
Phase 3: 完整长正合列
  └── 组装所有成分
  └── 验证整体正合性
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
