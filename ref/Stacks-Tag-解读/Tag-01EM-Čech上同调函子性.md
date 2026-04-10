# Stacks Project Tag 01EM - Čech上同调的函子性

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/01EM)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01EM |
| **英文名称** | Functoriality of Čech Cohomology |
| **中文名称** | Čech上同调的函子性 |
| **数学分支** | 层上同调 / 范畴论 |
| **所属章节** | Cohomology of Sheaves |
| **难度等级** | 中等 |

**前置知识要求**：函子、自然变换、Čech复形、阿贝尔范畴

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Lemma 01EM.** Let $X$ be a topological space. Let $\mathcal{U} : U = \bigcup_{i \in I} U_i$ be an open covering. The construction

$$\mathcal{F} \longmapsto \check{H}^n(\mathcal{U}, \mathcal{F})$$

is a functor from the category of abelian sheaves on $X$ to the category of abelian groups. Moreover, the assignment $\mathcal{F} \mapsto \check{C}^\bullet(\mathcal{U}, \mathcal{F})$ is an exact functor from abelian sheaves to complexes of abelian groups.

### 中文翻译

**引理 01EM.** 设 $X$ 为拓扑空间，$\mathcal{U} : U = \bigcup_{i \in I} U_i$ 为一开覆盖。构造

$$\mathcal{F} \longmapsto \check{H}^n(\mathcal{U}, \mathcal{F})$$

是从 $X$ 上阿贝尔层范畴到阿贝尔群范畴的函子。此外，赋值 $\mathcal{F} \mapsto \check{C}^\bullet(\mathcal{U}, \mathcal{F})$ 是从阿贝尔层到阿贝尔群复形的正合函子。

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │  阿贝尔层范畴       │
                    │   AbSh(X)          │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │  层同态 φ  │  │ Čech复形   │  │ 层同态 ψ  │
       │  ℱ → 𝒢    │  │ Ĉ^•(𝒰,-)  │  │  𝒢 → ℋ    │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ 复形同态        │
                    │ Ĉ^•(𝒰,φ)      │
                    │ Ĉ^•(𝒰,𝒢)      │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │  上同调诱导映射  │
                    │ φ_*: Ĥ^n(𝒰,ℱ) │
                    │   → Ĥ^n(𝒰,𝒢)  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 恒等保持   │ │ 合成保持   │ │ 自然性     │
       │ id_* = id  │ │ (ψ∘φ)_*    │ │ 复合同态   │
       │            │ │ = ψ_*∘φ_*  │ │ 交换图     │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **函子 (Functor)**：保持结构（对象和态射）的映射
- **正合函子 (Exact Functor)**：保持短正合列的函子
- **Čech复形构造**：层到复形的映射
- **自然性**：函子性在态射合成下的相容性

---

## 4. 证明概要

### 核心命题

Čech复形构造 $\mathcal{F} \mapsto \check{C}^\bullet(\mathcal{U}, \mathcal{F})$ 是阿贝尔范畴之间的正合函子。

### 证明步骤

**Step 1: 层同态诱导Čech余链映射**

设 $\varphi: \mathcal{F} \to \mathcal{G}$ 为层同态。对每个 $p \geq 0$，定义：

$$\check{C}^p(\varphi) : \check{C}^p(\mathcal{U}, \mathcal{F}) \to \check{C}^p(\mathcal{U}, \mathcal{G})$$

$$(\check{C}^p(\varphi)(s))_{i_0 \ldots i_p} = \varphi(s_{i_0 \ldots i_p})$$

**Step 2: 验证与微分交换**

需要证明下图交换：

```
Ĉ^p(𝒰,ℱ) --d--> Ĉ^{p+1}(𝒰,ℱ)
   |                  |
   | Ĉ^p(φ)           | Ĉ^{p+1}(φ)
   ▼                  ▼
Ĉ^p(𝒰,𝒢) --d--> Ĉ^{p+1}(𝒰,𝒢)
```

计算：
$$d(\check{C}^p(\varphi)(s)) = d(\varphi(s)) = \varphi(d(s)) = \check{C}^{p+1}(\varphi)(d(s))$$

其中等式成立因为 $\varphi$ 是层同态，与限制映射交换。

**Step 3: 验证函子公理**

- **恒等性**：$\check{C}^\bullet(\text{id}_{\mathcal{F}}) = \text{id}_{\check{C}^\bullet(\mathcal{U}, \mathcal{F})}$
- **合成性**：$\check{C}^\bullet(\psi \circ \varphi) = \check{C}^\bullet(\psi) \circ \check{C}^\bullet(\varphi)$

**Step 4: 正合性证明**

若 $0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$ 短正合，则对每个交集，截面序列正合：

$$0 \to \mathcal{F}(U_{i_0} \cap \cdots \cap U_{i_p}) \to \mathcal{G}(U_{i_0} \cap \cdots \cap U_{i_p}) \to \mathcal{H}(U_{i_0} \cap \cdots \cap U_{i_p}) \to 0$$

积保持正合性，故复形序列正合。

**Step 5: 上同调的诱导映射**

复形映射诱导上同调映射：

$$\varphi_*: \check{H}^n(\mathcal{U}, \mathcal{F}) \to \check{H}^n(\mathcal{U}, \mathcal{G})$$

满足函子性。

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 函子 | `docs/category-theory/functors.md` |
| 正合函子 | `docs/homological-algebra/exact-functors.md` |
| 层范畴 | `concept/sheaf_theory.md` |
| 阿贝尔范畴 | `docs/category-theory/abelian-categories.md` |

**推荐学习路径**：
1. 学习范畴论基础（函子、自然变换）
2. 理解阿贝尔范畴的结构
3. 掌握层范畴的 Abel 范畴性质
4. 学习Čech复形的函子性构造

---

## 6. 应用与重要性

### 实际应用

1. **上同调的计算**
   - 利用层同态计算Čech上同调的映射
   - 研究限制映射、推进映射的性质

2. **谱序列**
   - 函子性是构造Leray谱序列的基础
   - 层上同调的推进与拉回运算

3. **导出范畴**
   - Čech复形给出层范畴到导出范畴的函子
   - D^b(X) 的构造与研究

### 重要性

- **结构保持**：函子性保证了Čech上同调是层范畴的"好"不变量
- **计算工具**：通过层同态比较不同层的上同调
- **理论统一**：与导出函子框架相容

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Mac Lane《Categories for the Working Mathematician》 | ⭐⭐⭐⭐⭐ |
| **教材** | Kashiwara-Shapira《Sheaves on Manifolds》 | ⭐⭐⭐⭐⭐ |
| **讲义** | Vakil《代数几何基础》函子性章节 | ⭐⭐⭐⭐ |
| **论文** | Grothendieck《Sur quelques points d'algèbre homologique》 | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 01ED**：Čech复形（基础定义）
- **Tag 01EK**：层上同调的长正合列
- **Tag 0105**：阿贝尔范畴
- **Tag 0132**：导出函子

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中函子性已在CategoryTheory框架下发展：

```lean4
-- 概念性代码框架
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory Topology Sheaf

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

-- Čech复形作为函子
def CechComplexFunctor (𝒰 : ι → Opens X) : 
    Sheaf Ab X ⥤ CochainComplex Ab ℤ where
  obj ℱ := CechComplex ℱ 𝒰
  map {ℱ 𝒢} φ := {
    f p := Pi.map (fun i => ℱ.1.map (homOfLE ...)) -- 层的截面映射
    comm' := by
      -- 证明与微分交换
      ext
      simp [CechComplex, differential]
      -- 使用层同态与限制映射的交换性
  }
  map_id := by
    -- 验证恒等映射保持
    intros
    ext
    simp
  map_comp := by
    -- 验证映射合成保持
    intros
    ext
    simp

-- 正合性证明
theorem CechComplexFunctor_exact (𝒰 : ι → Opens X) :
    Functor.Exact (CechComplexFunctor 𝒰) := by
  -- 证明Čech复形函子是正合的
  sorry
```

### 形式化挑战

1. **无穷积的函子性**：在无穷范畴中处理积的函子性
2. **复形范畴的构造**：CochainComplex范畴的完整形式化
3. **正合性验证**：验证层限制映射的正合性

### 推荐形式化路径

```
Phase 1: 函子结构
  └── 定义CechComplexFunctor
  └── 验证Functor公理
  
Phase 2: 正合性
  └── 证明限制映射保持正合
  └── 证明积保持正合
  
Phase 3: 上同调函子
  └── 定义Čech上同调函子
  └── 验证导出函子性质
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
