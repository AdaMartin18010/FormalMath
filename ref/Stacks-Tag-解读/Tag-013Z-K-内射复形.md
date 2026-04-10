# Stacks Project Tag 013Z - K-内射复形（K-injective complexes）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013Z |
| **英文名称** | K-injective complexes |
| **中文名称** | K-内射复形 |
| **所属章节** | Chapter 13: Derived Categories (导出范畴) |
| **数学领域** | 同调代数、导出范畴理论 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息

- **URL**: https://stacks.math.columbia.edu/tag/013Z
- **章节**: 13.14 K-内射复形
- **前置Tags**: 013M (导出范畴), 013P (拟同构), 013U (截断函子)

---

## 2. 定理/定义原文

### 2.1 定义（Definition 13.14.1）

设 $\mathcal{A}$ 是一个Abel范畴，$K^\bullet$ 是 $\mathcal{A}$ 中的一个复形。称 $K^\bullet$ 是**K-内射的（K-injective）**，如果对于任意无环复形（acyclic complex）$M^\bullet$，有：

$$\text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet) = 0$$

即，从任意无环复形到 $K^\bullet$ 的链同态类只有零映射。

等价地，$K^\bullet$ 是K-内射的当且仅当对于任意复形态射 $f: M^\bullet \to N^\bullet$ 诱导拟同构时，诱导映射：

$$\text{Hom}_{K(\mathcal{A})}(N^\bullet, K^\bullet) \longrightarrow \text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet)$$

是同构。

### 2.2 核心性质

**引理 13.14.2**: 设 $K^\bullet$ 是K-内射复形，$M^\bullet$ 是任意复形。则自然映射

$$\text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet) \longrightarrow \text{Hom}_{D(\mathcal{A})}(M^\bullet, K^\bullet)$$

是双射。

**命题 13.14.3**: 设 $0 \to K_1^\bullet \to K_2^\bullet \to K_3^\bullet \to 0$ 是复形的短正合列，其中 $K_3^\bullet$ 是K-内射的。则 $K_1^\bullet$ 是K-内射的当且仅当 $K_2^\bullet$ 是K-内射的。

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │   Abel范畴 𝒜    │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │  复形范畴   │ │  链同伦范畴 │ │ 导出范畴 D(𝒜)│
       │  C(𝒜)     │ │  K(𝒜)     │ │            │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   无环复形     │
                    │  (Acyclic)   │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  K-内射复形   │◄────────────┐
                    │ K^• 满足:    │             │
                    │ Hom_K(M^•,K^•)│=0          │
                    │ ∀无环M^•     │             │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ 有界复形  │  │ 上有界   │  │ 下有界   │   │
       │ K^b(𝒜)  │  │ K^-(𝒜)  │  │ K^+(𝒜)  │   │
       └────┬─────┘  └────┬─────┘  └────┬─────┘   │
            │             │             │         │
            └─────────────┴─────────────┘         │
                          │                       │
                          ▼                       │
                  ┌───────────────┐               │
                  │ K-内射分解存在 │───────────────┘
                  │ 性定理         │
                  └───────────────┘
                          │
                          ▼
                  ┌───────────────┐
                  │ 右导出函子    │
                  │ RHom, RΓ, ... │
                  └───────────────┘
```

### 3.1 依赖链

```
Abel范畴 → 复形范畴 C(𝒜) → 链同伦范畴 K(𝒜) → 导出范畴 D(𝒜)
                     ↓
              无环复形定义
                     ↓
              K-内射复形定义 ←── 内射对象概念
                     ↓
              K-内射分解存在性 ←── 有足够内射元
                     ↓
              导出函子构造
```

---

## 4. 证明概要

### 4.1 K-内射复形的基本性质证明

**引理 13.14.2 的证明概要**:

1. **目标**: 证明 $\text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet) \cong \text{Hom}_{D(\mathcal{A})}(M^\bullet, K^\bullet)$

2. **回顾**: 导出范畴 $D(\mathcal{A})$ 是 $K(\mathcal{A})$ 关于拟同构的局部化

3. **关键观察**: 若 $f: M^\bullet \to N^\bullet$ 是拟同构，则Cone($f$) 是无环复形

4. **证明步骤**:
   - 对于 $\phi \in \text{Hom}_{D(\mathcal{A})}(M^\bullet, K^\bullet)$，存在 $s^{-1}f$ 表示，其中 $s: M^\bullet \to L^\bullet$ 是拟同构
   - Cone($s$) 无环，故 $\text{Hom}_{K(\mathcal{A})}(\text{Cone}(s)[-1], K^\bullet) = 0$
   - 由长正合列，$\text{Hom}_{K(\mathcal{A})}(L^\bullet, K^\bullet) \to \text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet)$ 是同构
   - 因此可以唯一提升 $f \circ s^{-1}$ 到 $K(\mathcal{A})$ 中的映射

### 4.2 K-内射分解存在性

**定理 13.14.5（Spaltenstein定理）**:

设 $\mathcal{A}$ 是有足够内射元的Grothendieck Abel范畴，则每个复形都有K-内射分解。

**证明策略**:

1. **构造**: 对复形 $M^\bullet$ 构造内射分解 $M^\bullet \to I^{\bullet,\bullet}$

2. **全复形**: 取双复形的全复形 $\text{Tot}(I^{\bullet,\bullet})$

3. **Cartan-Eilenberg分解**: 使用柱构造确保得到K-内射复形

4. **拟同构验证**: 证明 $M^\bullet \to \text{Tot}(I^{\bullet,\bullet})$ 是拟同构

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| Abel范畴 | 阿贝尔范畴定义 | `concept/范畴论/阿贝尔范畴.md` |
| 复形范畴 | 链复形定义 | `concept/同调代数/链复形.md` |
| K-内射复形 | 内射对象 | `concept/同调代数/内射对象.md` |
| 导出范畴 | 导出范畴 | `concept/同调代数/导出范畴.md` |
| 拟同构 | 拟同构 | `concept/同调代数/拟同构.md` |
| 无环复形 | 正合序列 | `concept/同调代数/正合序列.md` |

### 5.2 Lean4对应

```lean4
-- K-内射复形在Lean4中的可能形式化
import Mathlib.Algebra.Homology.HomotopyCategory

-- K-内射复形定义
structure KInjective {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) : Prop where
  /-- 对任意无环复形M，Hom_K(M, K) = 0 -/
  vanish_acyclic : ∀ (M : CochainComplex C ℤ),
    IsAcyclic M → ∀ (f : M ⟶ K), Homotopy f 0
```

### 5.3 在FormalMath知识体系中的位置

```
代数几何/导出范畴
    ├── 同调代数基础
    │       ├── 链复形 ──► K-内射复形 ◄── 本Tag
    │       ├── 导出函子
    │       └── 正合序列
    └── 层上同调
            ├── 导出像函子 Rf_*
            └── 局部上同调
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **导出函子的计算**
   - K-内射复形提供计算右导出函子的标准方法
   - 避免使用内射分解的复杂性

2. **层上同调理论**
   - 在代数几何中，K-内射复形是定义导出像函子 $Rf_*$ 的基础
   - 上同调与基变换定理依赖此构造

3. **六函子形式体系**
   - $f^*$, $f_*$, $f^!$, $f_!$ 及其导出版本
   - Grothendieck对偶性定理

### 6.2 历史重要性

- **N. Spaltenstein (1988)**: 引入K-内射复形概念
- **B. Keller (1994)**: 导出范畴的代数结构理论
- **重要性**: 解决了经典同调代数中导出范畴计算困难的问题

### 6.3 现代发展

- **dg-范畴框架**: K-内射复形在微分分次范畴中的应用
- **导出代数几何**: 高阶导出结构的基础
- **稳定同伦论**: 谱序列收敛性问题

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 013M | 导出范畴 | 基础概念 |
| 013P | 拟同构 | 定义依赖 |
| 0143 | Brown可表性 | 应用定理 |
| 01YC | 形式函数定理 | 应用实例 |
| 08H4 | 导出Hom (RHom) | 构造应用 |
| 08HP | 导出张量积 | 构造应用 |

### 7.2 外部资源

**教科书**:

- Gelfand-Manin: "Methods of Homological Algebra" (第二章)
- Weibel: "An Introduction to Homological Algebra" (第十章)
- Kashiwara-Shapira: "Categories and Sheaves"

**研究论文**:

- Spaltenstein, N. "Resolutions of unbounded complexes", Compositio Math. 65 (1988)
- Alonso-Tarrio et al. "Localization in categories of complexes"

**在线资源**:

- nLab: https://ncatlab.org/nlab/show/K-injective+complex
- Kerodon: https://kerodon.net/

### 7.3 相关数学软件

- **SageMath**: 复形计算
- **Macaulay2**: 同调代数计算
- **Lean4/Mathlib4**: 正在发展的形式化

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

截至2024年，Mathlib4中关于导出范畴和K-内射复形的形式化仍在发展中：

```
Mathlib4状态:
✅ 基础同调代数 (链复形、上同调)
✅ 阿贝尔范畴理论
🔄 导出范畴 (进行中)
⬜ K-内射复形 (待实现)
⬜ 导出函子 (部分实现)
```

### 8.2 形式化路线图

**阶段1: 基础准备** (预计6个月)

```lean4
-- 定义K-内射复形的核心结构
class KInjectiveComplex (C : Type u) [Category.{v} C] [Abelian C]
    (K : HomologicalComplex C (ComplexShape.up ℤ)) where
  hom_vanish : ∀ (M : HomologicalComplex C (ComplexShape.up ℤ)),
    IsAcyclic M → ∀ f : M ⟶ K, Nonempty (Homotopy f 0)
```

**阶段2: 分解定理** (预计12个月)

- Grothendieck范畴的K-内射分解存在性
- Spaltenstein定理的完整形式化

**阶段3: 应用** (预计18个月)

- 导出函子的形式化
- 层上同调的形式化基础

### 8.3 技术挑战

1. **宇宙层次管理**: 导出范畴涉及复杂的范畴论构造
2. **同伦理论**: 链同伦的形式化需要精细处理
3. **大范畴**: Grothendieck范畴可能不是小范畴

### 8.4 相关形式化项目

- **mathlib4#homology**: 同调代数库
- **condensed mathematics**: Clausen-Scholze的凝聚数学形式化
- **sphere eversion**: 同伦类型论应用

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| K-内射定义 | $\text{Hom}_{K(\mathcal{A})}(M^\bullet, K^\bullet) = 0$ 对无环 $M^\bullet$ |
| 导出Hom | $\text{RHom}(M^\bullet, K^\bullet) = \text{Hom}^\bullet(M^\bullet, I^\bullet)$ |
| 拟同构条件 | $H^n(f): H^n(M^\bullet) \cong H^n(N^\bullet)$ |
| 无环复形 | $H^n(M^\bullet) = 0$ 对所有 $n$ |

---

**文档版本**: 1.0
**创建日期**: 2026-04-10
**最后更新**: 2026-04-10
**作者**: FormalMath Knowledge System
