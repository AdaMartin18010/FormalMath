---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 01LC 解读：拟凝聚层定义

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01LC |
| **章节** | Schemes, Section 26.12: Quasi-coherent modules |
| **类型** | 定义 (Definition) |
| **重要性** | ⭐⭐⭐⭐⭐ (核心概念) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01LC |

---

## 2. 定义原文与翻译

### 英文原文

**Definition 26.12.1.** Let $(X, \mathcal{O}_X)$ be a ringed space. An $\mathcal{O}_X$-module $\mathcal{F}$ is called *quasi-coherent* if for every point $x \in X$ there exists an open neighbourhood $x \in U \subset X$ such that $\mathcal{F}|_U$ is isomorphic to the cokernel of a map

$$\bigoplus_{j \in J} \mathcal{O}_U \longrightarrow \bigoplus_{i \in I} \mathcal{O}_U$$

between free $\mathcal{O}_U$-modules.

An $\mathcal{O}_X$-module is called *coherent* if it is of finite type and for every open $U \subset X$ and every finite collection $s_i \in \mathcal{F}(U)$, $i = 1, \ldots, n$ the kernel of the associated map $\bigoplus_{i=1}^n \mathcal{O}_U \to \mathcal{F}|_U$ is of finite type.

### 中文翻译

**定义 26.12.1.** 设 $(X, \mathcal{O}_X)$ 是环化空间。一个 $\mathcal{O}_X$-模 $\mathcal{F}$ 称为**拟凝聚的** (quasi-coherent)，如果对每个点 $x \in X$，存在开邻域 $x \in U \subset X$ 使得 $\mathcal{F}|_U$ 同构于自由 $\mathcal{O}_U$-模之间映射的余核：

$$\bigoplus_{j \in J} \mathcal{O}_U \longrightarrow \bigoplus_{i \in I} \mathcal{O}_U$$

一个 $\mathcal{O}_X$-模称为**凝聚的** (coherent)，如果它是有限型的，且对任意开集 $U \subset X$ 和任意有限个截面 $s_i \in \mathcal{F}(U)$，$i = 1, \ldots, n$，相伴映射 $\bigoplus_{i=1}^n \mathcal{O}_U \to \mathcal{F}|_U$ 的核也是有限型的。

---

## 3. 概念依赖图

```
Tag 01LC: 拟凝聚层定义
│
├── 前置概念
│   ├── 环化空间 (Ringed Space)
│   │   ├── 拓扑空间 X
│   │   └── 结构层 O_X (取值在环中的层)
│   ├── O_X-模 (Module over O_X)
│   │   ├── 层论基础
│   │   └── 模论基础
│   ├── 自由模与直和
│   └── 余核 (Cokernel)
│
├── 核心概念
│   ├── 拟凝聚层 (Quasi-coherent sheaf)
│   │   └── 局部是自由模映射的余核
│   │   └── 直观："局部可由方程定义"
│   └── 凝聚层 (Coherent sheaf)
│       └── 拟凝聚 + 有限型 + 有限型核条件
│       └── 直观："局部有限表示"
│
├── 在概形上的特殊情况
│   ├── 仿射概形上的对应
│   │   └── QCoh(Spec R) ≅ Mod_R
│   ├── 仿射开覆盖的粘合
│   └── 与结构层的关系
│
└── 相关Tags
    ├── Tag 01LD: 拟凝聚层的基本性质
    ├── Tag 01LE: 仿射情形下的刻画
    ├── Tag 01LH: 概形上拟凝聚层的等价定义
    └── Tag 01M1: 凝聚层的性质
```

---

## 4. 详细内容与证明概要

### 4.1 拟凝聚层的直观理解

**核心思想**：拟凝聚层是"代数"的层，局部由方程（关系）定义。

给定一个映射 $\bigoplus_J \mathcal{O}_U \to \bigoplus_I \mathcal{O}_U$，可以用矩阵 $(a_{ij})$ 表示，其中 $a_{ij} \in \mathcal{O}_U(U)$。余核即为：

$$\mathcal{F}|_U \cong \text{coker}\left(\mathcal{O}_U^J \xrightarrow{(a_{ij})} \mathcal{O}_U^I\right)$$

这意味着 $\mathcal{F}$ 局部由生成元 $e_i$ 模去关系 $\sum_j a_{ij} e_j = 0$ 得到。

### 4.2 仿射情形的基本定理

**定理** (Tag 01LE): 设 $X = \text{Spec}(R)$ 是仿射概形，则存在范畴等价：

$$\text{QCoh}(X) \cong \text{Mod}_R$$

具体对应：

- 拟凝聚层 $\mathcal{F} \mapsto$ 全局截面模 $\Gamma(X, \mathcal{F})$
- $R$-模 $M \mapsto$ 相伴层 $\widetilde{M}$

其中 $\widetilde{M}$ 定义为 $\widetilde{M}(D(f)) = M_f$（局部化）。

### 4.3 凝聚层的额外条件

凝聚层要求：

1. **有限型**：局部有限生成（有限个截面生成）
2. **有限型核**：关系的集合也是有限生成的

**在诺特概形上**：凝聚层 = 有限型拟凝聚层（简化！）

### 4.4 重要性质证明概要

**性质1**: 拟凝聚层的核、余核、扩张仍是拟凝聚的（在概形上）。

**证明思路**：在仿射开集上验证，利用范畴等价转化为模论问题。

**性质2**: 仿射态射的推进保持拟凝聚性。

**性质3**: 平坦拉回保持拟凝聚性。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 层论基础 | 预层、层、茎 | `concept/层论/层的基本概念.md` |
| 环化空间 | 结构层、局部环化空间 | `concept/代数几何/环化空间.md` |
| 模论 | 模、自由模、余核 | `concept/环与代数/模论基础.md` |
| 概形 | 仿射概形、概形 | `concept/代数几何/概形.md` |
| 凝聚层 | 凝聚层的定义与性质 | `concept/代数几何/凝聚层.md` |

### 学习路径

```
FormalMath: 层与上同调
├── 前置
│   ├── 层论基础
│   ├── 环化空间
│   └── 概形基础
├── 当前 ← Tag 01LC
│   ├── 拟凝聚层
│   └── 凝聚层
└── 后续
    ├── 层上同调 (Tag 01E8)
    ├── 对偶性理论
    └── 导出范畴
```

---

## 6. 应用与重要性

### 6.1 为什么在代数几何中至关重要

拟凝聚层是代数几何的"正确"层类：

| 特性 | 说明 |
|------|------|
| 代数性 | 对应于模论，保持代数几何的代数本质 |
| 完备性 | 形成Abel范畴，可应用同调代数 |
| 可计算性 | 在仿射开集上可约化为模论计算 |
| 几何性 | 包含所有"几何"层（切层、法层等） |

### 6.2 典型例子

| 层 | 类型 | 说明 |
|----|------|------|
| $\mathcal{O}_X$ | 凝聚 | 结构层 |
| $\mathcal{O}_X(n)$ | 凝聚 | 射影空间上的扭曲层 |
| $\Omega_{X/k}^1$ | 拟凝聚 | Kähler微分层 |
| $\mathcal{T}_X$ | 拟凝聚 | 切层 |
| $j_! \mathcal{O}_U$ | 通常不拟凝聚 | 开浸入的推进 |

### 6.3 应用实例

1. **向量丛对应**：局部自由凝聚层 ↔ 向量丛（Serre-Swan定理）
2. **Picard群**：可逆层（秩1局部自由层）构成Picard群
3. **Riemann-Roch定理**：研究凝聚层的Euler示性数
4. **模空间理论**：凝聚层的模空间构造

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Hartshorne | II.5 | Quasi-coherent and coherent sheaves |
| Liu Qing | 5.1 | Quasi-coherent sheaves on schemes |
| Görtz-Wedhorn | 7 | Quasi-coherent modules |
| Vakil FOAG | 13 | Quasicoherent and coherent sheaves |
| EGA I | §1.4 | Faisceaux quasi-cohérents |

### 7.2 nLab条目

- [quasi-coherent sheaf](https://ncatlab.org/nlab/show/quasi-coherent+sheaf)
- [coherent sheaf](https://ncatlab.org/nlab/show/coherent+sheaf)
- [module over a ringed space](https://ncatlab.org/nlab/show/module+over+a+ringed+space)

### 7.3 Wikipedia条目

- [Quasi-coherent sheaf](https://en.wikipedia.org/wiki/Quasi-coherent_sheaf)
- [Coherent sheaf](https://en.wikipedia.org/wiki/Coherent_sheaf)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 01LD | 拟凝聚层的基本性质 | 后续 |
| 01LE | 仿射情形下的刻画 | 核心定理 |
| 01LH | 概形上的等价刻画 | 深化 |
| 01M1 | 凝聚层的性质 | 强化条件 |
| 01ME | 拟凝聚层构成的范畴 | 范畴论视角 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4中拟凝聚层理论仍在发展中：

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme

-- 拟凝聚层的定义框架
#check AlgebraicGeometry.QuasiCoherentSheaf

-- 仿射概形上的对应
#check AlgebraicGeometry.QuasiCoherentSheaf.equivFunctor
```

### 8.2 形式化路线图

| 阶段 | 目标 | 状态 |
|------|------|------|
| 1 | 拟凝聚层定义 | 进行中 |
| 2 | 仿射对应 | 部分完成 |
| 3 | 范畴等价 QCoh(Spec R) ≅ Mod_R | 待完成 |
| 4 | 凝聚层定义 | 待完成 |
| 5 | 诺特概形上凝聚层 = 有限型QCoh | 待完成 |
| 6 | 层上同调理论 | 待完成 |

### 8.3 形式化代码示例

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace AlgebraicGeometry

-- 拟凝聚层的定义（基于局部表示）
structure IsQuasiCoherent {X : Scheme} (F : SheafOfModules X.ringCatSheaf) :
    Prop where
  -- 每点存在开邻域使得限制是自由模映射的余核
  localPresentation : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃
    (I J : Type) (f : (⨁ fun _ : J ↦ O| U) ⟶ ⨁ fun _ : I ↦ O| U),
    F.restrict U ≅ cokernel f

-- 在仿射概形上的判别准则
theorem isQuasiCoherent_iff_affine {R : CommRingCat} {F : SheafOfModules (Spec R).ringCatSheaf} :
    IsQuasiCoherent F ↔ ∃ M : ModuleCat R, F ≅ M.sheafify := by
  sorry  -- 需要证明的核心定理

-- 全局截面函子
def globalSections {X : Scheme} (F : SheafOfModules X.ringCatSheaf) :
    ModuleCat (X.presheaf.obj (op ⊤)) :=
  F.module ⊤

-- 相伴层构造
def sheafify {R : CommRingCat} (M : ModuleCat R) :
    SheafOfModules (Spec R).ringCatSheaf :=
  sorry  -- 待实现

end AlgebraicGeometry
```

### 8.4 挑战与机遇

**挑战**：

- 层论在类型论中的表述复杂
- 范畴等价需要仔细的函子构造
- 上同调计算需要导出范畴基础

**机遇**：

- Mathlib的Abel范畴框架日趋成熟
- 仿射对应可借助局部化理论
- 可与Lean的代数计算能力结合

### 8.5 建议实现路径

1. **短期**：完成仿射概形上的相伴层构造
2. **中期**：建立QCoh(Spec R) ≅ Mod_R的范畴等价
3. **长期**：推广到一般概形，发展上同调理论

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 01LC}
}

@book{hartshorne1977algebraic,
  title     = {Algebraic Geometry},
  author    = {Hartshorne, Robin},
  year      = {1977},
  publisher = {Springer}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
