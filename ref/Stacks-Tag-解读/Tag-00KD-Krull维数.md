# Stacks Project Tag 00KD 解读：Krull维数

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00KD |
| **章节** | Commutative Algebra, Section 10.60: Dimension |
| **类型** | 定义 (Definition) |
| **重要性** | ⭐⭐⭐⭐⭐ (交换代数核心) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/00KD |

---

## 2. 定义原文与翻译

### 英文原文

**Definition 10.60.9.** The *Krull dimension* of the ring $R$ is the supremum of the lengths of chains of prime ideals

$$\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n$$

in $R$. The Krull dimension of $R$ will be denoted $\dim(R)$.

The *height* of a prime ideal $\mathfrak{p}$ of $R$ is the supremum of the lengths of chains of prime ideals

$$\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n = \mathfrak{p}$$

ending with $\mathfrak{p}$. The height of $\mathfrak{p}$ is denoted $\text{ht}(\mathfrak{p})$.

### 中文翻译

**定义 10.60.9.** 环 $R$ 的**Krull维数**是 $R$ 中素理想链长度的上确界：

$$\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n$$

记为 $\dim(R)$。

素理想 $\mathfrak{p}$ 的**高度**是以 $\mathfrak{p}$ 结尾的素理想链长度的上确界：

$$\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n = \mathfrak{p}$$

记为 $\text{ht}(\mathfrak{p})$。

---

## 3. 概念依赖图

```
Tag 00KD: Krull维数
│
├── 前置概念
│   ├── 环与理想
│   ├── 素理想
│   │   └── 素理想的定义与性质
│   ├── 素理想链
│   │   └── 严格包含链
│   └── 包含序与Spec拓扑
│
├── 核心概念
│   ├── Krull维数 dim(R)
│   │   └── 最长素理想链的长度
│   │   └── 可能是无限的
│   ├── 素理想高度 ht(p)
│   │   └── 从0到p的链长度
│   └── 余高度 coht(p)
│       └── 从p到极大理想的链长度
│
├── 基本关系
│   ├── dim(R) = sup{ht(p) | p ∈ Spec(R)}
│   ├── dim(R) = sup{coht(p) | p ∈ Spec(R)}
│   ├── ht(p) + dim(R/p) ≤ dim(R)
│   └── 等号成立条件
│
├── 计算方法
│   ├── 诺特环的维数有限性
│   ├── 高度定理 (Tag 00KW)
│   ├── 维数公式
│   └── 局部化与维数
│
└── 相关Tags
    ├── Tag 00KE: 维数的基本性质
    ├── Tag 00KF: 局部化的维数
    ├── Tag 00KW: Krull高度定理
    └── Tag 02JP: 概形的维数
```

---

## 4. 详细内容与证明概要

### 4.1 直观理解

**Krull维数**度量了环的"几何维数"或"深度"：

| 环 | 几何对象 | dim(R) |
|----|---------|--------|
| 域 $k$ | 点 | 0 |
| $k[x]$ | 仿射直线 | 1 |
| $k[x,y]$ | 仿射平面 | 2 |
| $k[x_1,...,x_n]$ | n维仿射空间 | n |
| $\mathbb{Z}$ | Spec(Z) = { (p), (0) } | 1 |

**素理想高度**：度量素理想"距离"零理想的远近，对应于子簇的余维数。

### 4.2 基本性质

**性质1**: $\dim(R) = \sup_{\mathfrak{p}} \text{ht}(\mathfrak{p}) = \sup_{\mathfrak{p}} \dim(R/\mathfrak{p})$

**性质2**: $\text{ht}(\mathfrak{p}) + \dim(R/\mathfrak{p}) \leq \dim(R)$

**性质3**: 局部化保持高度：$\text{ht}_R(\mathfrak{p}) = \text{ht}_{R_{\mathfrak{p}}}(\mathfrak{p}R_{\mathfrak{p}})$

**性质4**: 若 $R \subset S$ 是整扩张，则 $\dim(R) = \dim(S)$（整扩张的维数不变性）

### 4.3 Krull高度定理 (Tag 00KW)

**定理**: 设 $R$ 是诺特环，$I = (f_1, \ldots, f_r)$ 是由 $r$ 个元素生成的理想。则包含 $I$ 的极小素理想的高度不超过 $r$：

$$\text{ht}(\mathfrak{p}) \leq r \quad \text{对 } I \subseteq \mathfrak{p} \text{ 极小}$$

**推论**: 诺特局部环的维数有限。

### 4.4 诺特环的维数理论

**定理 (维数公式)**: 设 $(R, \mathfrak{m})$ 是诺特局部环，则：

$$\dim(R) = \deg P_R$$

其中 $P_R$ 是Hilbert-Samuel多项式。

**定理 (正则局部环)**: $(R, \mathfrak{m})$ 是 $d$ 维正则局部环当且仅当 $\mathfrak{m}$ 可由 $d$ 个元素生成。

### 4.5 维数计算示例

**例1**: $k[x_1, \ldots, x_n]$ 的维数是 $n$。

*证明*: 链 $(0) \subset (x_1) \subset (x_1, x_2) \subset \cdots \subset (x_1, \ldots, x_n)$ 长度为 $n$，由高度定理知这是最大的。

**例2**: $k[x,y]/(xy)$ 的维数是 1。

*解释*: 对应于x轴与y轴的并，每个分支维数为1。

**例3**: 无限维诺特环（存在！）。

*构造*: Nagata的反例，通过无限次 blowing-up 构造。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 交换环 | 环的基本理论 | `concept/交换代数/交换环.md` |
| 素理想 | 素理想的定义与性质 | `concept/交换代数/素理想.md` |
| 维数理论 | Krull维数 | `concept/交换代数/Krull维数.md` |
| 高度定理 | Krull高度定理 | `concept/交换代数/高度定理.md` |
| 概形的维数 | 代数几何中的维数 | `concept/代数几何/概形的维数.md` |

### 学习路径

```
FormalMath: 交换代数核心
├── 前置
│   ├── 环与理想
│   ├── 素理想与极大理想
│   └── 局部化
├── 当前 ← Tag 00KD
│   ├── Krull维数
│   ├── 素理想高度
│   └── 维数公式
└── 后续
    ├── 高度定理 (Tag 00KW)
    ├── Noether正规化 (Tag 00GV)
    ├── 正则局部环
    └── 概形的维数理论
```

---

## 6. 应用与重要性

### 6.1 代数几何中的应用

| 应用 | 说明 |
|------|------|
| 概形维数 | $\dim(X) = \dim(\mathcal{O}_{X,x})$ 在闭点处 |
| 余维数 | 子概形的余维数 = 定义理想的高度 |
| 交理论 | 相交的维数预期 |
| 光滑性判别 | 正则局部环 = 光滑点 |

### 6.2 与其他不变量的关系

| 不变量 | 关系 |
|--------|------|
| 超越次数 | 整环：$\dim(R) = \text{tr.deg}_k(\text{Frac}(R))$ |
| 深度 | $\text{depth}(R) \leq \dim(R)$（Cohen-Macaulay环取等） |
| 嵌入维数 | $\text{embdim}(R) \geq \dim(R)$ |
| 重数 | Hilbert-Samuel重数 |

### 6.3 重要定理

**定理 (Noether正规化)**: 有限生成 $k$-代数 $R$ 存在多项式子环 $k[x_1, \ldots, x_d] \subset R$ 使得 $R$ 在其上整，其中 $d = \dim(R)$。

**定理 (Catenary环)**: 诺特局部环 $R$ 是catenary的（所有极大素理想链等长）当满足适当条件。

**定理 (正则局部环的维数)**: $R$ 正则局部 ⟺ $\dim(R) = \dim_k(\mathfrak{m}/\mathfrak{m}^2)$。

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Atiyah-Macdonald | Chapter 11 | Dimension theory |
| Matsumura | Chapter 5 | Dimension theory |
| Eisenbud | Chapter 10 | Appendix: Krull dimension |
| Liu Qing | 2.5 | Dimension of schemes |
| Stacks Project | Tag 00KD | Krull dimension |

### 7.2 nLab条目

- [Krull dimension](https://ncatlab.org/nlab/show/Krull+dimension)
- [dimension of a scheme](https://ncatlab.org/nlab/show/dimension+of+a+scheme)
- [height of a prime ideal](https://ncatlab.org/nlab/show/height+of+a+prime+ideal)

### 7.3 Wikipedia条目

- [Krull dimension](https://en.wikipedia.org/wiki/Krull_dimension)
- [Dimension theory (algebra)](https://en.wikipedia.org/wiki/Dimension_theory_(algebra))

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 00KE | 维数的基本性质 | 基本 |
| 00KF | 局部化的维数 | 计算工具 |
| 00KW | Krull高度定理 | 核心定理 |
| 00GV | Noether正规化 | 计算应用 |
| 02JP | 概形的维数 | 几何应用 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4中Krull维数理论已较为完整：

```lean
import Mathlib.RingTheory.KrullDimension
import Mathlib.RingTheory.Ideal.Height

-- Krull维数
def krullDimension (R : Type*) [Ring R] : ℕ∞ := ...

-- 素理想高度
def Ideal.height {R : Type*} [Ring R] (I : Ideal R) : ℕ∞ := ...

-- 基本性质
#check krullDimension_eq_iSup_height
#check krullDimension_le_of_integral
```

### 8.2 形式化状态

| 组件 | 状态 | Mathlib4位置 |
|------|------|--------------|
| Krull维数定义 | ✅ 完成 | `RingTheory.KrullDimension.Basic` |
| 素理想高度 | ✅ 完成 | `RingTheory.Ideal.Height` |
| 高度定理 | 🟡 部分 | 有限生成情形 |
| 维数公式 | 🟡 部分 | 诺特局部环 |
| 正则局部环维数 | 🟡 部分 | 与嵌入维数关系 |
| Noether正规化 | 🔴 待完成 | Tag 00GV |

### 8.3 形式化代码示例

```lean
import Mathlib.RingTheory.KrullDimension
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Basic

namespace RingTheory

variable {R : Type*} [CommRing R]

-- Krull维数定义（Tag 00KD）
#check krullDimension R

-- 素理想高度
#check Ideal.height

-- 高度 + 余高度 ≤ 维数
theorem height_add_coheight_le_krullDimension {p : Ideal R} [p.IsPrime] :
    p.height + krullDimension (R ⧸ p) ≤ krullDimension R := by
  sorry

-- 局部化保持高度
theorem height_localization {p : Ideal R} [p.IsPrime] :
    (Ideal.height p : ℕ∞) = Ideal.height (p.localize (R ⧸ p)ˣ) := by
  sorry

-- 整扩张维数不变
theorem krullDimension_eq_of_integral {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    krullDimension R = krullDimension S := by
  sorry

-- 多项式环维数增加1
theorem krullDimension_polynomial [Nontrivial R] :
    krullDimension (R[X]) = krullDimension R + 1 := by
  sorry

end RingTheory
```

### 8.4 形式化挑战

1. **无限维数处理**：使用 `ℕ∞` (WithTop ℕ) 处理无限维数
2. **高度定理证明**：需要Noether归纳和准素分解
3. **维数公式**：需要Hilbert-Samuel理论
4. **几何解释**：与概形维数理论的联系

### 8.5 进一步发展

```lean
-- 概形的维数
namespace AlgebraicGeometry

def Scheme.dimension (X : Scheme) : ℕ∞ :=
  ⨆ (x : X), krullDimension (X.presheaf.stalk x)

-- 维数在闭点处取得
theorem dimension_eq_sup_closed_points [X.CompactSpace] :
    X.dimension = ⨆ (x : X) (_ : IsClosed ({x} : Set X)),
      krullDimension (X.presheaf.stalk x) := by
  sorry

-- 余维数定义
def codimension {X : Scheme} (Z : ClosedImmersion X) : ℕ∞ :=
  Ideal.height Z.ideal

end AlgebraicGeometry
```

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 00KD}
}

@book{atiyah2018introduction,
  title     = {Introduction to Commutative Algebra},
  author    = {Atiyah, Michael Francis and Macdonald, Ian Grant},
  year      = {2018},
  publisher = {CRC Press}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
