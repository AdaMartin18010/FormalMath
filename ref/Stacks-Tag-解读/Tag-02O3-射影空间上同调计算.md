# Stacks Project Tag 02O3 解读：射影空间上同调计算

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 02O3 |
| **章节** | Schemes, Section 30.8: Cohomology of projective space |
| **类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐⭐ (经典计算) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/02O3 |

---

## 2. 定理原文与翻译

### 英文原文

**Lemma 30.8.1.** Let $A$ be a ring. Let $n \geq 0$. Then

$$H^q(\mathbf{P}^n_A, \mathcal{O}_{\mathbf{P}^n_A}(d)) = \begin{cases}
(A[T_0, \ldots, T_n])_d & \text{if } q = 0 \\
0 & \text{if } q \neq 0, n \\
\left(\frac{1}{T_0 \cdots T_n} A[\frac{1}{T_0}, \ldots, \frac{1}{T_n}]\right)_d & \text{if } q = n
\end{cases}$$

In particular we have $H^q(\mathbf{P}^n_A, \mathcal{O}_{\mathbf{P}^n_A}(d)) = 0$ if $q \not\in \{0, n\}$ or if $d \geq -n$ and $q = n$.

### 中文翻译

**引理 30.8.1.** 设 $A$ 是环，$n \geq 0$。则：

$$H^q(\mathbf{P}^n_A, \mathcal{O}_{\mathbf{P}^n_A}(d)) = \begin{cases}
(A[T_0, \ldots, T_n])_d & \text{若 } q = 0 \\
0 & \text{若 } q \neq 0, n \\
\left(\frac{1}{T_0 \cdots T_n} A[\frac{1}{T_0}, \ldots, \frac{1}{T_n}]\right)_d & \text{若 } q = n
\end{cases}$$

特别地，若 $q \not\in \{0, n\}$ 或 $d \geq -n$ 且 $q = n$，则 $H^q(\mathbf{P}^n_A, \mathcal{O}_{\mathbf{P}^n_A}(d)) = 0$。

---

## 3. 概念依赖图

```
Tag 02O3: 射影空间上同调计算
│
├── 前置概念
│   ├── 射影空间 P^n_A
│   │   ├── 齐次坐标环 A[T_0,...,T_n]
│   │   └── 标准仿射覆盖
│   ├── 扭曲层 O(d)
│   │   └── 分次模的相伴层
│   │   └── 整体截面与齐次元
│   ├── Čech上同调
│   │   └── 开覆盖上的计算
│   └── 仿射概形上同调 (Tag 01X8)
│       └── 消失定理
│
├── 核心计算
│   ├── H^0: 全局截面
│   │   └── Γ(P^n, O(d)) = A[T]_d
│   ├── H^q (0<q<n): 消失
│   │   └── Čech复形的正合性
│   └── H^n: 最高上同调
│       └── 由Cech边界计算
│       └── 负分次部分
│
├── 关键观察
│   ├── Cech复形 = Koszul复形
│   ├── 分次结构与计算兼容
│   └── 对偶性预示
│
└── 相关Tags
    ├── Tag 01X8: 仿射概形上同调
    ├── Tag 02N6: 射影空间的定义
    ├── Tag 02OA: 扭曲层的性质
    └── Tag 0B4C: 射影空间的对偶性
```

---

## 4. 详细证明

### 4.1 证明概览

这是代数几何中最经典、最重要的计算之一。证明使用**标准仿射开覆盖的Čech上同调**。

### 4.2 标准仿射开覆盖

取 $\mathbf{P}^n_A$ 的标准仿射覆盖：

$$\mathcal{U} = \{U_0, U_1, \ldots, U_n\}, \quad U_i = D_+(T_i) \cong \mathbb{A}^n_A$$

其中 $U_{i_0} \cap \cdots \cap U_{i_p} = D_+(T_{i_0} \cdots T_{i_p}) \cong \text{Spec}(A[T_0, \ldots, T_n]_{(T_{i_0} \cdots T_{i_p})})_0$。

### 4.3 Čech复形的结构

层 $\mathcal{O}(d)$ 在 $U_{i_0} \cap \cdots \cap U_{i_p}$ 上的截面为：

$$\mathcal{O}(d)(U_{i_0} \cap \cdots \cap U_{i_p}) = \left(A[T_0, \ldots, T_n]_{T_{i_0} \cdots T_{i_p}}\right)_d$$

Čech复形 $C^\bullet = \check{C}^\bullet(\mathcal{U}, \mathcal{O}(d))$ 为：

$$0 \to \prod_{i=0}^n A[T, T_i^{-1}]_d \to \prod_{0 \leq i < j \leq n} A[T, T_i^{-1}T_j^{-1}]_d \to \cdots$$

### 4.4 H^0 的计算

$H^0$ 是全局截面：

$$H^0(\mathbf{P}^n, \mathcal{O}(d)) = \bigcap_{i=0}^n A[T, T_i^{-1}]_d = A[T]_d$$

这是次数为 $d$ 的齐次多项式空间。

### 4.5 H^q (0 < q < n) 的消失

**关键观察**：Čech复形 $C^\bullet$ 同构于**Koszul复形**的某个变体。

考虑乘法映射：
$$\cdot T_i : A[T, T_0^{-1}, \ldots, T_{i-1}^{-1}, T_{i+1}^{-1}, \ldots]_d \to A[T, T_0^{-1}, \ldots, T_n^{-1}]_{d+1}$$

这些映射的交错和给出Čech微分。

**引理**：对于 $n+1$ 个变量的序列 $(T_0, \ldots, T_n)$，对应的Čech复形在 $0 < q < n$ 处正合。

**证明**：利用 $T_0, \ldots, T_n$ 在 $A[T]$ 中构成正则序列的事实，以及Koszul复形的正合性。

### 4.6 H^n 的计算

最高上同调 $H^n$ 是Čech复形的最高余核：

$$H^n(\mathbf{P}^n, \mathcal{O}(d)) = \text{coker}\left(\bigoplus_{i=0}^n A[T, T_0^{-1}, \ldots, \widehat{T_i^{-1}}, \ldots, T_n^{-1}]_d \to A[T, T_0^{-1}, \ldots, T_n^{-1}]_d\right)$$

分子包含所有形如 $T_0^{a_0} \cdots T_n^{a_n}$ 的单项式，其中至少有一个 $a_i \geq 0$。

因此余核由**所有指数均为负**的单项式组成：

$$H^n(\mathbf{P}^n, \mathcal{O}(d)) = \left\{\sum_{a_0 + \cdots + a_n = d \atop a_i < 0} c_a T_0^{a_0} \cdots T_n^{a_n}\right\}$$

这可以重写为：

$$\left(\frac{1}{T_0 \cdots T_n} A[\frac{1}{T_0}, \ldots, \frac{1}{T_n}]\right)_d$$

### 4.7 维度公式

当 $A = k$ 是域时：

$$\dim_k H^0(\mathbf{P}^n, \mathcal{O}(d)) = \binom{n+d}{n} \quad (d \geq 0)$$

$$\dim_k H^n(\mathbf{P}^n, \mathcal{O}(d)) = \binom{-d-1}{n} \quad (d \leq -n-1)$$

验证Serre对偶：$H^n(\mathbf{P}^n, \mathcal{O}(d)) \cong H^0(\mathbf{P}^n, \mathcal{O}(-d-n-1))^\vee$

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 射影空间 | Proj构造 | `concept/代数几何/射影概形.md` |
| 扭曲层 | O(d)的定义 | `concept/代数几何/扭曲层.md` |
| 分次环 | 齐次坐标环 | `concept/交换代数/分次环与模.md` |
| Čech上同调 | 计算工具 | `concept/层论/Čech上同调.md` |
| Koszul复形 | 正合性工具 | `concept/同调代数/Koszul复形.md` |

### 学习路径

```
FormalMath: 射影概形理论
├── 前置
│   ├── 分次代数
│   ├── Proj构造
│   ├── 扭曲层
│   └── 仿射开覆盖
├── 当前 ← Tag 02O3
│   ├── 射影空间上同调
│   └── 扭曲层的上同调
└── 后续
    ├── Riemann-Roch定理
    ├── Serre对偶
    └── 一般射影概形的上同调
```

---

## 6. 应用与重要性

### 6.1 历史意义

这是Serre的经典计算 (FAC, 1955)，奠定了：
- 层上同调作为计算工具的有效性
- 射影几何的现代处理方法
- 对偶性理论的雏形

### 6.2 直接应用

| 应用 | 说明 |
|------|------|
| Riemann-Roch | 曲线情形的基础计算 |
| 超曲面上同调 | 使用正合序列从射影空间导出 |
| 判别完全交 | 通过上同调判别完全交簇 |
| Hilbert多项式 | 欧拉示性数的计算 |

### 6.3 结构理论

**Serre消失定理**：对凝聚层 $\mathcal{F}$ 在射影概形 $X$ 上：
- $H^i(X, \mathcal{F}(d)) = 0$ 对 $i > 0$ 和 $d \gg 0$

**有限生成性**：$\bigoplus_d H^0(X, \mathcal{F}(d))$ 是有限生成分次模。

### 6.4 与对偶性的联系

计算结果预示Serre对偶：

$$H^n(\mathbf{P}^n, \mathcal{O}(d)) \cong H^0(\mathbf{P}^n, \mathcal{O}(-n-1-d))^*$$

其中 $\omega_{\mathbf{P}^n} = \mathcal{O}(-n-1)$ 是典则层。

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Hartshorne | III.5 | Cohomology of projective space |
| Liu Qing | 5.3 | Cohomology of projective schemes |
| Görtz-Wedhorn | 12.3 | Cohomology of the projective space |
| Vakil FOAG | 18.3 | Cohomology of projective space |
| EGA III | §2 | Cohomologie des faisceaux O(d) |

### 7.2 原始文献

```bibtex
@article{serre1955faisceaux,
  title     = {Faisceaux alg{\'e}briques coh{\'e}rents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  number    = {2},
  pages     = {197--278},
  year      = {1955}
}
```

### 7.3 nLab条目

- [projective space](https://ncatlab.org/nlab/show/projective+space)
- [twisted sheaf](https://ncatlab.org/nlab/show/twisted+sheaf)
- [cohomology of projective space](https://ncatlab.org/nlab/show/cohomology+of+projective+space)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 01X8 | 仿射概形上同调 | 基础工具 |
| 02N6 | 射影空间的定义 | 前置 |
| 02OA | 扭曲层O(d) | 对象定义 |
| 0B4C | 射影空间的对偶性 | 深化 |
| 0FD8 | 射影概形的上同调 | 推广 |

---

## 8. Lean4形式化展望

### 8.1 形式化挑战

这是代数几何形式化的**核心目标之一**，挑战包括：

1. **分次结构处理**：需要在类型论中处理分次环和分次模
2. **Čech复形构造**：处理复杂的交错和与符号
3. **Koszul复形联系**：建立Čech与Koszul复形的关系
4. **正合性证明**：需要精细的交换代数论证

### 8.2 Mathlib4现状

```lean
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

-- 射影空间的定义
#check ProjectiveSpectrum

-- 扭曲层（部分实现）
-- #check twistingSheaf

-- 上同调计算（待开发）
```

### 8.3 形式化路线图

| 阶段 | 目标 | 难度 | 依赖 |
|------|------|------|------|
| 1 | 分次环/模完善 | 中 | Mathlib基础 |
| 2 | Proj构造完整 | 中 | 分次代数 |
| 3 | O(d)层定义 | 中 | Proj |
| 4 | 标准仿射覆盖 | 低 | Proj |
| 5 | Čech复形构造 | 高 | 覆盖+层论 |
| 6 | H^0计算 | 中 | Čech |
| 7 | H^n计算 | 高 | Koszul复形 |
| 8 | 中间消失 | 高 | 正合性论证 |

### 8.4 形式化代码框架

```lean
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.Homology.Homology

namespace AlgebraicGeometry

variable (A : Type*) [CommRing A] (n : ℕ)

-- 射影空间定义
abbrev ProjectiveSpace : Scheme :=
  ProjectiveSpectrum (MvPolynomial (Fin (n+1)) A)

-- 扭曲层 O(d)
def twistingSheaf (d : ℤ) : SheafOfModules (ProjectiveSpace A n).ringCatSheaf :=
  sorry  -- 需要Proj上的层构造

-- 射影空间上同调计算主定理
theorem projective_space_cohomology (d : ℤ) (q : ℕ) :
    cohomology (ProjectiveSpace A n) (twistingSheaf A n d) q =
    match q with
    | 0 => 分次部分 (MvPolynomial (Fin (n+1)) A) d  -- H^0
    | n => 负分次部分 (1/(T_0...T_n) * ...) d      -- H^n
    | _ => 0                                        -- 中间消失
  := by
  -- 步骤1: 使用Čech上同调
  rw [cohomology_eq_cech _ _ (standardAffineCover _)]
  -- 步骤2: 分次分解
  apply graded_decomposition
  -- 步骤3: Koszul复形联系
  rw [cech_eq_koszul]
  -- 步骤4: Koszul复形的正合性
  apply koszul_exact_middle
  -- 步骤5: 最高上同调计算
  simp [koszul_cohomology_top]

-- H^0的具体描述
theorem H0_twistingSheaf (d : ℕ) :
    cohomology (ProjectiveSpace A n) (twistingSheaf A n d) 0 ≅
    ModuleCat.of A (homogeneousComponent d (MvPolynomial (Fin (n+1)) A)) :=
  sorry

-- 中间上同调消失
theorem Hq_twistingSheaf_vanishing (q : ℕ) (hq : 0 < q ∧ q < n) (d : ℤ) :
    cohomology (ProjectiveSpace A n) (twistingSheaf A n d) q = 0 :=
  sorry

-- H^n的具体描述
theorem Hn_twistingSheaf (d : ℤ) :
    cohomology (ProjectiveSpace A n) (twistingSheaf A n d) n ≅
    ModuleCat.of A (negativelyGradedComponent (n+1) d) :=
  sorry

end AlgebraicGeometry
```

### 8.5 建议实现策略

**短期（6个月）**：
- 完善Mathlib中分次环理论
- 完成Proj构造的核心部分
- 定义扭曲层O(d)

**中期（1-2年）**：
- 建立Čech上同调计算框架
- 完成H^0和H^n的计算
- 证明中间消失

**长期（2-3年）**：
- 完整的形式化证明
- 推广到一般射影概形
- 建立Serre对偶的形式化

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 02O3}
}

@article{serre1955faisceaux,
  title     = {Faisceaux alg{\'e}briques coh{\'e}rents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  pages     = {197--278},
  year      = {1955}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
