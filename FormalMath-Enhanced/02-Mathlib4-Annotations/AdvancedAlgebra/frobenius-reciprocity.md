---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Frobenius互反律
---
# Frobenius互反律

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.FrobeniusReciprocity

namespace RepresentationTheory

/-- Frobenius互反律：诱导与限制函子的伴随性 -/
theorem frobenius_reciprocity
    {k G H : Type*} [Field k] [Group G] [Group H]
    (φ : H →* G) (W : Rep k H) (V : Rep k G) :
    (φ.inducedModule W →ₗ[k[G]] V) ≃ₗ[k]
    (W →ₗ[k[H]] φ.restrictedModule V) := by
  -- 构造自然的线性同构
  apply Hom.induction.equiv
  intro f
  constructor
  · -- 方向：诱导 → 限制
    intro x
    exact f (φ x)
  · -- 方向：限制 → 诱导
    intro x
    -- 使用张量积的泛性质
    sorry

end RepresentationTheory
```

## 数学背景

Frobenius互反律由Ferdinand Georg Frobenius在1898年建立，描述了群表示论中两个基本运算——诱导(induction)和限制(restriction)之间的深刻对偶关系。这一定律表明：从子群H的表示诱导到G，再映射到G的表示，等价于直接从H的表示映射到限制的表示。这一结果奠定了诱导表示理论的基础。

## 直观解释

Frobenius互反律如同一座桥梁，连接了子群和母群的表示世界。想象G-表示是一个大舞台，H-表示是其中的子舞台。互反律告诉我们：从大舞台诱导出的演员（诱导表示）到大舞台表演（G-同态），与小舞台演员直接到子舞台表演（H-同态）之间存在自然的对应。这种伴随性是范畴论中伴随函子的典型例子。

## 形式化表述

设 $H \leq G$ 是有限群，$k$ 是域。

**Frobenius互反律**：存在自然的线性同构
$$\text{Hom}_{k[G]}(\text{Ind}_H^G W, V) \cong \text{Hom}_{k[H]}(W, \text{Res}_H^G V)$$

等价表述：诱导函子 $\text{Ind}_H^G$ 与限制函子 $\text{Res}_H^G$ 是一对伴随函子，$\text{Ind}_H^G$ 是左伴随。

## 证明思路

1. **构造映射**：定义从诱导表示的同态到限制表示的同态的转换
2. **利用张量积**：将诱导表示写为 $k[G] \otimes_{k[H]} W$
3. **应用张量-Hom伴随**：这是代数中的标准伴随对
4. **验证自然性**：证明同构对 $W$ 和 $V$ 的函子性

## 示例

### 示例 1：对称群的诱导表示

**问题**：设 $H = S_2 \times S_1 \leq S_3$，计算平凡表示从 $H$ 到 $S_3$ 的诱导。

**解答**：

使用Frobenius互反律和特征标正交性：
$$\langle \chi_{\text{Ind}_H^G \mathbf{1}}, \chi_i \rangle = \langle \mathbf{1}, \chi_i|_H \rangle$$

计算得：$\text{Ind}_H^G \mathbf{1} = \chi_1 \oplus \chi_3$（平凡表示加标准表示）

### 示例 2：Mackey分解

**问题**：设 $K, H \leq G$，研究 $\text{Res}_K^G \text{Ind}_H^G W$ 的结构。

**解答**：

利用双陪集分解和Frobenius互反律，可得Mackey公式：
$$\text{Res}_K^G \text{Ind}_H^G W = \bigoplus_{g \in K \backslash G / H} \text{Ind}_{K \cap gHg^{-1}}^K \text{Res}_{K \cap gHg^{-1}}^{gHg^{-1}} W^g$$

## 应用

- **Artin诱导定理**：有理表示的刻画
- **Brauer特征标**：模表示论的核心工具
- **Clifford理论**：正规子群表示的研究
- **Langlands纲领**：自守表示的构造
- **量子场论**：对称性诱导的粒子谱

## 相关概念

- [Maschke定理](./maschke-theorem.md)：表示的完全可约性
- [特征标正交性](./character-orthogonality.md)：特征标的内积理论
- [诱导表示](./induced-representation.md)：从子群构造母群表示
- Mackey理论：诱导与限制的交互
- Nakayama关系：模论版本的互反律

## 参考

### 教材

- Serre, J.P. Linear Representations of Finite Groups. Springer, 1977. Chapter 7
- Alperin, J.L. Local Representation Theory. Cambridge, 1986. Chapter 3

### 论文

- Frobenius, G. Über Relationen zwischen den Charakteren einer Gruppe und denen ihrer Untergruppen. Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften, 501-515, 1898.
- Nakayama, T. Frobeniusean Algebras II. Annals of Math., 42(1): 1-21, 1941.

### 在线资源

- [Frobenius Reciprocity Wikipedia](https://en.wikipedia.org/wiki/Frobenius_reciprocity)
- [Groupprops - Frobenius reciprocity][https://groupprops.subwiki.org/wiki/Frobenius_reciprocity](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
