---
msc_primary: 03B38
msc_secondary: [03B15, 55U35, 68T15]
title: nLab - 同伦类型论 (Homotopy Type Theory) 中文解读
nlab_url: https://ncatlab.org/nlab/show/homotopy+type+theory
processed_at: '2026-04-09'
---

# nLab - 同伦类型论 (Homotopy Type Theory) 中文解读

**原文链接**: https://ncatlab.org/nlab/show/homotopy+type+theory  
**最后修订**: 2026年1月14日（第127版）  
**nLab讨论区**: https://nforum.ncatlab.org/discussion/3185/  
**解读版本**: v0.1（框架版）

---

## 一、核心概念

### 1.1 类型即空间 (Types as Spaces)

**核心思想**:

同伦类型论的核心洞见是**将类型解释为拓扑空间（或更准确地说是∞-群胚）**：

| 类型论语义 | 空间解释 | 直观理解 |
|------------|----------|----------|
| 类型 $A$ | 空间 $A$ | 点的集合带有拓扑结构 |
| 项 $a : A$ | 点 $a \in A$ | 空间中的一个点 |
| 等同类型 $a =_A b$ | 路径空间 | 从 $a$ 到 $b$ 的所有路径 |
| 恒等证明 $p : a = b$ | 路径 $p: a \leadsto b$ | 连接两点的道路 |

**哲学意义**:

这一对应关系由 [Awodey](https://ncatlab.org/nlab/show/Steve+Awodey) 和 [Warren](https://ncatlab.org/nlab/show/Michael+Warren) 以及独立地由 [Voevodsky](https://ncatlab.org/nlab/show/Vladimir+Voevodsky) 发现，建立了**类型论与代数拓扑之间**的深刻联系。

### 1.2 等同即路径 (Equality as Path)

**Martin-Löf 等同类型**:

在Martin-Löf类型论中，对类型 $A$ 和项 $a, b : A$，可以构造**等同类型** $Id_A(a, b)$（也记作 $a =_A b$）。

**关键洞见**:

同伦类型论提出：

```
等同证明 p : a = b  ⟺  路径 p : a ↝ b
```

这意味着：

- **自反性** $refl_a : a = a$ 对应**常值路径**（停留在点 $a$）
- **对称性** $p^{-1} : b = a$ 对应**路径的反向**
- **传递性** $p \cdot q : a = c$ 对应**路径的拼接**

### 1.3 高阶等同 (Higher Identity)

**∞-群胚结构**:

如果 $p, q : a = b$ 是两个等同证明，我们可以再问：$p = q$ 吗？

```
a ====== b   （第一层：路径/1-态射）
  \    /
   \  /     （第二层：路径之间的同伦/2-态射）
    \/
   p≈q
```

这产生了**无穷层的结构**：

| 层次 | 类型论语义 | 拓扑语义 |
|------|------------|----------|
| 0 | 类型 $A$ | 空间 $A$ |
| 1 | $a = b$ | 路径 |
| 2 | $p =_{a=b} q$ | 路径间的同伦 |
| 3 | $\alpha =_{p=q} \beta$ | 同伦之间的同伦 |
| ... | ... | ... |

**van Kampen 定理的类型论版本**:

同伦类型论可以证明拓扑中的经典结果，如Seifert-van Kampen定理的类型论版本。

---

## 二、Martin-Löf 类型论基础

### 2.1 类型构造器

**基本类型**:

| 类型 | 构造 | 说明 |
|------|------|------|
| 积类型 $A \times B$ | $(a, b)$ | 有序对 |
| 和类型 $A + B$ | $inl(a)$, $inr(b)$ | 不相交并 |
| 函数类型 $A \to B$ | $\lambda x. b(x)$ | 依赖函数（非依赖时）|
| 依赖积 $\prod_{x:A} B(x)$ | $\lambda x. b(x)$ | 对每个家庭给出一个元素 |
| 依赖和 $\sum_{x:A} B(x)$ | $(a, b)$ | 带索引的对 |
| 等同类型 $a =_A b$ | $refl_a$ | 等同证明 |

### 2.2 归纳原理

**自然数类型 $\mathbb{N}$**:

```
0 : ℕ
succ : ℕ → ℕ

归纳原理:
给定 P : ℕ → Type,
base : P(0),
step : Π(n:ℕ). P(n) → P(succ(n)),
可得 ind(P, base, step) : Π(n:ℕ). P(n)
```

**等同类型的归纳原理 (J-规则)**:

```
J : Π(P: Π(a,b:A). (a=b) → Type).
    (Π(a:A). P(a, a, refl_a)) →
    Π(a,b:A). Π(p:a=b). P(a, b, p)
```

直观：要证明关于所有等同证明的命题，只需证明关于自反性的情况。

### 2.3 类型论与构造主义

**构造主义数学**:

Martin-Löf类型论是**构造主义**的：

- 要证明 $A \lor B$，必须构造 $inl(a)$ 或 $inr(b)$
- 要证明 $\exists x. P(x)$，必须给出具体的 $a$ 和 $p : P(a)$
- **排中律** $A \lor \neg A$ 不是普遍成立的

这与经典逻辑形成对比，对计算机形式化证明至关重要。

---

## 三、单值公理 (Univalence Axiom)

### 3.1 类型的等价

**同伦等价**:

函数 $f : A \to B$ 是**同伦等价**，如果存在 $g : B \to A$ 使得：

```
g ∘ f ~ id_A   （同伦于恒等）
f ∘ g ~ id_B
```

记 $A \simeq B$ 为"$A$ 同伦等价于 $B$"的类型。

### 3.2 单值公理陈述

**Voevodsky 单值公理**:

```
(A =_𝒰 B) ≃ (A ≃ B)
```

其中：
- $\mathcal{U}$ 是宇宙（类型的类型）
- $A =_𝒰 B$ 是类型的等同
- $A ≃ B$ 是类型的同伦等价

**核心意义**:

> **结构等同 ⇔ 结构等价**

换言之：
- 如果两个类型作为数学结构是等价的（同伦等价）
- 那么它们在类型论中就是**等同的**（有等同证明）
- 反之亦然

### 3.3 单值公理的推论

**同构即等同**:

对于代数结构（群、环、范畴等），结构同构蕴涵等同。

```
G ≅ H  ⟹  G = H   （在适当的宇宙上下文中）
```

这使得**传递构造**成为可能：

- 先在类型 $A$ 上构造对象 $x$
- 证明 $A = B$（使用单值公理）
- 自动得到 $B$ 上相应的对象

**函数外延性**:

单值公理蕴涵函数外延性：

```
(Π(x:A). f(x) = g(x)) → (f = g)
```

即：逐点相等的函数是等同的。

---

## 四、与∞-群胚的关系

### 4.1 ∞-群胚的模型

**Grothendieck 猜想**:

类型的结构对应于**∞-群胚**（∞-groupoid）：

| 结构 | 类型论语义 | ∞-群胚语义 |
|------|------------|------------|
| 0-胞腔 | 项 $a : A$ | 对象 |
| 1-胞腔 | $p : a = b$ | 态射 |
| 2-胞腔 | $\alpha : p = q$ | 2-态射 |
| n-胞腔 | n阶等同 | n-态射 |

**弱∞-群胚**: 所有高阶结构都是"弱"的（满足结合律、单位律等仅到同伦）。

### 4.2 单纯集模型

**Kapulkin-Lumsdaine** 证明了：

Martin-Löf类型论（加单值公理）可以在**单纯集模型**中得到解释，其中：

- 类型 = Kan复形
- 等同类型 = 路径空间
- 单值公理成立

这为HoTT提供了**范畴语义**。

### 4.3 与∞-范畴的关系

**联系**:

- ∞-群胚是特殊的∞-范畴（所有态射可逆）
- 同伦类型论可以看作是"∞-群胚的内在语言"
- 有研究将HoTT扩展到一般的∞-范畴（如Simpson、Riehl-Shulman的工作）

---

## 五、与Lean4/Coq/Agda的关联

### 5.1 形式化证明助手

**Coq**:

- 最早的HoTT实现之一
- 使用**归纳类型族**模拟高阶等同结构
- [HoTT/HoTT](https://github.com/HoTT/HoTT) 库

**Agda**:

- 依赖类型语言，天然支持HoTT
- [Cubical Agda](https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html): 立方类型论实现
- 直接计算路径和高阶结构

**Lean4**:

- 数学库 [mathlib4](https://github.com/leanprover-community/mathlib4)
- 主要使用**公理化集合论**基础
- 有HoTT库（较少维护）

### 5.2 立方类型论 (Cubical Type Theory)

**动机**:

解决HoTT中的**计算问题**：单值公理作为公理，不给出计算行为。

**核心思想**:

引入**区间类型** $\mathbb{I}$，路径是函数 $p : \mathbb{I} \to A$。

```
路径 p : a = b  定义为  p : 𝕀 → A, p(0) = a, p(1) = b
```

**立方Ag达**:

- 原生支持立方类型论
- 可以计算单值公理
- 更适合实际形式化证明

### 5.3 形式化数学项目

| 项目 | 工具 | 内容 |
|------|------|------|
| HoTT Book 形式化 | Coq/Agda | 教材中的定理 |
| [Unimath](https://github.com/UniMath/UniMath) | Coq | 基于单值的数学 |
| [TypeTopology](https://github.com/martinescardo/TypeTopology) | Agda | 拓扑的构造主义发展 |
| [lean-hott](https://github.com/gebner/lean-hott) | Lean | Lean4的HoTT库 |

---

## 六、与形式化证明的关系

### 6.1 数学形式化的新范式

**传统方法** (基于集合论/ZFC): 

```
ZFC公理系统 → 形式化集合 → 形式化数学对象
```

**HoTT方法**:

```
类型论 + 单值公理 → 结构即类型 → 结构等同即类型等同
```

**优势**:

1. **结构不变性**：同构的结构行为完全一致
2. **高阶结构**：自然处理高阶同伦信息
3. **构造主义**：算法可提取、可计算

### 6.2 实际应用案例

**同伦群计算**:

[Brunerie](https://ncatlab.org/nlab/show/Guillaume+Brunerie) 证明了：

```
π₄(S³) ≅ ℤ/2ℤ
```

使用HoTT在Agda中形式化完成，这是第一个用类型论证明的高阶同伦群结果。

**谱序列**:

使用HoTT发展谱序列理论，为代数拓扑的形式化提供工具。

### 6.3 与Lean4数学库的对比

| 特征 | HoTT/UF | Lean4/mathlib |
|------|---------|---------------|
| 基础 | 类型论+单值 | 类型论+选择公理 |
| 外延性 | 函数外延性 | 经典逻辑 |
| 高阶结构 | 原生支持 | 公理化处理 |
| 计算性 | 好（尤其立方TT）| 良好 |
| 数学覆盖 | 发展中 | 非常广泛 |
| 社区规模 | 较小但活跃 | 大且活跃 |

---

## 七、与FormalMath的关联

### 7.1 当前覆盖情况

**相关文档**:

- `docs/01-基础结构/02-核心理论/数理逻辑基础/06-类型论基础.md`
- `docs/01-基础结构/02-核心理论/数理逻辑基础/07-直觉主义逻辑.md`
- `docs/02-代数结构/02-核心理论/同调代数/12-导出范畴与同伦论.md`

**现状评估**:

- ⏳ 同伦类型论系统内容待补充
- ⏳ 单值公理及其应用未覆盖
- ⏳ 与形式化证明的关联待建立
- ⏳ Martin-Löf类型论基础需深化

### 7.2 建议补充内容

| 主题 | 优先级 | 关联分支 |
|------|--------|----------|
| Martin-Löf类型论 | P1 | 数理逻辑、形式化证明 |
| 同伦类型论基础 | P1 | 代数拓扑、形式化证明 |
| 单值公理 | P2 | 数理逻辑、代数几何 |
| 立方类型论 | P3 | 形式化证明 |
| ∞-群胚理论 | P2 | 代数拓扑、范畴论 |

### 7.3 与现有内容的连接

**数理逻辑模块**:

```
数理逻辑基础
├── 一阶逻辑
├── 模型论
├── 递归论
├── 证明论
├── 类型论（现有）
│   └── 简单类型λ演算
├── Martin-Löf类型论（建议补充）
└── 同伦类型论（建议补充）
    └── 单值公理
```

**代数拓扑模块**:

```
代数拓扑
├── 同伦论基础
│   └── 基本群
├── 高阶同伦论
│   └── 同伦群
├── 同伦类型论视角（建议补充）
│   ├── 类型即空间
│   ├── 等同即路径
│   └── πₙ的类型论计算
└── ∞-群胚
```

---

## 八、学习路径

### 8.1 前置知识

```
1. 数理逻辑基础
   ├── 命题逻辑
   ├── 一阶逻辑
   └── 自然演绎系统

2. 类型论入门
   ├── λ演算
   └── 简单类型论

3. 代数拓扑基础（可选但推荐）
   ├── 同伦
   ├── 基本群
   └── 同伦提升性质

4. 范畴论基础（可选但推荐）
   ├── 范畴、函子、自然变换
   └── 伴随函子

5. 同伦类型论
    ├── Martin-Löf类型论
    ├── 同伦解释
    └── 单值公理
```

### 8.2 推荐资源

| 资源 | 作者/来源 | 难度 | 备注 |
|------|----------|------|------|
| **The HoTT Book** | HoTT社区 | ⭐⭐⭐⭐ | 权威入门教材，免费 |
| 同伦类型论讲义 | E. Rijke | ⭐⭐⭐⭐ | 较新的系统教材 |
| Type Theory and Formal Proof | Nederpelt & Geuvers | ⭐⭐⭐ | 类型论基础 |
| Introduction to Homotopy Type Theory | P. Padilla | ⭐⭐⭐⭐ | 研究生课程笔记 |
| Cubical Type Theory | Cohen et al. | ⭐⭐⭐⭐⭐ | 立方类型论原始论文 |

### 8.3 nLab相关条目

- [homotopy type theory](https://ncatlab.org/nlab/show/homotopy+type+theory)
- [univalence axiom](https://ncatlab.org/nlab/show/univalence+axiom)
- [Martin-Löf type theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+type+theory)
- [identity type](https://ncatlab.org/nlab/show/identity+type)
- [higher inductive type](https://ncatlab.org/nlab/show/higher+inductive+type)
- [cubical type theory](https://ncatlab.org/nlab/show/cubical+type+theory)
- [synthetic homotopy theory](https://ncatlab.org/nlab/show/synthetic+homotopy+theory)

---

## 九、深化行动项

### 立即行动（Round 35-36）

- [ ] 在FormalMath创建同伦类型论概念条目
- [ ] 补充Martin-Löf类型论基础文档
- [ ] 建立与形式化证明模块的链接

### 中期计划（Round 37-40）

- [ ] 建设单值公理专题文档
- [ ] 添加高阶归纳类型(HIT)介绍
- [ ] 与代数拓扑模块建立对应关系

### 长期目标（Round 41+）

- [ ] 完成HoTT基础体系文档建设
- [ ] 探索与Lean4 HoTT库的对接
- [ ] 补充立方类型论内容

---

**解读人**: AI Assistant  
**审核状态**: 待数理逻辑专家审核  
**最后更新**: 2026年4月9日  
**下次更新**: 随nLab更新
