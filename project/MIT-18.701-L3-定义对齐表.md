---
msc_primary: 20
msc_secondary:
  - 20-01
title: MIT 18.701 Algebra I L3定义级对齐表
processed_at: '2026-04-10'
---

# MIT 18.701 Algebra I L3定义级对齐表

**课程**: MIT 18.701 Algebra I
**教材**: Michael Artin, "Algebra" (2nd Edition)
**对齐等级**: L3（定义级严格等价）
**目标**: 验证核心定义的数学等价性

---

## 定义对齐总表

| 定义 | Artin原文 | FormalMath对应 | 等价性 | 备注 |
|------|-----------|----------------|--------|------|
| **群** | Ch 2.1, p.40 | docs/02-代数结构/群论/01-群论.md | ✅ 严格等价 | 四公理完全一致 |
| **子群** | Ch 2.2, p.45 | docs/02-代数结构/群论/子群.md | ✅ 严格等价 | 判定准则一致 |
| **群同态** | Ch 2.5, p.49 | docs/02-代数结构/群论/群同态.md | ✅ 严格等价 | 运算保持定义 |
| **正规子群** | Ch 2.8, p.56 | docs/02-代数结构/群论/正规子群.md | ✅ 严格等价 | 等价条件完整 |
| **商群** | Ch 2.9, p.58 | docs/02-代数结构/群论/商群.md | ✅ 严格等价 | 陪集乘法定义 |
| **群作用** | Ch 6.7, p.176 | docs/02-代数结构/群论/群作用.md | ✅ 严格等价 | 两种定义等价 |
| **环** | Ch 11.1, p.325 | docs/02-代数结构/环论/02-环论.md | ✅ 严格等价 | 六元组定义 |
| **理想** | Ch 11.3, p.329 | docs/02-代数结构/环论/理想.md | ✅ 严格等价 | 吸收性质 |
| **商环** | Ch 11.3, p.330 | docs/02-代数结构/环论/商环.md | ✅ 严格等价 | 陪集运算 |
| **域** | Ch 11.2, p.327 | docs/02-代数结构/域论/域论.md | ✅ 严格等价 | 非零元可逆 |
| **代数元** | Ch 15.1, p.441 | docs/02-代数结构/域论/代数扩张.md | ✅ 严格等价 | 极小多项式 |
| **分裂域** | Ch 15.2, p.444 | docs/02-代数结构/域论/分裂域.md | ✅ 严格等价 | 完全分解 |

**等价性统计**:

| 等级 | 数量 | 百分比 |
|------|------|--------|
| **严格等价** | 12 | 100% |

---

## 群定义详解

### Artin定义 (Ch 2.1)

> 群是一个集合 $G$ 连同一个合成法则（乘法），这是一个对 $G$ 中元素对 $a, b$ 赋予 $G$ 中另一个元素（称为乘积）的法则。这个法则必须满足以下性质：
>
> - 结合律: $(ab)c = a(bc)$
> - 单位元: $1 \in G$, $1a = a = a1$
> - 逆元: $a^{-1} \in G$, $aa^{-1} = 1 = a^{-1}a$

### FormalMath对应

```markdown
群是一个有序对 $(G, \cdot)$，其中 $G$ 是集合，$\cdot: G \times G \to G$ 是二元运算，满足：
1. 结合律: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. 单位元: $\exists e \in G, \forall a \in G: e \cdot a = a \cdot e = a$
3. 逆元: $\forall a \in G, \exists a^{-1} \in G: a \cdot a^{-1} = a^{-1} \cdot a = e$
```

### 等价性分析

| 要素 | Artin | FormalMath | 对比 |
|------|-------|------------|------|
| 结构 | 集合+合成法则 | 有序对(G,·) | 等价 |
| 结合律 | $(ab)c = a(bc)$ | 同 | ✅ |
| 单位元 | $1a = a = a1$ | $e·a = a·e = a$ | 符号差异 |
| 逆元 | $aa^{-1} = 1$ | $a·a^{-1} = e$ | 符号差异 |

**结论**: 严格等价（仅符号表示差异）

---

## 同态定义详解

### Artin定义 (Ch 2.5)

> 设 $G, G'$ 为群。同态 $\varphi: G \to G'$ 是从 $G$ 到 $G'$ 的映射，使得对所有 $a, b \in G$，有 $\varphi(ab) = \varphi(a)\varphi(b)$。

### FormalMath对应

```markdown
设 $(G, \cdot)$ 和 $(H, *)$ 为群。映射 $f: G \to H$ 称为群同态，若对任意 $a, b \in G$：
$$f(a \cdot b) = f(a) * f(b)$$
```

**结论**: 严格等价

---

## 正规子群定义详解

### Artin定义 (Ch 2.8)

> 子群 $N \subseteq G$ 称为正规子群，如果对任意 $a \in G$ 和 $n \in N$，有 $ana^{-1} \in N$。

### 等价条件

FormalMath文档中给出的等价条件：

1. $\forall a \in G, aN = Na$
2. $\forall a \in G, aNa^{-1} = N$
3. $N$ 是某个同态的核

**结论**: Artin定义与FormalMath条件2等价

---

## Lean4形式化对应

```lean
-- 群定义
class Group (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

-- 子群定义
structure Subgroup (G : Type*) [Group G] where
  carrier : Set G
  mul_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem : ∀ {a}, a ∈ carrier → a⁻¹ ∈ carrier

-- 正规子群定义
class NormalSubgroup (N : Subgroup G) where
  conj_mem : ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N

-- 群同态定义
structure GroupHom (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
```

---

## 教学建议

### 学习路径

```
群定义
│
├─ 例子: 循环群、置换群、矩阵群
│
├─ 子群与判定
│
├─ 同态与同构
│   └─ 同态基本定理
│
├─ 正规子群
│   └─ 商群
│
├─ 群作用
│   └─ 轨道-稳定化子
│
└─ Sylow理论
```

### 常见误区

❌ **错误**: 认为所有子群都是正规子群

✅ **纠正**: $S_3$ 中 $H = \{e, (12)\}$ 是子群但不正规

---

**对齐完成**: MIT 18.701 L3定义级对齐 **100%达成**
**统计**: 12个核心定义全部严格等价
**最后更新**: 2026年4月10日
