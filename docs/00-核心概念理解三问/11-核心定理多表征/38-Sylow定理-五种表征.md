# Sylow定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 群论
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Sylow定理 |
| **领域**: 群论 |
| **发现者** | Ludwig Sylow (1872) |
| **前置知识** | 有限群、p-子群、群作用 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

设G是有限群，|G| = pⁿm，其中p是素数，gcd(p,m)=1。

**Sylow第一定理**：G有阶为pⁿ的子群（Sylow p-子群）。

**Sylow第二定理**：所有Sylow p-子群共轭。

**Sylow第三定理**：设nₚ是Sylow p-子群的个数，则：
- nₚ ≡ 1 (mod p)
- nₚ | m

### 1.2 Lean 4 形式化

```lean
import Mathlib.GroupTheory.Sylow

-- Sylow第一定理
theorem sylow_exists {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, True := ⟨default, trivial⟩

-- Sylow第二定理
theorem sylow_conjugate {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (P Q : Sylow p G) : ∃ g : G, P.toSubgroup = g • Q.toSubgroup := by
  exact Sylow.exists_smul_eq P Q

-- Sylow第三定理
theorem sylow_card_mod_p {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  exact card_sylow_modEq_one p G
```

---

## 二、几何表征（可视化）

### 2.1 Sylow子群结构

```text
    G（阶 = pⁿ × m）
    │
    ├── P₁ (Sylow p-子群，阶pⁿ)
    ├── P₂ (共轭于P₁)
    ├── ...
    └── Pₙₚ

    所有Pᵢ共轭，nₚ ≡ 1 (mod p)
```

### 2.2 群作用视角

```text
G作用在Sylow p-子群的集合上（共轭）：
├─ 作用传递（第二定理）
├─ 轨道大小 | |G|
└─ 稳定子 = 正规化子
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Sylow定理**：有限群中，每个素数幂"充分"存在为子群，且这些子群"协调"

### 3.2 因数分解类比

- |G| = pⁿm：群阶的素数分解
- Sylow p-子群：群中"p的成分"的最大体现
- 共轭：所有"p-成分"本质相同

### 3.3 为什么重要？

Sylow定理是分类有限群的核心工具

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
from sympy.combinatorics import PermutationGroup, Permutation
from sympy.ntheory import factorint

def find_sylow_subgroups(G, p):
    """
    找群G的Sylow p-子群
    """
    order_G = G.order()
    factors = factorint(order_G)

    if p not in factors:
        return []  # p不整除|G|

    n = factors[p]
    sylow_order = p ** n

    # 枚举所有子群（简化：仅适用于小群）
    sylow_subgroups = []
    for H in G.subgroups():
        if H.order() == sylow_order:
            sylow_subgroups.append(H)

    return sylow_subgroups

def verify_sylow_third(G, p):
    """验证Sylow第三定理"""
    sylows = find_sylow_subgroups(G, p)
    n_p = len(sylows)

    order_G = G.order()
    factors = factorint(order_G)
    n = factors.get(p, 0)
    m = order_G // (p ** n)

    # 验证 n_p ≡ 1 (mod p) 且 n_p | m
    cond1 = (n_p % p == 1)
    cond2 = (m % n_p == 0)

    print(f"n_{p} = {n_p}")
    print(f"n_{p} ≡ 1 (mod {p}): {cond1}")
    print(f"n_{p} | {m}: {cond2}")

    return cond1 and cond2

# 示例：S₃ (阶6 = 2×3)
# Sylow 2-子群：3个（阶2），Sylow 3-子群：1个（阶3）
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Sylow定理 = 群的p-局部化
├─ Sylow p-子群：G的"p-局部结构"
├─ 共轭：在G的伴随作用下等价
└─ p-群范畴：p-主部分的分类
```

### 5.2 推广

- **p-融合**：Sylow子群间的关系
- **Burnside定理**：应用Sylow定理
- **局部-整体原理**：通过p-子群理解G

### 5.3 群论中的地位

```text
有限群分类 → 找Sylow子群 → 分析正规化子 → 确定结构
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Lagrange定理** | 基础 |
| **Cauchy定理** | p整除|G| ⟹ ∃阶p元素 |
| **Burnside定理** | pᵃqᵇ阶群可解 |

---

**状态**: ✅ 完成
