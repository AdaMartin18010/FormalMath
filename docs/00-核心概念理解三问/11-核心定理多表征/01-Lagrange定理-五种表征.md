---
msc_primary: "20A05"
msc_secondary: ["20D99"]
---

# Lagrange定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 群论
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Lagrange定理 |
| **领域** | 群论 |
| **发现者** | Joseph-Louis Lagrange (1771) |
| **前置知识** | 群、子群、陪集 |
| **Mathlib** | `Mathlib.GroupTheory.Coset` |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**定理（Lagrange）**：设G是有限群，H是G的子群，则：

$$|G| = |H| \cdot [G:H]$$

其中 [G:H] 是H在G中的指数（陪集个数）。

**等价表述**：|H| 整除 |G|

### 1.2 Lean 4 形式化

```lean
import Mathlib.GroupTheory.Coset

theorem lagrange {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card G = Fintype.card H * H.index := by
  rw [← H.card_mul_index]

-- 推论：子群阶整除群阶
theorem subgroup_card_dvd {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  use H.index
  exact lagrange H
```

### 1.3 证明梗概

```text
        [Lagrange定理证明]
                │
    ┌───────────┴───────────┐
    │                       │
[陪集分解]              [等势性]
G = gH ∪ g'H ∪ ...     |gH| = |H|
    │                       │
不交并                  左乘是双射
    │                       │
    └───────────┬───────────┘
                │
        |G| = (陪集数) × |H|
```

**关键步骤**：

1. 证明左陪集两两不交或相等
2. 证明每个左陪集与H等势（通过 g·: H → gH）
3. G是所有左陪集的不交并
4. 计数得出结论

---

## 二、几何表征（可视化）

### 2.1 核心图示

```text
        [群G被子群H的陪集分割]

    G = 24个元素（以S₄为例）
    ┌────────────────────────────────┐
    │                                │
    │  ┌──────┐ ┌──────┐ ┌──────┐  │
    │  │  H   │ │ g₁H  │ │ g₂H  │  │
    │  │(6个) │ │(6个) │ │(6个) │  │
    │  └──────┘ └──────┘ └──────┘  │
    │                                │
    │  ┌──────┐                      │
    │  │ g₃H  │  ...共4个陪集        │
    │  │(6个) │                      │
    │  └──────┘                      │
    │                                │
    └────────────────────────────────┘

    |G| = 24 = 6 × 4 = |H| × [G:H]
```

### 2.2 动态理解

```text
想象一个大房间（群G）被墙分成几个相等的小房间（陪集）

    [子群H]        [陪集gH]        [陪集g'H]
    ┌─────┐        ┌─────┐         ┌─────┐
    │e    │   g×   │g    │   g'×   │g'   │
    │h₁   │ ────→  │gh₁  │  ────→  │g'h₁ │
    │h₂   │        │gh₂  │         │g'h₂ │
    │...  │        │...  │         │...  │
    └─────┘        └─────┘         └─────┘

    每个房间大小相同！
```

### 2.3 陪集分解的可视化

```text
ℤ/12ℤ 中子群 H = {0,3,6,9} 的陪集分解：

    0  1  2  3  4  5  6  7  8  9  10 11
    ├──┼──┼──┼──┼──┼──┼──┼──┼──┼──┼──┤
    │  │  │  │  │  │  │  │  │  │  │  │
    └──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┘

    H     = {0, 3, 6, 9}    ← 陪集1
    1+H   = {1, 4, 7, 10}   ← 陪集2
    2+H   = {2, 5, 8, 11}   ← 陪集3

    12 = 4 × 3（子群阶 × 陪集数）
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Lagrange定理**：把群分成"大小相等的小块"（陪集），总元素数 = 小块大小 × 小块个数

### 3.2 生活类比

**班级分组类比**：

```text
一个班有60个学生（群G）
按宿舍分组，每个宿舍6人（子群H）
├─ 每个宿舍恰好6人（陪集等势于H）
├─ 宿舍之间没有交集（陪集不交）
├─ 所有宿舍覆盖全班（陪集并=G）
└─ 60 = 6 × 10（10个宿舍）

宿舍人数必须整除班级人数！
```

**蛋糕切分类比**：

```text
一个圆蛋糕（群G）
用特定刀法切成相等的块（陪集）
├─ 每块大小完全相同
├─ 不重复切
├─ 覆盖整个蛋糕
└─ 块数 × 每块大小 = 整个蛋糕
```

### 3.3 为什么是真的？

**核心直觉**：

- 左乘是"重新标记"——不改变大小
- g·H 与 H "形状相同"，只是"位置不同"
- 群被"等大的块"完美分割

```text
为什么 |gH| = |H|？

映射 φ: H → gH, h ↦ gh 是双射！
├─ 单射：gh₁=gh₂ ⟹ h₁=h₂（消去律）
└─ 满射：gH的每个元素gh都有原像h
```

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
from itertools import permutations
from typing import Set, List, Callable

def lagrange_verification(group: Set, subgroup: Set,
                          op: Callable) -> dict:
    """
    验证Lagrange定理

    Parameters:
        group: 群的元素集合
        subgroup: 子群的元素集合
        op: 群运算（二元函数）

    Returns:
        包含陪集分解和验证结果的字典
    """
    cosets = []
    remaining = set(group)

    while remaining:
        # 选取一个代表元
        g = next(iter(remaining))
        # 计算陪集 gH
        coset = {op(g, h) for h in subgroup}
        cosets.append(coset)
        remaining -= coset

    return {
        'group_order': len(group),
        'subgroup_order': len(subgroup),
        'num_cosets': len(cosets),
        'cosets': cosets,
        'lagrange_holds': len(group) == len(subgroup) * len(cosets)
    }

# 例子：ℤ/12ℤ 和子群 {0,3,6,9}
Z12 = set(range(12))
H = {0, 3, 6, 9}
add_mod12 = lambda a, b: (a + b) % 12

result = lagrange_verification(Z12, H, add_mod12)
print(f"|G| = {result['group_order']}")
print(f"|H| = {result['subgroup_order']}")
print(f"陪集数 = {result['num_cosets']}")
print(f"Lagrange成立: {result['lagrange_holds']}")
print(f"陪集: {result['cosets']}")
```

### 4.2 输出结果

```text
|G| = 12
|H| = 4
陪集数 = 3
Lagrange成立: True
陪集: [{0, 3, 6, 9}, {1, 4, 7, 10}, {2, 5, 8, 11}]
```

### 4.3 对称群S₃的例子

```python
from itertools import permutations

def compose(p1, p2):
    """置换复合"""
    return tuple(p1[p2[i]] for i in range(len(p1)))

# S₃的元素
S3 = list(permutations([0, 1, 2]))
print(f"|S₃| = {len(S3)}")  # 6

# 子群 H = {e, (12)} ≅ ℤ/2ℤ
e = (0, 1, 2)
swap = (1, 0, 2)  # 交换0和1
H = {e, swap}
print(f"|H| = {len(H)}")  # 2

# 验证：6 = 2 × 3（3个陪集）
# 陪集分解确认Lagrange定理
```

---

## 五、范畴表征（抽象）

### 5.1 范畴论视角

**群的陪集分解对应于范畴论中的余核**：

```text
        [范畴论视角]
              │
    H ↪ G → G/H（商群/陪集空间）
              │
    这是"等化子"的对偶（余等化子）
              │
    G/H = coeq(H⇉G)
```

**商对象的万有性质**：

```text
如果 f: G → X 满足 f(gh) = f(g) ∀h∈H
则存在唯一 f̄: G/H → X 使得 f = f̄ ∘ π

    G ──f──→ X
    │       ↗
  π │     f̄
    ↓   ∕
   G/H
```

### 5.2 作为群胚的视角

```text
群G可以看作只有一个对象的群胚
子群H定义了一个等价关系
Lagrange定理说的是：

    |Ob(G/H)| = [G:H]
    |Aut(*)| = |H|

    |G| = |Ob(G/H)| × |Aut(*)|
```

### 5.3 推广：Lagrange定理的变体

| 推广 | 内容 |
|------|------|
| **无限群** | [G:H]可以无限 |
| **正规子群** | G/H是群（商群） |
| **群胚** | 对象数×自同构数 |
| **范畴** | 伴随函子的计数 |

---

## 六、推论与应用

### 6.1 重要推论

| 推论 | 内容 |
|------|------|
| 元素阶整除群阶 | \|⟨g⟩\| 整除 \|G\| |
| Fermat小定理 | aᵖ ≡ a (mod p) |
| Euler定理 | a^φ(n) ≡ 1 (mod n) |
| 素数阶群是循环的 | \|G\|=p ⟹ G ≅ ℤ/pℤ |

### 6.2 证明Fermat小定理

```text
设 p 是素数，a 不被 p 整除

考虑群 G = (ℤ/pℤ)* （非零元乘法群）
|G| = p-1

⟨a⟩ 是G的子群
由Lagrange定理：|⟨a⟩| 整除 p-1

设 |⟨a⟩| = d，则 aᵈ ≡ 1 (mod p)
由于 d | (p-1)，有 aᵖ⁻¹ ≡ 1 (mod p)
两边乘 a：aᵖ ≡ a (mod p) ∎
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **第一同构定理** | \|G/ker(φ)\| = \|Im(φ)\| |
| **Sylow定理** | p-子群的存在性 |
| **轨道-稳定子定理** | \|G\| = \|Orb(x)\| × \|Stab(x)\| |
| **Burnside引理** | 轨道计数 |

---

**最后更新**: 2025年12月1日
**状态**: ✅ 完成
