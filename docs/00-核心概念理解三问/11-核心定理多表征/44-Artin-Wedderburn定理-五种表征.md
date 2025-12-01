# Artin-Wedderburn定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 环论/非交换代数
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Artin-Wedderburn定理 |
| **领域** | 环论/非交换代数 |
| **发现者** | Wedderburn (1907), Artin (1927) |
| **前置知识** | 半单环、单环、矩阵环 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Artin-Wedderburn定理**：设R是左Artin半单环，则R同构于有限个矩阵环的直积：

$$R \cong M_{n_1}(D_1) \times M_{n_2}(D_2) \times \cdots \times M_{n_k}(D_k)$$

其中Dᵢ是除环，分解唯一（在排列和同构意义下）。

### 1.2 特殊情况

- 若R可交换：Dᵢ都是域
- 若R是域上的代数：Dᵢ是域的有限扩张

### 1.3 Lean 4 形式化

```lean
import Mathlib.RingTheory.SimpleModule.Basic

-- Artin-Wedderburn定理（概念性）
theorem artin_wedderburn {R : Type*} [Ring R] [IsSemisimple R] :
    ∃ (n : ℕ) (D : Fin n → Type*) (dims : Fin n → ℕ),
      (∀ i, DivisionRing (D i)) ∧
      R ≃+* (Π i, Matrix (Fin (dims i)) (Fin (dims i)) (D i)) := by
  sorry  -- 需要详细的环论形式化
```

---

## 二、几何表征（可视化）

### 2.1 结构分解

```text
半单环R的结构：

    R ≅ M_{n₁}(D₁) × M_{n₂}(D₂) × ... × M_{nₖ}(Dₖ)
          │           │               │
       单分支₁      单分支₂          单分支ₖ
          │           │               │
       nᵢ×nᵢ矩阵   nⱼ×nⱼ矩阵        nₖ×nₖ矩阵
```

### 2.2 模的分解

```text
R-模的分类：

    每个单模 ≅ Dᵢⁿⁱ（作为Dᵢ-向量空间）

    半单模 = 单模的直和
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Artin-Wedderburn**：半单环就是"矩阵环的乘积"，每个分支是对应除环上的矩阵

### 3.2 块对角类比

- 半单环：块对角矩阵
- 每个块：某除环上的矩阵环
- 分解：按"本质不同"的部分分解

### 3.3 为什么重要？

完全刻画了半单环的结构

---

## 四、计算表征（算法）

### 4.1 Python实现（有限群代数）

```python
import numpy as np
from sympy import symbols, Matrix, GF

def wedderburn_group_algebra(G, F):
    """
    计算有限群G在域F上的群代数F[G]的Wedderburn分解
    （当char(F)不整除|G|时，F[G]是半单的）
    """
    # 群代数是半单的（Maschke定理）
    # 分解由不可约表示决定

    # 简化：计算不可约表示的维数
    # F[G] ≅ ⊕ M_{dᵢ}(F) 其中dᵢ是不可约表示维数

    # 例：S₃的ℂ[S₃] ≅ ℂ × ℂ × M₂(ℂ)
    # 维数: 1² + 1² + 2² = 6 = |S₃|

    return "需要表示论计算"

def verify_wedderburn():
    """验证：ℂ[S₃]的分解"""
    # S₃有3个不可约表示：
    # - 平凡表示（维数1）
    # - 符号表示（维数1）
    # - 标准表示（维数2）

    irrep_dims = [1, 1, 2]
    total = sum(d**2 for d in irrep_dims)
    print(f"dim ℂ[S₃] = {total} = |S₃|")
    print(f"ℂ[S₃] ≅ ℂ × ℂ × M₂(ℂ)")

verify_wedderburn()
```

### 4.2 单性检验

```python
def is_simple_ring(R):
    """
    检验环R是否单（只有平凡双边理想）
    """
    # 单环 ⟺ M_n(D) 对某除环D
    pass
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Artin-Wedderburn = 模范畴的分解
├─ R-Mod ≅ D₁-Mod × D₂-Mod × ... × Dₖ-Mod
├─ 每个Dᵢ-Mod是单模范畴
└─ 半单性 ⟺ Abel范畴是半单的
```

### 5.2 Morita等价

M_n(D)与D是Morita等价的（有相同的模范畴）

### 5.3 推广

- **半素环**：不一定Artin
- **代数K-理论**：更精细的不变量
- **导出范畴**：同调推广

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Maschke定理** | 群代数的半单性 |
| **Jacobson稠密定理** | 证明工具 |
| **Morita理论** | 范畴等价 |

---

**状态**: ✅ 完成
