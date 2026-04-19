---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 02W1 - 平坦性判别（Criterion of Flatness）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 02W1 |
| **章节** | Chapter 10: Commutative Algebra, Section 10.99 |
| **类型** | 引理 (Lemma) |
| **重要性** | ★★★★★ (重要工具) |
| **位置** | Algebra, Section 10.99 |

## 2. 定理/定义原文

### 英文原文

**Algebra, Lemma 10.99.1 (Local criterion for flatness).** Let $R$ be a ring, $\mathfrak{m} \subset R$ an ideal, and $M$ an $R$-module. Assume that:
1. $R$ is Noetherian;
2. $\mathfrak{m}$ is nilpotent;
3. $M/\mathfrak{m}M$ is flat over $R/\mathfrak{m}$.

Then $M$ is flat over $R$.

**Algebra, Lemma 10.99.3 (Local criterion for flatness, stronger form).** Let $R$ be a ring, $\mathfrak{m} \subset R$ an ideal, and $M$ an $R$-module. Assume that:
1. $R$ is Noetherian;
2. $M$ is $\mathfrak{m}$-adically complete;
3. $M/\mathfrak{m}M$ is flat over $R/\mathfrak{m}$.

Then $M$ is flat over $R$.

### 中文翻译

**引理 10.99.1（平坦性局部判别法）.** 设 $R$ 是环，$\mathfrak{m} \subset R$ 是理想，$M$ 是 $R$-模。假设：
1. $R$ 是诺特的；
2. $\mathfrak{m}$ 是幂零的；
3. $M/\mathfrak{m}M$ 在 $R/\mathfrak{m}$ 上平坦。

则 $M$ 在 $R$ 上平坦。

**引理 10.99.3（平坦性局部判别法，更强形式）.** 设 $R$ 是环，$\mathfrak{m} \subset R$ 是理想，$M$ 是 $R$-模。假设：
1. $R$ 是诺特的；
2. $M$ 是 $\mathfrak{m}$-进完备的；
3. $M/\mathfrak{m}M$ 在 $R/\mathfrak{m}$ 上平坦。

则 $M$ 在 $R$ 上平坦。

## 3. 概念依赖图

```
                  平坦性判别 (Criterion of Flatness)
                           |
          +----------------+----------------+
          |                |                |
      幂零理想        m-进完备性       纤维平坦性
      (Nilpotent     (m-adic         (Fiber
       Ideal)        Completeness)    Flatness)
          |                |                |
          +----------------+----------------+
                           |
                  诺特环假设的关键作用
                           |
       +-------------------+-------------------+
       |                   |                   |
   完备化技巧          滤过方法           归纳论证
   (Completion       (Filtration       (Inductive
    Technique)       Method)           Argument)
```

**前置概念：**
- Tag 02V0: 平坦模的基本理论
- Tag 00IP: 诺特环（Noetherian Rings）
- Tag 00M8: 完备化（Completion）
- Tag 00IX: 幂零理想

**依赖此概念：**
- 形变理论（Deformation Theory）
- Hilbert概形的构造
- 局部上同调
- 形式概形理论

## 4. 证明概要

### 4.1 幂零情形（Lemma 10.99.1）

**证明策略：** 对 $n$ 进行归纳，其中 $\mathfrak{m}^n = 0$。

**关键步骤：**

**基例 ($n = 1$):** 若 $\mathfrak{m} = 0$，则 $R/\mathfrak{m} = R$，条件即 $M$ 平坦。

**归纳步骤：** 假设对 $\mathfrak{m}^{n-1}$ 成立。考虑正合序列：

$$0 \to \mathfrak{m}^{n-1}M \to M \to M/\mathfrak{m}^{n-1}M \to 0$$

由归纳假设，$M/\mathfrak{m}^{n-1}M$ 在 $R/\mathfrak{m}^{n-1}$ 上平坦，进而在 $R$ 上平坦（因为 $\mathfrak{m}^{n-1}$ 作用为0）。

需要证明 $\mathfrak{m}^{n-1}M$ 平坦，然后由正合序列得到 $M$ 平坦。

**关键引理：** $\mathfrak{m}^{n-1}M \cong \mathfrak{m}^{n-1} \otimes_R M/\mathfrak{m}M$ 作为 $R/\mathfrak{m}$-模，且这是平坦的因为 $M/\mathfrak{m}M$ 平坦。

### 4.2 完备情形（Lemma 10.99.3）

**证明思路：** 约化到幂零情形。

1. $M$ 是 $\mathfrak{m}$-进完备的：$M = \varprojlim M/\mathfrak{m}^n M$

2. 考虑 $M_n = M/\mathfrak{m}^n M$，对每个 $n$，由幂零情形知 $M_n$ 平坦

3. 证明：若所有 $M_n$ 平坦，则 $M$ 平坦

**技术性引理：** 对于诺特环 $R$ 和 $\mathfrak{m}$-进完备模 $M$，有：
$$\text{Tor}_i^R(N, M) = \varprojlim \text{Tor}_i^R(N, M_n)$$

### 4.3 应用判别法

**典型应用场景：**

设 $R$ 是局部环，$\mathfrak{m}$ 是极大理想，$k = R/\mathfrak{m}$ 是剩余域。

要验证 $M$ 平坦，只需验证：$M/\mathfrak{m}M$ 是 $k$-向量空间（自动平坦）！

**但这是不够的**——还需要完备性假设。

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `NoetherianRing` | 诺特环 | `IsNoetherianRing` ✓ |
| `IsNilpotent` | 幂零理想 | `IsNilpotent` ✓ |
| `AdicCompletion` | $\mathfrak{m}$-进完备 | `AdicCompletion` |
| `Module.Flat` | 平坦模 | `Module.Flat` ✓ |
| `TensorProduct` | 张量积 | `TensorProduct` ✓ |

**mathlib4对应代码：**
```lean
-- 平坦性局部判别法（计划形式化）
theorem local_criterion_flatness_nilpotent {R : Type*} [CommRing R] 
    [IsNoetherianRing R] (m : Ideal R) [h_nilpotent : IsNilpotent m]
    {M : Type*} [AddCommGroup M] [Module R M]
    (h_fiber : Module.Flat (R ⧸ m) (M ⧸ m • ⊤)) :
    Module.Flat R M := by
  -- 证明：归纳法
  sorry

-- 完备形式
theorem local_criterion_flatness_complete {R : Type*} [CommRing R]
    [IsNoetherianRing R] (m : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicallyComplete m M]
    (h_fiber : Module.Flat (R ⧸ m) (M ⧸ m • ⊤)) :
    Module.Flat R M := by
  -- 证明：完备化约化
  sorry
```

## 6. 应用与重要性

### 6.1 形变理论

平坦性判别法是形变理论的核心工具：

**问题：** 给定概形 $X_0$ 在域 $k$ 上，研究其在Artin局部环上的形变。

**应用：** 若 $A$ 是Artin局部环，$\mathfrak{m}$ 是极大理想，则 $A$ 上的平坦族由 $A/\mathfrak{m}$ 上的纤维决定。

**后果：** 形变函子可以用Schlessinger判别法研究。

### 6.2 Hilbert概形的构造

Grothendieck的Hilbert概形构造依赖平坦性判别法：

1. 在射影空间 $\mathbb{P}^n$ 中，Hilbert概形参数化闭子概形
2. 平坦性确保Hilbert多项式沿族常值
3. 判别法用于验证拟凝聚层的平坦性

### 6.3 完备化与忠实平坦性

**定理：** 设 $(R, \mathfrak{m})$ 是诺特局部环，则：
- $R \to \hat{R}$（完备化）是忠实平坦的

**证明：** 使用局部判别法验证平坦性，然后验证忠实性。

### 6.4 形式概形

形式概形的理论建立在完备化的基础上，平坦性判别法是验证形式概形间态射平坦性的关键。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Matsumura | Ch.8 | 平坦性与完备化 |
| Hartshorne | III.9 | 平坦态射的判别 |
| Schlessinger | 论文 | 形变理论 |
| Stacks | Tag 02V0 | 平坦模基础 |
| Stacks | Tag 00MB | 忠实平坦性 |

**Stacks Project交叉引用：**
- Tag 02V0: 平坦模
- Tag 00MB: 忠实平坦性
- Tag 00M8: 完备化
- Tag 0B91: 平坦性下降

## 8. Lean4形式化展望

### 8.1 形式化难点

1. **归纳构造的技术细节**
   - 需要仔细处理滤过结构
   - Tor函子的极限交换

2. **完备化的泛性质**
   - 需要形式化逆向极限与张量积的交换

3. **诺特条件的应用**
   - 有限性在证明中的关键作用

### 8.2 建议的形式化路线

```lean
-- 阶段1: 幂零情形的核心归纳
lemma flat_of_nilpotent_induction (n : ℕ) (hn : m ^ n = ⊥) :
    Module.Flat (R ⧸ m) (M ⧸ m • ⊤) → Module.Flat R M := by
  induction n with
  | zero => ...
  | succ n ih => ...

-- 阶段2: 完备化约化
theorem flat_of_complete (h_complete : IsAdicallyComplete m M) :
    (∀ n, Module.Flat (R ⧸ m ^ n) (M ⧸ m ^ n • ⊤)) → 
    Module.Flat R M := by
  -- 使用Tor函子的极限性质
  sorry

-- 阶段3: 主定理
theorem local_criterion_flatness [IsNoetherianRing R] 
    [IsAdicallyComplete m M] :
    Module.Flat (R ⧸ m) (M ⧸ m • ⊤) → Module.Flat R M := by
  intro h
  have : ∀ n, Module.Flat (R ⧸ m ^ n) (M ⧸ m ^ n • ⊤) := 
    flat_fiber_implies_flat_all_powers h
  exact flat_of_complete inferInstance this
```

### 8.3 应用形式化

```lean
-- 形变理论中的平坦性判定
structure Deformation (R : Type*) [CommRing R] (X₀ : Scheme) where
  scheme : Scheme
  base : Spec R
  morphism : scheme ⟶ Spec R
  fiber : SpecialFiber morphism ≅ X₀
  flat : IsFlat morphism

-- 用局部判别法验证平坦性
theorem deformation_flat_iff_fiber_flat {R : Type*} [CommRing R] 
    [IsLocalRing R] [IsNoetherianRing R] 
    (def : Deformation R X₀) :
    IsFlat def.morphism ↔ IsFlat (def.fiber.hom) := by
  apply local_criterion_flatness
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
