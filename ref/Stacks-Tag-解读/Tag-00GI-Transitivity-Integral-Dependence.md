# Stacks Project Tag 00GI - 整依赖的传递性

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00GI |
| **章节** | Chapter 10: Commutative Algebra, Section 10.36: Finite and integral ring extensions |
| **类型** | 引理 (Lemma) |
| **重要性** | ★★★★★ (核心性质) |
| **位置** | Algebra, Lemma 10.36.6 |

## 2. 定理/定义原文

### 英文原文

**Lemma 10.36.6.** Suppose that $R \to S$ and $S \to T$ are integral ring maps. Then $R \to T$ is integral.

### 中文翻译

**引理 10.36.6.** 假设 $R \to S$ 和 $S \to T$ 都是整环映射。则 $R \to T$ 也是整的。

## 3. 概念依赖图

```
                    整依赖的传递性
                   (Transitivity of 
                    Integral Dependence)
                           |
          +----------------+----------------+
          |                |                |
      R → S            S → T            R → T
     (Integral)      (Integral)       (Integral)
          |                |                |
          +----------------+----------------+
                           |
                复合映射的整性证明
                           |
          +----------------+----------------+
          |                |                |
    有限生成模        多项式方程         张量积技巧
   (Finitely Gen)   (Polynomial Eq)   (Tensor Product)
```

**前置依赖：**
- Tag 00GH: 整依赖的定义
- Tag 00GE: Cayley-Hamilton定理
- Tag 00G8: 有限扩张的性质

**被依赖：**
- Tag 00GK: 整闭包的性质
- Tag 00GP: 整扩张的谱映射
- Tag 01W7: 固有态射

## 4. 证明概要

### 4.1 完整证明

**证明.** (详细版本)

设 $t \in T$。我们的目标是证明 $t$ 在 $R$ 上整。

**步骤1：在 $S$ 上建立整性方程**

由于 $S \to T$ 是整的，存在首一多项式 $P(x) \in S[x]$ 使得 $P(t) = 0$。

设 $P(x) = x^d + a_{d-1}x^{d-1} + \cdots + a_1 x + a_0$，其中 $a_i \in S$。

**步骤2：系数在 $R$ 上的有限扩张中**

由引理 10.36.4，系数 $a_0, a_1, \ldots, a_{d-1}$ 都在某个有限 $R$-子代数 $S' \subset S$ 中。

由于每个 $a_i$ 都在 $R$ 上整，由引理 10.36.4，存在有限扩张 $R \to S'$ 包含所有系数。

**步骤3：构造有限中间代数**

考虑 $t$ 在 $S'$ 上整，因此存在有限扩张 $S' \to T'$ 使得 $t \in T'$。

由引理 10.7.3（有限扩张的传递性），$R \to S' \to T'$ 的复合给出 $R \to T'$ 是有限扩张。

**步骤4：应用有限性判别**

由于 $t \in T'$ 且 $R \to T'$ 是有限扩张，由引理 10.36.3，$t$ 在 $R$ 上整。

$\square$

### 4.2 关键步骤说明

| 步骤 | 关键引理 | 作用 |
|------|---------|------|
| 1 | 整的定义 | 建立初始方程 |
| 2 | Lemma 10.36.4 | 系数的有限性 |
| 3 | Lemma 10.7.3 | 有限扩张的传递性 |
| 4 | Lemma 10.36.3 | 有限⇒整 |

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 备注 |
|----------------|---------|------|
| `IsIntegral` | $t$ 在 $R$ 上整 | 核心概念 |
| `Subalgebra.Finite` | 有限子代数 | 构造关键 |
| `Algebra.Trans` | 传递性 | 一般代数结构 |
| `Polynomial.Monic` | 首一多项式 | 整性判别 |

**mathlib4对应：**
```lean
-- 整扩张传递性的形式化
lemma isIntegral_trans [Algebra.IsIntegral R S] [Algebra.IsIntegral S T] :
    Algebra.IsIntegral R T := by
  -- 证明结构与上述证明对应
  intro t
  -- ... 详细证明
```

## 6. 应用与重要性

### 6.1 理论意义

1. **范畴论视角**
   - 整扩张构成一个子范畴
   - 与有限扩张的关系：有限 = 整 + 有限型

2. **代数几何对应**
   - 有限态射的复合仍是有限的
   - 固有态射的复合仍是固有的

### 6.2 实际应用

**例1：域扩张的代数闭包**

若 $K \subseteq L \subseteq M$ 是域扩张，$L/K$ 和 $M/L$ 都是代数的，则 $M/K$ 也是代数的。

**例2：整闭包的塔性质**

对于 $R \subseteq S \subseteq T$，整闭包的计算可以分层进行。

### 6.3 与有限扩张的关系

```
                    整扩张 (Integral)
                          |
           +--------------+--------------+
           |                             |
      有限扩张                        无限整扩张
      (Finite)                     (如：代数闭包)
           |
    整 + 有限型
```

## 7. 与其他资源的关联

| 资源 | 相关章节 | 关联内容 |
|------|---------|---------|
| Stacks | Tag 00GH | 整依赖定义 |
| Stacks | Tag 00G8 | 有限扩张 |
| Stacks | Tag 00GK | 整闭包 |
| Hartshorne | II.3 | 有限态射 |
| Atiyah-Macdonald | Ch.5 | 整扩张理论 |

**延伸阅读：**
- Tag 00GL: 整闭包的局部化
- Tag 00GO: 整扩张的纤维性质
- Tag 00GR: Cohen-Seidenberg定理

## 8. Lean4形式化展望

### 8.1 形式化策略

传递性的形式化需要处理以下技术细节：

```lean
-- 技术挑战1: 系数环的嵌套
example (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    Algebra.IsIntegral R S → Algebra.IsIntegral S T → 
    Algebra.IsIntegral R T := sorry

-- 技术挑战2: 多项式环的提升
-- S[x] 到 T 的关系需要仔细处理标量塔结构
```

### 8.2 建议的API设计

```lean
namespace Algebra.IsIntegral

/-- 整扩张的传递性 -/
theorem trans {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (hRS : IsIntegral R S) (hST : IsIntegral S T) : IsIntegral R T := by
  -- 实现
  
/-- 整元素的传递性 -/
theorem isIntegral_trans {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (hRS : ∀ s : S, IsIntegral R s) (hST : ∀ t : T, IsIntegral S t)
    (t : T) : IsIntegral R t := by
  -- 实现

end Algebra.IsIntegral
```

### 8.3 证明自动化展望

```lean
-- 目标：自动证明链式整依赖
macro "integral_chain" : tactic =>
  `(tactic| repeat (apply isIntegral_trans <;> intro))

-- 使用示例
example : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  integral_chain -- 自动处理传递性
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
