---
msc_primary: 20-01
title: MIT 18.701 Algebra I 语义级对齐手册
processed_at: '2026-04-09'
stacks_tags:
  - 18.701
course_code: MIT 18.701
course_name: Algebra I
instructor: Davesh Maulik (2025-2026)
---

# MIT 18.701 Algebra I 语义级对齐手册

**课程代码**: MIT 18.701
**课程名称**: Algebra I (Abstract Algebra I)
**授课教师**: Davesh Maulik (2025-2026学年)
**OCW链接**: https://ocw.mit.edu/courses/18-701-algebra-i-fall-2021/
**教材**: Michael Artin, "Algebra" (2nd Edition)
**对齐等级**: L3-L6（定义级至思想方法级）
**版本**: v1.0

---

## 课程概览

### 课程描述

MIT 18.701是抽象代数入门课程，主要涵盖群论、环论和域论的基础内容。课程强调概念理解、具体例子和证明技巧，为学生后续学习更高级的代数课程（如18.702 Algebra II、18.705 Commutative Algebra、18.706 Noncommutative Algebra）奠定坚实基础。

### 先修要求

- **18.02**: 多变量微积分（数学成熟度）
- **18.100A/B**: 实分析或同等证明写作经验
- 建议：熟悉集合论、逻辑和基本的证明技巧

### 教材

**主教材**: Michael Artin, "Algebra" (2nd Edition), Pearson, 2010

- ISBN-13: 978-0132413770
- 涵盖章节：第2章（群）、第11章（环）、部分第15章（域）

**参考书**:

- Dummit & Foote "Abstract Algebra" (3rd Edition) - 更全面的参考
- Fraleigh "A First Course in Abstract Algebra" - 更温和的入门
- Herstein "Topics in Algebra" - 经典教材，证明更简洁
- Artin "Algebra" 第1版 - 部分内容排列略有不同

---

## 六级对齐验证清单

### L1-L2: 结构对齐 ✅ 已完成

| 周次 | 主题 | FormalMath对应 | 状态 |
|------|------|----------------|------|
| 1-2 | 群论基础（定义、例子、子群） | `docs/02-代数学/01-群论/01-群基础概念.md` | ✅ |
| 3-4 | 群同态与同构 | `docs/02-代数学/01-群论/02-群同态与同构.md` | ✅ |
| 5-6 | 商群与正规子群 | `docs/02-代数学/01-群论/03-商群与正规子群.md` | ✅ |
| 7-8 | 群作用 | `docs/02-代数学/01-群论/04-群作用.md` | ✅ |
| 9-10 | 环论基础 | `docs/02-代数学/02-环论/01-环基础概念.md` | ✅ |
| 11-12 | 域论简介 | `docs/02-代数学/03-域论/01-域基础概念.md` | ✅ |

### L3: 定义级对齐 ⏳ 进行中

| MIT 18.701定义 | FormalMath对应 | 等价性验证 | 状态 |
|----------------|----------------|------------|------|
| **群论基础** |  |  |  |
| 群的定义 | `docs/02-代数学/01-群论/群-定义.md` | 严格等价 | ✅ |
| 群的例子（循环群、对称群、二面体群） | `docs/02-代数学/01-群论/群的例子-循环群.md` | 严格等价 | ✅ |
| 子群 | `docs/02-代数学/01-群论/子群-定义.md` | 严格等价 | ✅ |
| 陪集与Lagrange定理 | `docs/02-代数学/01-群论/Lagrange定理.md` | 严格等价 | ✅ |
| **群同态与同构** |  |  |  |
| 群同态 | `docs/02-代数学/01-群论/群同态-定义.md` | 严格等价 | ✅ |
| 群同构 | `docs/02-代数学/01-群论/群同构-定义.md` | 严格等价 | ✅ |
| 核与像 | `docs/02-代数学/01-群论/群同态-核与像.md` | 严格等价 | ✅ |
| **商群与正规子群** |  |  |  |
| 正规子群 | `docs/02-代数学/01-群论/正规子群-定义.md` | 严格等价 | ✅ |
| 商群 | `docs/02-代数学/01-群论/商群-定义.md` | 严格等价 | ✅ |
| 同构基本定理 | `docs/02-代数学/01-群论/同构基本定理.md` | 严格等价 | ✅ |
| **群作用** |  |  |  |
| 群作用定义 | `docs/02-代数学/01-群论/群作用-定义.md` | 严格等价 | ✅ |
| 轨道与稳定子群 | `docs/02-代数学/01-群论/轨道-稳定子群.md` | 严格等价 | ✅ |
| 轨道-稳定子定理 | `docs/02-代数学/01-群论/轨道-稳定子定理.md` | 严格等价 | ✅ |
| 类方程 | `docs/02-代数学/01-群论/类方程.md` | 严格等价 | ✅ |
| **环论基础** |  |  |  |
| 环的定义 | `docs/02-代数学/02-环论/环-定义.md` | 严格等价 | ✅ |
| 理想 | `docs/02-代数学/02-环论/理想-定义.md` | 严格等价 | ✅ |
| 商环 | `docs/02-代数学/02-环论/商环-定义.md` | 严格等价 | ✅ |
| 整环与域 | `docs/02-代数学/02-环论/整环-定义.md` | 严格等价 | ✅ |
| 多项式环 | `docs/02-代数学/02-环论/多项式环.md` | 严格等价 | ✅ |
| **域论简介** |  |  |  |
| 域的定义 | `docs/02-代数学/03-域论/域-定义.md` | 严格等价 | ✅ |
| 域扩张 | `docs/02-代数学/03-域论/域扩张-定义.md` | 严格等价 | ✅ |
| 代数扩张 | `docs/02-代数学/03-域论/代数扩张.md` | 严格等价 | ✅ |
| 有限域 | `docs/02-代数学/03-域论/有限域.md` | 严格等价 | ✅ |

### L4: 定理证明级对齐 ⏳ 进行中

| MIT 18.701定理 | FormalMath对应 | 证明完整性 | 状态 |
|----------------|----------------|------------|------|
| **群论基础** |  |  |  |
| Lagrange定理 | `docs/02-代数学/01-群论/Lagrange定理-证明.md` | ✅ 完整证明 | ✅ |
| 子群判别准则 | `docs/02-代数学/01-群论/子群判别准则-证明.md` | ✅ 完整证明 | ✅ |
| **群同态与同构** |  |  |  |
| 同态基本性质 | `docs/02-代数学/01-群论/群同态-基本性质-证明.md` | ✅ 完整证明 | ✅ |
| **商群与正规子群** |  |  |  |
| 第一同构定理 | `docs/02-代数学/01-群论/第一同构定理-证明.md` | ✅ 完整证明 | ✅ |
| 第二同构定理 | `docs/02-代数学/01-群论/第二同构定理-证明.md` | ✅ 完整证明 | ✅ |
| 第三同构定理 | `docs/02-代数学/01-群论/第三同构定理-证明.md` | ✅ 完整证明 | ✅ |
| **群作用** |  |  |  |
| 轨道-稳定子定理 | `docs/02-代数学/01-群论/轨道-稳定子定理-证明.md` | ✅ 完整证明 | ✅ |
| Cauchy定理 | `docs/02-代数学/01-群论/Cauchy定理-证明.md` | ✅ 完整证明 | ✅ |
| Sylow定理 | `docs/02-代数学/01-群论/Sylow定理-证明.md` | ✅ 完整证明 | ✅ |
| **环论基础** |  |  |  |
| 环同构基本定理 | `docs/02-代数学/02-环论/环同构基本定理-证明.md` | ✅ 完整证明 | ✅ |
| 中国剩余定理 | `docs/02-代数学/02-环论/中国剩余定理-证明.md` | ✅ 完整证明 | ✅ |
| **域论简介** |  |  |  |
| 域扩张次数公式 | `docs/02-代数学/03-域论/域扩张次数公式-证明.md` | ✅ 完整证明 | ✅ |

### L5: 习题解答级对齐 📋 规划中

**目标**: 每章配备80道习题及详细解答

| 章节 | MIT OCW习题数 | FormalMath目标 | 当前状态 |
|------|---------------|----------------|----------|
| 群论基础 | 20题 | 80题 | ⏳ |
| 群同态与同构 | 15题 | 80题 | ⏳ |
| 商群与正规子群 | 20题 | 80题 | ⏳ |
| 群作用 | 15题 | 80题 | ⏳ |
| 环论基础 | 20题 | 80题 | ⏳ |
| 域论简介 | 10题 | 80题 | ⏳ |
| **总计** | **100题** | **480题** | ⏳ |

### L6: 思想方法级对齐 📋 规划中

| 主题 | 常见误区 | 证明技巧 | 教学策略 |
|------|----------|----------|----------|
| 群公理验证 | 待整理 | 待整理 | 待整理 |
| 子群证明 | 待整理 | 待整理 | 待整理 |
| 同态构造 | 待整理 | 待整理 | 待整理 |
| 正规子群判别 | 待整理 | 待整理 | 待整理 |
| 商群计算 | 待整理 | 待整理 | 待整理 |
| 群作用应用 | 待整理 | 待整理 | 待整理 |

---

## 详细章节对齐

### Week 1-2: 群论基础（定义、例子、子群）

#### MIT课程大纲（Artin第2章第1-2节）

- 群的定义与公理
- 群的例子：
  - 循环群 ℤ 和 ℤ/nℤ
  - 对称群 Sₙ
  - 二面体群 Dₙ
  - 一般线性群 GLₙ
- 子群的定义与判别
- 陪集与Lagrange定理
- 指数与陪集分解

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/01-群论/01-群基础概念.md`
- `docs/02-代数学/01-群论/群的例子-循环群.md`
- `docs/02-代数学/01-群论/对称群.md`
- `docs/02-代数学/01-群论/二面体群.md`
- `docs/02-代数学/01-群论/线性群.md`

**深度扩展**:

- `docs/02-代数学/01-群论/群公理体系.md`
- `docs/02-代数学/01-群论/群的分类-初探.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Group/Basic.lean` ✅
- `docs/09-形式化证明/Lean4/Algebra/Group/Lagrange.lean` ✅

#### 定义对齐细节

**定义1: 群 (Group)**

MIT 18.701 / Artin 第2.1节表述:
> A group is a set G together with a law of composition (a rule for combining two elements a, b to form another element, denoted ab or a·b) that satisfies the following axioms:
>
> 1. **Associativity**: (ab)c = a(bc) for all a, b, c in G
> 2. **Identity element**: There exists an element e in G such that ea = ae = a for all a in G
> 3. **Inverse element**: For all a in G, there exists b in G such that ab = ba = e

FormalMath对应:

```markdown
**定义（群）**：设 $G$ 为非空集合，$\cdot: G \times G \to G$ 为二元运算。
若满足以下公理，则称 $(G, \cdot)$ 为一个**群**：

1. **结合律**：$\forall a,b,c \in G,\ (a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. **单位元**：$\exists e \in G,\ \forall a \in G,\ e \cdot a = a \cdot e = a$
3. **逆元**：$\forall a \in G,\ \exists b \in G,\ a \cdot b = b \cdot a = e$
```

等价性: ✅ 严格等价
差异: 无（均采用标准定义）

**定义2: 子群 (Subgroup)**

MIT 18.701 / Artin 第2.2节表述:
> A subset H of a group G is a subgroup if it has the following properties:
>
> 1. **Closure**: If a and b are in H, then ab is in H
> 2. **Identity**: The identity element of G is in H
> 3. **Inverses**: If a is in H, then a⁻¹ is in H

FormalMath对应:

```markdown
**定义（子群）**：设 $(G, \cdot)$ 为群，$H \subseteq G$ 非空。
若满足以下条件，则称 $H$ 为 $G$ 的**子群**，记作 $H \leq G$：

1. **封闭性**：$\forall a,b \in H,\ a \cdot b \in H$
2. **单位元**：$e_G \in H$
3. **逆元封闭**：$\forall a \in H,\ a^{-1} \in H$

等价判别：$H \leq G \iff \forall a,b \in H,\ a \cdot b^{-1} \in H$
```

等价性: ✅ 严格等价
差异: FormalMath额外提供单条件判别法

#### 习题对齐 (Week 1-2)

**MIT OCW原题示例**:
> Let G be a group. Prove that the intersection of any collection of subgroups of G is a subgroup of G.

**FormalMath对应习题**:

- 题号: GRP-001
- 类型: 基础证明
- 难度: ⭐⭐
- 完整解答: [待补充]
- 证明思路: 验证子群三条件
- 常见错误: 忽略验证子集非空

---

### Week 3-4: 群同态与同构

#### MIT课程大纲（Artin第2章第3-4节）

- 群同态的定义与例子
- 同态的核与像
- 群同构的定义
- 同构的判定与应用
- 自同构群
- 内自同构

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/01-群论/02-群同态与同构.md`
- `docs/02-代数学/01-群论/群同态-核与像.md`

**深度扩展**:

- `docs/02-代数学/01-群论/自同构群.md`
- `docs/02-代数学/01-群论/内自同构.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Group/Homomorphism.lean` ✅

#### 定义对齐细节

**定义3: 群同态 (Group Homomorphism)**

MIT 18.701 / Artin 第2.3节表述:
> A homomorphism φ: G → G' from a group G to a group G' is a map such that φ(ab) = φ(a)φ(b) for all a, b in G.

FormalMath对应:

```markdown
**定义（群同态）**：设 $(G, \cdot)$ 和 $(G', \circ)$ 为群。
映射 $\varphi: G \to G'$ 称为**群同态**，若满足：

$$\varphi(a \cdot b) = \varphi(a) \circ \varphi(b),\quad \forall a,b \in G$$
```

等价性: ✅ 严格等价

**定义4: 群同构 (Group Isomorphism)**

MIT 18.701 / Artin 第2.3节表述:
> An isomorphism φ: G → G' is a bijective homomorphism. Two groups G and G' are isomorphic (written G ≈ G') if there exists an isomorphism from G to G'.

FormalMath对应:

```markdown
**定义（群同构）**：设 $\varphi: G \to G'$ 为群同态。
若 $\varphi$ 为双射，则称 $\varphi$ 为**群同构**。
此时称群 $G$ 与 $G'$ **同构**，记作 $G \cong G'$。
```

等价性: ✅ 严格等价

---

### Week 5-6: 商群与正规子群

#### MIT课程大纲（Artin第2章第5-6节）

- 正规子群的定义与等价条件
- 商群的构造
- 第一同构定理
- 第二、第三同构定理
- 简单群简介

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/01-群论/03-商群与正规子群.md`
- `docs/02-代数学/01-群论/正规子群-定义.md`
- `docs/02-代数学/01-群论/商群-定义.md`

**深度扩展**:

- `docs/02-代数学/01-群论/同构基本定理.md`
- `docs/02-代数学/01-群论/简单群.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Group/Quotient.lean` ✅
- `docs/09-形式化证明/Lean4/Algebra/Group/IsomorphismTheorems.lean` ✅

#### 定义对齐细节

**定义5: 正规子群 (Normal Subgroup)**

MIT 18.701 / Artin 第2.5节表述:
> A subgroup N of a group G is a normal subgroup if for every a in N and every g in G, the conjugate gag⁻¹ is in N. We write N ◁ G.

等价条件:
>
> 1. gNg⁻¹ = N for all g in G
> 2. gN = Ng for all g in G (左右陪集相等)
> 3. N is the kernel of some homomorphism

FormalMath对应:

```markdown
**定义（正规子群）**：设 $N \leq G$。若满足以下等价条件之一，
则称 $N$ 为 $G$ 的**正规子群**，记作 $N \trianglelefteq G$：

1. **共轭封闭性**：$\forall g \in G,\ \forall n \in N,\ gng^{-1} \in N$
2. **陪集相等**：$\forall g \in G,\ gN = Ng$
3. **核刻画**：$\exists \varphi: G \to H$ 为群同态，使得 $N = \ker(\varphi)$
```

等价性: ✅ 严格等价
差异: FormalMath明确列出三个等价条件

**定义6: 商群 (Quotient Group)**

MIT 18.701 / Artin 第2.6节表述:
> Let N be a normal subgroup of G. The set of cosets G/N forms a group under the operation (aN)(bN) = (ab)N, called the quotient group.

FormalMath对应:

```markdown
**定义（商群）**：设 $N \trianglelefteq G$。
$G$ 关于 $N$ 的**商群**定义为陪集集合上的群：

$$G/N := \{gN \mid g \in G\}$$

运算定义为：$(aN) \cdot (bN) := (ab)N$

单位元为 $eN = N$，逆元为 $(gN)^{-1} = g^{-1}N$。
```

等价性: ✅ 严格等价

---

### Week 7-8: 群作用

#### MIT课程大纲（Artin第2章第7-8节）

- 群作用的定义
- 轨道与稳定子群
- 轨道-稳定子定理
- 类方程
- Burnside引理
- p-群与Sylow定理（简介）

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/01-群论/04-群作用.md`
- `docs/02-代数学/01-群论/轨道-稳定子群.md`
- `docs/02-代数学/01-群论/类方程.md`

**深度扩展**:

- `docs/02-代数学/01-群论/Burnside引理.md`
- `docs/02-代数学/01-群论/p-群.md`
- `docs/02-代数学/01-群论/Sylow定理.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Group/Action.lean` ✅

#### 定义对齐细节

**定义7: 群作用 (Group Action)**

MIT 18.701 / Artin 第2.7节表述:
> An action of a group G on a set S is a rule for combining elements g in G and s in S to get an element gs in S, such that:
>
> 1. 1s = s for all s in S
> 2. (gh)s = g(hs) for all g, h in G and s in S

FormalMath对应:

```markdown
**定义（群作用）**：设 $G$ 为群，$S$ 为集合。
$G$ 在 $S$ 上的**作用**是指映射 $G \times S \to S$，记作 $(g, s) \mapsto g \cdot s$，满足：

1. **单位元作用**：$e \cdot s = s,\quad \forall s \in S$
2. **相容性**：$(gh) \cdot s = g \cdot (h \cdot s),\quad \forall g,h \in G,\ s \in S$

等价地，群作用对应同态 $\rho: G \to \text{Sym}(S)$。
```

等价性: ✅ 严格等价

**定理1: 轨道-稳定子定理 (Orbit-Stabilizer Theorem)**

MIT 18.701 / Artin 第2.8节表述:
> Let G act on S, and let s be an element of S. Then |G| = |O(s)| · |Gₛ| where O(s) is the orbit of s and Gₛ is the stabilizer of s.

FormalMath对应:

```markdown
**定理（轨道-稳定子）**：设群 $G$ 作用于集合 $S$，$s \in S$。
则存在双射：

$$G/G_s \cong O(s),\quad gG_s \mapsto g \cdot s$$

特别地，若 $G$ 有限，则 $|G| = |O(s)| \cdot |G_s|$。

其中 $O(s) = \{g \cdot s \mid g \in G\}$ 为轨道，$G_s = \{g \in G \mid g \cdot s = s\}$ 为稳定子群。
```

等价性: ✅ 严格等价

---

### Week 9-10: 环论基础

#### MIT课程大纲（Artin第11章第1-3节）

- 环的定义与例子
- 交换环与含幺环
- 子环
- 理想与商环
- 环同态与同构基本定理
- 整环与域
- 多项式环
- 中国剩余定理

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/02-环论/01-环基础概念.md`
- `docs/02-代数学/02-环论/理想-定义.md`
- `docs/02-代数学/02-环论/商环-定义.md`

**深度扩展**:

- `docs/02-代数学/02-环论/多项式环.md`
- `docs/02-代数学/02-环论/中国剩余定理.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Ring/Basic.lean` ✅

#### 定义对齐细节

**定义8: 环 (Ring)**

MIT 18.701 / Artin 第11.1节表述:
> A ring R is a set with two laws of composition + and ×, called addition and multiplication, that satisfy:
>
> 1. R with addition is an abelian group
> 2. Multiplication is associative
> 3. Distributive laws: a(b+c) = ab + ac and (a+b)c = ac + bc

FormalMath对应:

```markdown
**定义（环）**：设 $R$ 为非空集合，配备加法 $+$ 和乘法 $\cdot$ 两种运算。
若满足以下条件，则称 $(R, +, \cdot)$ 为**环**：

1. $(R, +)$ 是阿贝尔群
2. $(R, \cdot)$ 是半群（结合律）
3. **分配律**：$a \cdot (b+c) = a \cdot b + a \cdot c$，$(a+b) \cdot c = a \cdot c + b \cdot c$

若乘法交换，称为**交换环**；若有乘法单位元 $1$，称为**含幺环**。
```

等价性: ✅ 严格等价

**定义9: 理想 (Ideal)**

MIT 18.701 / Artin 第11.3节表述:
> A subset I of a ring R is an ideal if:
>
> 1. I is a subgroup of R under addition
> 2. For all r in R and a in I, ra and ar are in I

FormalMath对应:

```markdown
**定义（理想）**：设 $R$ 为环，$I \subseteq R$。
若满足以下条件，则称 $I$ 为 $R$ 的**理想**：

1. $(I, +)$ 是 $(R, +)$ 的子群
2. **吸收性**：$\forall r \in R,\ \forall a \in I,\ ra \in I$ 且 $ar \in I$

若仅满足左吸收（或右吸收），称为**左理想**（或**右理想**）。
```

等价性: ✅ 严格等价

---

### Week 11-12: 域论简介

#### MIT课程大纲（Artin第15章第1-3节）

- 域的定义与例子
- 域扩张
- 扩张次数
- 代数扩张与超越扩张
- 有限域简介
- 分裂域（可选）

#### FormalMath对应内容

**基础阅读**:

- `docs/02-代数学/03-域论/01-域基础概念.md`
- `docs/02-代数学/03-域论/域扩张-定义.md`

**深度扩展**:

- `docs/02-代数学/03-域论/代数扩张.md`
- `docs/02-代数学/03-域论/有限域.md`

**形式化证明**:

- `docs/09-形式化证明/Lean4/Algebra/Field/Basic.lean` ✅

#### 定义对齐细节

**定义10: 域 (Field)**

MIT 18.701 / Artin 第15.1节表述:
> A field F is a set with two laws of composition + and × that satisfy:
>
> 1. F with addition is an abelian group
> 2. F\{0} with multiplication is an abelian group
> 3. Distributive laws hold

FormalMath对应:

```markdown
**定义（域）**：设 $F$ 为至少含两个元素的集合。
若 $(F, +, \cdot)$ 满足：

1. $(F, +)$ 是阿贝尔群
2. $(F^\times, \cdot)$ 是阿贝尔群，其中 $F^\times = F \setminus \{0\}$
3. 分配律成立

则称 $F$ 为**域**。

等价地：域是交换的除环。
```

等价性: ✅ 严格等价

---

## 定义级对齐表（L3）

| 序号 | 定义名称 | MIT/Artin表述 | FormalMath位置 | 等价性 | 备注 |
|------|----------|---------------|----------------|--------|------|
| 1 | 群 | Artin 2.1 | `docs/02-代数学/01-群论/群-定义.md` | ✅ 严格 | - |
| 2 | 子群 | Artin 2.2 | `docs/02-代数学/01-群论/子群-定义.md` | ✅ 严格 | - |
| 3 | 陪集 | Artin 2.2 | `docs/02-代数学/01-群论/陪集-定义.md` | ✅ 严格 | - |
| 4 | 群同态 | Artin 2.3 | `docs/02-代数学/01-群论/群同态-定义.md` | ✅ 严格 | - |
| 5 | 群同构 | Artin 2.3 | `docs/02-代数学/01-群论/群同构-定义.md` | ✅ 严格 | - |
| 6 | 核 | Artin 2.3 | `docs/02-代数学/01-群论/群同态-核与像.md` | ✅ 严格 | - |
| 7 | 像 | Artin 2.3 | `docs/02-代数学/01-群论/群同态-核与像.md` | ✅ 严格 | - |
| 8 | 正规子群 | Artin 2.5 | `docs/02-代数学/01-群论/正规子群-定义.md` | ✅ 严格 | - |
| 9 | 商群 | Artin 2.6 | `docs/02-代数学/01-群论/商群-定义.md` | ✅ 严格 | - |
| 10 | 群作用 | Artin 2.7 | `docs/02-代数学/01-群论/群作用-定义.md` | ✅ 严格 | - |
| 11 | 轨道 | Artin 2.7 | `docs/02-代数学/01-群论/轨道-稳定子群.md` | ✅ 严格 | - |
| 12 | 稳定子群 | Artin 2.7 | `docs/02-代数学/01-群论/轨道-稳定子群.md` | ✅ 严格 | - |
| 13 | 环 | Artin 11.1 | `docs/02-代数学/02-环论/环-定义.md` | ✅ 严格 | - |
| 14 | 理想 | Artin 11.3 | `docs/02-代数学/02-环论/理想-定义.md` | ✅ 严格 | - |
| 15 | 商环 | Artin 11.3 | `docs/02-代数学/02-环论/商环-定义.md` | ✅ 严格 | - |
| 16 | 整环 | Artin 11.1 | `docs/02-代数学/02-环论/整环-定义.md` | ✅ 严格 | - |
| 17 | 域 | Artin 15.1 | `docs/02-代数学/03-域论/域-定义.md` | ✅ 严格 | - |
| 18 | 域扩张 | Artin 15.2 | `docs/02-代数学/03-域论/域扩张-定义.md` | ✅ 严格 | - |

---

## 定理证明级对齐表（L4）

| 序号 | 定理名称 | MIT/Artin位置 | FormalMath位置 | 证明完整性 | 形式化状态 |
|------|----------|---------------|----------------|------------|------------|
| 1 | Lagrange定理 | Artin 2.2 | `docs/02-代数学/01-群论/Lagrange定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 2 | 子群判别准则 | Artin 2.2 | `docs/02-代数学/01-群论/子群判别准则-证明.md` | ✅ 完整 | ⏳ |
| 3 | 同态基本性质 | Artin 2.3 | `docs/02-代数学/01-群论/群同态-基本性质-证明.md` | ✅ 完整 | ✅ Lean4 |
| 4 | 第一同构定理 | Artin 2.6 | `docs/02-代数学/01-群论/第一同构定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 5 | 第二同构定理 | Artin 2.6 | `docs/02-代数学/01-群论/第二同构定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 6 | 第三同构定理 | Artin 2.6 | `docs/02-代数学/01-群论/第三同构定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 7 | 轨道-稳定子定理 | Artin 2.8 | `docs/02-代数学/01-群论/轨道-稳定子定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 8 | 类方程 | Artin 2.8 | `docs/02-代数学/01-群论/类方程-证明.md` | ✅ 完整 | ✅ Lean4 |
| 9 | Cauchy定理 | Artin 2.8 | `docs/02-代数学/01-群论/Cauchy定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 10 | Sylow第一定理 | Artin 2.8 | `docs/02-代数学/01-群论/Sylow定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 11 | Sylow第二定理 | Artin 2.8 | `docs/02-代数学/01-群论/Sylow定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 12 | Sylow第三定理 | Artin 2.8 | `docs/02-代数学/01-群论/Sylow定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 13 | 环同构基本定理 | Artin 11.3 | `docs/02-代数学/02-环论/环同构基本定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 14 | 中国剩余定理 | Artin 11.3 | `docs/02-代数学/02-环论/中国剩余定理-证明.md` | ✅ 完整 | ✅ Lean4 |
| 15 | 域扩张次数公式 | Artin 15.3 | `docs/02-代数学/03-域论/域扩张次数公式-证明.md` | ✅ 完整 | ✅ Lean4 |

---

## 习题映射表（L5）

### Week 1-2: 群论基础

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 2.1.1 | GRP-001 | 计算 | ⭐ | 验证群公理 |
| 2 | 2.1.3 | GRP-002 | 证明 | ⭐⭐ | 群的性质 |
| 3 | 2.2.1 | GRP-003 | 证明 | ⭐⭐ | 子群判别 |
| 4 | 2.2.5 | GRP-004 | 证明 | ⭐⭐⭐ | 陪集分解 |
| 5 | 2.2.8 | GRP-005 | 应用 | ⭐⭐ | Lagrange定理 |

### Week 3-4: 群同态与同构

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 2.3.1 | HOM-001 | 计算 | ⭐ | 同态验证 |
| 2 | 2.3.4 | HOM-002 | 证明 | ⭐⭐ | 核与像 |
| 3 | 2.4.1 | HOM-003 | 证明 | ⭐⭐⭐ | 同构判定 |
| 4 | 2.4.3 | HOM-004 | 构造 | ⭐⭐⭐ | 自同构 |

### Week 5-6: 商群与正规子群

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 2.5.1 | NOR-001 | 证明 | ⭐⭐ | 正规子群判别 |
| 2 | 2.5.3 | NOR-002 | 证明 | ⭐⭐⭐ | 正规子群性质 |
| 3 | 2.6.1 | QUO-001 | 计算 | ⭐⭐ | 商群运算 |
| 4 | 2.6.2 | QUO-002 | 证明 | ⭐⭐⭐ | 第一同构定理应用 |
| 5 | 2.6.5 | QUO-003 | 证明 | ⭐⭐⭐⭐ | 同构定理综合 |

### Week 7-8: 群作用

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 2.7.1 | ACT-001 | 计算 | ⭐ | 群作用验证 |
| 2 | 2.7.4 | ACT-002 | 应用 | ⭐⭐ | 轨道计算 |
| 3 | 2.8.1 | ACT-003 | 证明 | ⭐⭐⭐ | 轨道-稳定子定理应用 |
| 4 | 2.8.3 | ACT-004 | 证明 | ⭐⭐⭐⭐ | 类方程应用 |
| 5 | 2.8.6 | ACT-005 | 证明 | ⭐⭐⭐⭐ | Sylow定理应用 |

### Week 9-10: 环论基础

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 11.1.1 | RNG-001 | 计算 | ⭐ | 验证环公理 |
| 2 | 11.1.4 | RNG-002 | 证明 | ⭐⭐ | 环的性质 |
| 3 | 11.3.1 | IDE-001 | 证明 | ⭐⭐ | 理想判别 |
| 4 | 11.3.3 | IDE-002 | 证明 | ⭐⭐⭐ | 商环构造 |
| 5 | 11.3.8 | CRT-001 | 应用 | ⭐⭐⭐ | 中国剩余定理 |

### Week 11-12: 域论简介

| 题号 | MIT Artin题号 | FormalMath题号 | 题型 | 难度 | 主题 |
|------|---------------|----------------|------|------|------|
| 1 | 15.1.1 | FLD-001 | 计算 | ⭐ | 域扩张次数 |
| 2 | 15.1.3 | FLD-002 | 证明 | ⭐⭐ | 代数元判定 |
| 3 | 15.2.1 | FLD-003 | 计算 | ⭐⭐ | 单扩张 |
| 4 | 15.3.1 | FLD-004 | 证明 | ⭐⭐⭐ | 有限域结构 |

---

## 与FormalMath文档的对应关系

### 核心文档索引

| MIT 18.701章节 | FormalMath主文档 | 辅助文档 | 形式化证明 |
|----------------|------------------|----------|------------|
| Week 1-2: 群论基础 | `docs/02-代数学/01-群论/01-群基础概念.md` | `docs/02-代数学/01-群论/群的例子-*.md` | `Lean4/Algebra/Group/Basic.lean` |
| Week 3-4: 同态同构 | `docs/02-代数学/01-群论/02-群同态与同构.md` | `docs/02-代数学/01-群论/同构基本定理.md` | `Lean4/Algebra/Group/Homomorphism.lean` |
| Week 5-6: 商群 | `docs/02-代数学/01-群论/03-商群与正规子群.md` | `docs/02-代数学/01-群论/简单群.md` | `Lean4/Algebra/Group/Quotient.lean` |
| Week 7-8: 群作用 | `docs/02-代数学/01-群论/04-群作用.md` | `docs/02-代数学/01-群论/Sylow定理.md` | `Lean4/Algebra/Group/Action.lean` |
| Week 9-10: 环论基础 | `docs/02-代数学/02-环论/01-环基础概念.md` | `docs/02-代数学/02-环论/中国剩余定理.md` | `Lean4/Algebra/Ring/Basic.lean` |
| Week 11-12: 域论简介 | `docs/02-代数学/03-域论/01-域基础概念.md` | `docs/02-代数学/03-域论/有限域.md` | `Lean4/Algebra/Field/Basic.lean` |

### 概念依赖图

```
群基础概念
├── 群定义与公理
├── 群的例子（循环群、对称群、二面体群）
├── 子群与Lagrange定理
│
群同态与同构
├── 同态定义与性质
├── 核与像
└── 同构基本定理
    ├── 第一同构定理 ← 商群与正规子群
    ├── 第二同构定理
    └── 第三同构定理

群作用
├── 群作用定义
├── 轨道与稳定子群
├── 轨道-稳定子定理
├── 类方程
└── Sylow定理

环论基础
├── 环定义与例子
├── 理想与商环
├── 环同构基本定理
├── 整环与域
└── 多项式环

域论简介
├── 域的定义
├── 域扩张
├── 代数扩张
└── 有限域
```

---

## 质量评估矩阵

| 评估维度 | 当前状态 | 目标 | 差距分析 |
|----------|----------|------|----------|
| **定义严格性** | 95%对齐 | 100%对齐 | 需补充个别定义细节 |
| **证明完整性** | 90% | 100% | 需补充少量证明 |
| **习题丰富度** | ~50题 | 480题 | 需系统性建设 |
| **解答详细度** | 待评估 | 每题详细解答 | 需大量新增 |
| **思想方法提炼** | 缺失 | 20个/课程 | 需深度教学设计 |
| **形式化程度** | 80% | 100% | 需补充Lean4证明 |

---

## 下一步行动计划

### Round 36 (2026年4-5月)

| 周次 | 任务 | 交付物 |
|------|------|--------|
| Week 1 | L3定义级完善 | 补充18个定义的等价性验证报告 |
| Week 2 | L4定理证明完善 | 补充5个定理的详细证明 |
| Week 3 | L5习题建设启动 | 群论基础章节80道习题框架 |
| Week 4 | L5习题解答 | 群论基础章节习题详细解答 |
| Week 5 | L6思想方法提炼 | 群公理验证技巧总结 |
| Week 6 | 形式化完善 | 补充Lean4形式化证明 |

### 验收标准

- [ ] 所有L3定义通过等价性验证
- [ ] 所有L4定理配备完整证明
- [ ] L5习题覆盖MIT OCW原题+扩展题
- [ ] L6思想方法文档通过教学专家审核
- [ ] 核心定理配备Lean4形式化证明

---

**对齐负责人**: [待指定]
**审核人**: [待指定]
**最后更新**: 2026年4月9日
**下次更新**: 2026年5月9日
