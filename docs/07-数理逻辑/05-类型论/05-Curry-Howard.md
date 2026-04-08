---
title: Curry-Howard同构 (Curry-Howard Isomorphism)
msc_primary: 03B35
msc_secondary:
- 03B15
- 68N18
- 68Q60
processed_at: '2026-04-08'
---

# Curry-Howard同构 / Curry-Howard Isomorphism

> **前置知识**: [05-类型论/01-基础概念](01-基础概念.md)、[05-类型论/04-依赖类型](04-依赖类型.md)  
> **难度**: 进阶  
> **目标**: 深入理解"证明即程序，命题即类型"的深刻对应

---

## 🗺️ 概念思维导图

```mermaid
mindmap
  root((Curry-Howard同构))
    基础对应
      命题即类型
        真 ↔ 单元类型
        假 ↔ 空类型
        合取 ↔ 积类型
        析取 ↔ 和类型
        蕴含 ↔ 函数类型
      证明即程序
        证明项
        正规化
        可计算性
    量词对应
      全称量词
        ∀x:A.P(x) ↔ (x:A)→P(x)
        依赖函数
      存在量词
        ∃x:A.P(x) ↔ Σ(x:A).P(x)
        依赖对
    证明策略
      构造性证明
        存在性提取
        见证计算
      经典逻辑
        双重否定
        连续性
    应用
      程序提取
        Coq提取
        正确性保证
      证明辅助
        Lean策略
        类型推导
```

---

## 📊 知识矩阵

| 逻辑概念 | 类型概念 | 编程概念 | 典型应用 |
|---------|---------|---------|---------|
| 命题 | 类型 | 规格/契约 | 形式化规范 |
| 证明 | 项/程序 | 实现 | 验证代码 |
| 蕴含P→Q | 函数类型P→Q | 函数 | 转换器 |
| 合取P∧Q | 积类型P×Q | 对/记录 | 数据结构 |
| 析取P∨Q | 和类型P+Q | 变体/枚举 | 错误处理 |
| 假⊥ | 空类型Void | 永不返回 | 异常 |
| ∀x.P(x) | 依赖类型Π | 泛型 | 多态函数 |
| ∃x.P(x) | 依赖和Σ | 存在包装 | 信息隐藏 |

---

## 一、基础对应关系

### 1.1 命题逻辑与简单类型

**Curry-Howard同构**建立了直觉命题逻辑与简单类型λ演算之间的对应：

| 逻辑 | 类型 | 编程 | 记法 |
|------|------|------|------|
| 真 (T) | 单元类型 | unit | 1 或 Unit |
| 假 (⊥) | 空类型 | void | 0 或 Void |
| 合取 (P ∧ Q) | 积类型 | pair | P × Q |
| 析取 (P ∨ Q) | 和类型 | either | P + Q |
| 蕴含 (P → Q) | 函数类型 | function | P → Q |
| 否定 (¬P) | 否定类型 | continuation | P → 0 |

**核心洞察**:
- **类型 = 命题**: 一个类型对应一个逻辑命题
- **项 = 证明**: 该类型的一个 inhabitant 对应命题的一个证明
- **归约 = 证明简化**: β归约对应证明的正规化

### 1.2 证明构造即程序编写

**合取 (∧) 的引入**:

```
  Γ ⊢ t : P    Γ ⊢ u : Q
  ---------------------- (∧I)
     Γ ⊢ ⟨t, u⟩ : P ∧ Q
```

对应于构造对(pair)：

```haskell
-- 逻辑: P ∧ Q
-- 类型: (P, Q)
pair :: P -> Q -> (P, Q)
pair p q = (p, q)
```

**蕴含 (→) 的引入**:

```
  Γ, x : P ⊢ t : Q
  ----------------- (→I)
   Γ ⊢ λx.t : P → Q
```

对应于λ抽象：

```haskell
-- 逻辑: P → Q
-- 类型: P -> Q
implies :: (P -> Q) -> P -> Q
implies f p = f p
```

### 1.3 自然演绎规则的 Curry-Howard 解释

| 规则 | 逻辑形式 | 类型形式 | 编程意义 |
|------|---------|---------|---------|
| ∧I | $P \quad Q \over P \land Q$ | $t: P \quad u: Q \over \langle t, u \rangle : P \times Q$ | 构造对 |
| ∧E₁ | $P \land Q \over P$ | $\langle t, u \rangle : P \times Q \over \pi_1(t) : P$ | 取第一个分量 |
| ∧E₂ | $P \land Q \over Q$ | $\langle t, u \rangle : P \times Q \over \pi_2(t) : Q$ | 取第二个分量 |
| ∨I₁ | $P \over P \lor Q$ | $t : P \over \text{inl}(t) : P + Q$ | 左注入 |
| ∨I₂ | $Q \over P \lor Q$ | $u : Q \over \text{inr}(u) : P + Q$ | 右注入 |
| ∨E | ${P \lor Q \quad [P] \cdots R \quad [Q] \cdots R \over R}$ | ${t : P + Q \quad \lambda x.s : P \to R \quad \lambda y.u : Q \to R \over \text{case}(t, \lambda x.s, \lambda y.u) : R}$ | 模式匹配 |
| →I | ${[P] \cdots Q \over P \to Q}$ | ${x : P \vdash t : Q \over \lambda x.t : P \to Q}$ | λ抽象 |
| →E | ${P \to Q \quad P \over Q}$ | ${f : P \to Q \quad t : P \over f(t) : Q}$ | 函数应用 |

---

## 二、量词与依赖类型

### 2.1 全称量词 (∀)

**逻辑**: $\forall x : A. P(x)$

**类型**: 依赖函数类型 $\Pi(x : A). P(x)$ 或 $(x : A) \to P(x)$

**直观**: 一个证明是一个函数，对每个$x : A$给出$P(x)$的证明

**例子**:

```lean
-- 逻辑: ∀n:Nat. n + 0 = n
-- 类型: (n : Nat) → n + 0 = n
-- 证明: λn. reflexivity (n + 0)

def add_zero_right : (n : Nat) → n + 0 = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (add_zero_right n)
```

### 2.2 存在量词 (∃)

**逻辑**: $\exists x : A. P(x)$

**类型**: 依赖对类型 $\Sigma(x : A). P(x)$ 或 $(x : A) \times P(x)$

**直观**: 一个证明是一对⟨见证, 该见证满足性质的证明⟩

**例子**:

```lean
-- 逻辑: ∃n:Nat. n > 10 ∧ n < 20
-- 类型: Σ(n:Nat). (n > 10) × (n < 20)
-- 证明: ⟨15, ⟨proof_15_gt_10, proof_15_lt_20⟩⟩

def exists_between : Σ(n:Nat), (n > 10) × (n < 20) :=
  ⟨15, by constructor <;> norm_num⟩
```

### 2.3 依赖类型对应表

| 逻辑概念 | 类型概念 | 记法 | 示例 |
|---------|---------|------|------|
| 全称量词 | 依赖函数 | $\Pi(x:A).B(x)$ | 向量长度保持 |
| 存在量词 | 依赖对 | $\Sigma(x:A).B(x)$ | 提取见证 |
| 等式 | 恒等类型 | $a =_A b$ | 重写/替换 |
| 合取 | 积类型 | $A \times B$ | 记录/结构体 |
| 析取 | 和类型 | $A + B$ | 变体/枚举 |

---

## 三、构造性数学与程序提取

### 3.1 构造性存在性

**经典逻辑**: $\exists x. P(x)$ 可能不提供如何找到$x$

**构造性逻辑**: $\exists x. P(x)$ 的证明必须包含：
1. 具体的见证$x$
2. $P(x)$成立的证明

**程序提取**: 从证明中自动提取计算内容

```coq
(* Coq中的程序提取示例 *)
Theorem sqrt_2_irrational : ~ exists p q : nat, p * p = 2 * q * q.
Proof.
  (* 构造性证明，可以提取计算内容 *)
Qed.

(* 提取为OCaml代码 *)
Extraction sqrt_2_irrational.
```

### 3.2 选择原理与计算

**选择原理 (Axiom of Choice)**:

$$\forall x. \exists y. P(x, y) \rightarrow \exists f. \forall x. P(x, f(x))$$

**类型论版本**:

```lean
-- AC对应于从证明构造函数
axiom choice {A : Type} {B : A → Type} :
  ((x : A) → Σ(y : B x), P x y) → (Σ(f : (x : A) → B x), (x : A) → P x (f x))
```

**注意**: AC在类型论中是可证明的（作为定理），因为存在性已经是构造性的。

### 3.3 从证明到算法的提取

**排序算法提取示例**:

```coq
(* 证明: 每个列表都可以排序 *)
Theorem sort_exists : forall l : list nat, exists l', sorted l' /\ Permutation l l'.
Proof.
  (* 构造性证明，使用归并排序 *)
Qed.

(* 提取为可执行代码 *)
Extraction sort_exists.
(* 生成归并排序的OCaml实现 *)
```

---

## 四、经典逻辑与双重否定

### 4.1 双重否定翻译

经典逻辑可以通过双重否定翻译嵌入直觉逻辑：

| 经典逻辑 | 直觉逻辑翻译 |
|---------|-------------|
| $P$ (原子) | $\neg\neg P$ |
| $A \land B$ | $\neg\neg A \land \neg\neg B$ |
| $A \lor B$ | $\neg(\neg A \land \neg B)$ |
| $A \rightarrow B$ | $\neg\neg A \rightarrow \neg\neg B$ |
| $\forall x. A$ | $\forall x. \neg\neg A$ |
| $\exists x. A$ | $\neg\forall x. \neg A$ |

### 4.2 连续性 (Continuation)

**否定**: $\neg A = A \rightarrow \bot$ (A蕴含假)

**类型论**: 对应于**连续性** (continuation)：

```haskell
-- ¬A 对应于 Cont r a = (a -> r) -> r
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

-- 双重否定消除 (call/cc)
callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
```

### 4.3 Peirce定律与call/cc

**Peirce定律**: $((A \rightarrow B) \rightarrow A) \rightarrow A$

对应于**call-with-current-continuation**：

```haskell
peirce :: ((a -> b) -> a) -> a
peirce f = callCC (\k -> f (\x -> k x))
```

这表明经典逻辑对应于带控制操作符的编程语言。

---

## 五、形式化实现

### 5.1 Lean 4: 基本Curry-Howard

```lean
-- 逻辑与类型的对应

-- 真 ↔ Unit
def True_as_Type := Unit

-- 证明Unit是 inhabited
def true_proof : True_as_Type := ()

-- 假 ↔ Empty
def False_as_Type := Empty

-- 没有Empty的inhabitant (由定义)

-- 合取 ↔ 积
def And_as_Type (P Q : Type) := P × Q

def and_intro {P Q : Type} (p : P) (q : Q) : P × Q :=
  (p, q)

def and_elim_left {P Q : Type} (pq : P × Q) : P :=
  pq.1

def and_elim_right {P Q : Type} (pq : P × Q) : Q :=
  pq.2

-- 析取 ↔ 和
def Or_as_Type (P Q : Type) := Sum P Q

def or_intro_left {P Q : Type} (p : P) : Sum P Q :=
  Sum.inl p

def or_intro_right {P Q : Type} (q : Q) : Sum P Q :=
  Sum.inr q

def or_elim {P Q R : Type} (pq : Sum P Q) 
    (f : P → R) (g : Q → R) : R :=
  match pq with
  | Sum.inl p => f p
  | Sum.inr q => g q

-- 蕴含 ↔ 函数
def Implies_as_Type (P Q : Type) := P → Q

def implies_intro {P Q : Type} (f : P → Q) : P → Q :=
  f

def implies_elim {P Q : Type} (f : P → Q) (p : P) : Q :=
  f p

-- 否定 ↔ 到Void的函数
def Not_as_Type (P : Type) := P → Empty

def not_intro {P : Type} (f : P → Empty) : P → Empty :=
  f

def not_elim {P : Type} (np : P → Empty) (p : P) : Empty :=
  np p

-- 排中律不成立 (在直觉逻辑中)
-- 不存在 P + (P → Empty) 的通用构造
```

### 5.2 依赖类型与量词

```lean
-- 全称量词 ↔ 依赖函数
def Forall_as_Type {A : Type} (P : A → Type) :=
  (x : A) → P x

def forall_intro {A : Type} {P : A → Type} 
    (f : (x : A) → P x) : (x : A) → P x :=
  f

def forall_elim {A : Type} {P : A → Type} 
    (f : (x : A) → P x) (a : A) : P a :=
  f a

-- 存在量词 ↔ 依赖对
def Exists_as_Type {A : Type} (P : A → Type) :=
  Σ(x : A), P x

def exists_intro {A : Type} {P : A → Type} 
    (a : A) (pa : P a) : Σ(x : A), P x :=
  ⟨a, pa⟩

def exists_elim {A : Type} {P : A → Type} {Q : Type}
    (e : Σ(x : A), P x) (f : (a : A) → P a → Q) : Q :=
  match e with
  | ⟨a, pa⟩ => f a pa

-- 示例: 证明存在性并提取见证
example : Σ(n : Nat), n * n = 16 :=
  ⟨4, by norm_num⟩

-- 从证明中提取见证
def witness : Nat :=
  (⟨4, by norm_num⟩ : Σ(n : Nat), n * n = 16).fst

#eval witness  -- 输出: 4
```

### 5.3 程序验证应用

```lean
-- 验证的排序函数

def isSorted (l : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l.get! i ≤ l.get! j

def isPermutation (l₁ l₂ : List Nat) : Prop :=
  l₁ ~ l₂  -- Lean的排列关系

-- 规范: 排序返回排序后的列表且是原列表的排列
structure Sorted (l : List Nat) where
  result : List Nat
  sorted : isSorted result
  perm : isPermutation result l

-- 实现并验证插入排序
partial def insertSort (l : List Nat) : Sorted l :=
  match l with
  | [] => ⟨[], by simp [isSorted], by simp⟩
  | x :: xs =>
    let sorted_xs := insertSort xs
    let inserted := insert x sorted_xs.result
    ⟨inserted, by 
      -- 证明: 插入后仍有序
      simp [isSorted] at *
      sorry  -- 完整证明需要辅助引理
    , by
      -- 证明: 插入后是排列
      simp [isPermutation] at *
      sorry
    ⟩
where
  insert (x : Nat) (l : List Nat) : List Nat :=
    match l with
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys
```

---

## 六、习题与解答

### 习题 1: 证明项构造

**题目**: 在简单类型λ演算中构造以下命题的证明项：$(P \land Q) \rightarrow (Q \land P)$

**解答**:

```lean
-- 类型: (P × Q) → (Q × P)
def swap {P Q : Type} : P × Q → Q × P :=
  λp => (p.2, p.1)

-- 对应于证明:
-- 假设 p : P ∧ Q
-- 需要证明 Q ∧ P
-- 由p得p.1 : P和p.2 : Q
-- 构造(p.2, p.1) : Q × P
```

---

### 习题 2: 存在量词提取

**题目**: 给定证明 $\exists x : \mathbb{N}. x^2 = 25$，提取具体的见证。

**解答**:

```lean
-- 存在性证明
def proof_exists_sqrt_25 : Σ(x : Nat), x * x = 25 :=
  ⟨5, by norm_num⟩

-- 提取见证
def sqrt_25 : Nat := proof_exists_sqrt_25.fst

#eval sqrt_25  -- 5

-- 或者使用5本身
example : Σ(x : Nat), x * x = 25 :=
  ⟨5, rfl⟩  -- 5是25的平方根
```

---

### 习题 3: 经典逻辑到直觉逻辑

**题目**: 使用双重否定翻译证明排中律在经典逻辑中等价于$\neg\neg P \rightarrow P$

**解答**:

```lean
-- 排中律
axiom LEM (P : Prop) : P ∨ ¬P

-- 双重否定消除
axiom DNE (P : Prop) : ¬¬P → P

-- LEM蕴含DNE
theorem lem_implies_dne (P : Prop) (lem : P ∨ ¬P) : ¬¬P → P :=
  λhnnp => match lem with
  | Or.inl p => p
  | Or.inr np => False.elim (hnnp np)

-- DNE蕴含LEM (需要排中律本身或构造)
-- 实际上DNE不直接蕴含LEM在直觉逻辑中
-- 需要更强的假设
```

---

### 习题 4: 类型同构

**题目**: 证明$A \rightarrow (B \rightarrow C)$与$(A \times B) \rightarrow C$同构

**解答**:

```lean
-- Curry化与Uncurry化
def curry {A B C : Type} : ((A × B) → C) → (A → B → C) :=
  λf => λa => λb => f (a, b)

def uncurry {A B C : Type} : (A → B → C) → ((A × B) → C) :=
  λf => λp => f p.1 p.2

-- 证明互逆
theorem curry_uncurry {A B C : Type} (f : A → B → C) :
  curry (uncurry f) = f := rfl

theorem uncurry_curry {A B C : Type} (f : (A × B) → C) :
  uncurry (curry f) = f := by
  funext p
  cases p
  rfl
```

---

### 习题 5: 依赖类型应用

**题目**: 使用依赖类型实现长度保持的向量映射函数

**解答**:

```lean
inductive Vect (A : Type) : Nat → Type where
  | nil : Vect A 0
  | cons : A → Vect A n → Vect A (n + 1)

def vmap {A B : Type} {n : Nat} (f : A → B) : Vect A n → Vect B n
  | .nil => .nil
  | .cons x xs => .cons (f x) (vmap f xs)

-- 类型保证: 输入输出长度相同
-- Vect A n → Vect B n

-- 示例使用
def numbers : Vect Nat 3 :=
  Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))

def doubled : Vect Nat 3 :=
  vmap (λx => x * 2) numbers
```

---

## 七、应用与拓展

### 7.1 程序验证

- **类型即规范**: 函数类型编码前置条件和后置条件
- **证明即验证**: 证明项保证实现满足规范
- **零开销抽象**: 证明在编译时验证，运行时擦除

### 7.2 自动定理证明

- **证明搜索**: 将定理证明视为类型 inhabitation 问题
- **策略语言**: 高级策略生成低层证明项
- **反射**: 将证明过程本身形式化

### 7.3 函数式编程

- **GADTs**: 广义代数数据类型编码更精确的类型
- **依赖类型**: Idris、Agda中的完整依赖类型
- **线性类型**: 资源敏感的类型系统

### 7.4 前沿方向

| 方向 | 描述 | 代表工作 |
|------|------|---------|
| 同伦类型论 | 类型即空间，项即路径 | HoTT Book |
| 立方类型论 | 高维路径代数 | Cubical Agda |
| 模式类型 | 效应和资源的类型 | Eff, Koka |
| 微分逻辑 | 可微分编程的逻辑基础 | Diff. Privacy |

---

## 参考文献

1. Howard, W. A. (1980). The formulae-as-types notion of construction.
2. Girard, J. Y., Taylor, P., & Lafont, Y. (1989). *Proofs and Types*.
3. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
4. Harper, R. (2016). *Practical Foundations for Programming Languages* (2nd ed.).
5. The Univalent Foundations Program. (2013). *Homotopy Type Theory*.

---

**相关文档**:
- [05-类型论/01-基础概念](01-基础概念.md) - λ演算基础
- [05-类型论/04-依赖类型](04-依赖类型.md) - 依赖类型深入
- [05-类型论/06-同伦类型论](06-同伦类型论.md) - 同伦类型论
- [01-基础内容/04-直觉逻辑](../01-基础内容/04-直觉逻辑.md) - 构造性逻辑
