---
msc_primary: "00A15"
msc_secondary: "01A99"
---

# 范畴与Haskell类型

**创建日期**: 2025年12月11日
**来源**: Category Theory Using Haskell, Chapter 1-2
**主题编号**: CT.YUKITA.01.01

---

## 📑 目录

- [范畴与Haskell类型](#范畴与haskell类型)
  - [📑 目录](#目录)
  - [一、范畴的定义](#一范畴的定义)
    - [1.1 范畴的数学定义](#11-范畴的数学定义)
    - [1.2 Haskell中的范畴](#12-haskell中的范畴)
  - [二、Haskell类型作为范畴](#二haskell类型作为范畴)
    - [2.1 类型系统](#21-类型系统)
    - [2.2 类型类与范畴](#22-类型类与范畴)
  - [三、类型与函数](#三类型与函数)
    - [3.1 函数类型](#31-函数类型)
    - [3.2 函数的性质](#32-函数的性质)
  - [四、恒等函数与复合](#四恒等函数与复合)
    - [4.1 恒等函数](#41-恒等函数)
    - [4.2 函数复合](#42-函数复合)

---

## 一、范畴的定义

### 1.1 范畴的数学定义

**范畴 (Category)** 由以下数据组成：

1. **对象 (Objects)**: 集合 $\text{Ob}(\mathcal{C})$
2. **映射 (Morphisms)**: 对每对对象 $A, B$，集合 $\text{Hom}(A, B)$
3. **恒等映射**: 对每个对象 $A$，$1_A \in \text{Hom}(A, A)$
4. **复合运算**: 对 $f \in \text{Hom}(A, B)$ 和 $g \in \text{Hom}(B, C)$，$g \circ f \in \text{Hom}(A, C)$

**满足的规则**：

- **恒等律**: $f \circ 1_A = f$ 且 $1_B \circ f = f$
- **结合律**: $(h \circ g) \circ f = h \circ (g \circ f)$

### 1.2 Haskell中的范畴

在Haskell中，**Hask范畴**定义如下：

- **对象**: Haskell类型（如 `Int`, `Bool`, `[Int]`）
- **映射**: Haskell函数（如 `f :: Int -> Bool`）
- **恒等映射**: `id :: a -> a`
- **复合**: `(.) :: (b -> c) -> (a -> b) -> (a -> c)`

**数学表示**：

- 对象：$A, B, C \in \text{Ob}(\mathbf{Hask})$
- 映射：$f: A \to B$ 对应 `f :: A -> B`
- 恒等：$1_A: A \to A$ 对应 `id :: A -> A`
- 复合：$g \circ f$ 对应 `g . f`

---

## 二、Haskell类型作为范畴

### 2.1 类型系统

**Haskell类型**形成范畴的对象：

- **基本类型**: `Int`, `Bool`, `Char`, `Double`
- **复合类型**: `[Int]`（列表），`(Int, Bool)`（元组），`Maybe Int`（可选类型）
- **函数类型**: `Int -> Bool`（函数类型）

**类型构造子**：

- `[]`：列表构造子，`[] :: * -> *`
- `Maybe`：可选类型构造子，`Maybe :: * -> *`
- `(,)`：元组构造子，`(,) :: * -> * -> *`

### 2.2 类型类与范畴

**类型类**可以看作范畴的"结构"：

```haskell
class Category cat where
    id :: cat a a
    (.) :: cat b c -> cat a b -> cat a c
```

**数学表示**：

- `Category` 类型类定义了范畴的结构
- `id` 对应恒等映射 $1_A$
- `(.)` 对应复合运算 $\circ$

---

## 三、类型与函数

### 3.1 函数类型

**函数类型** $A \to B$ 在Haskell中表示为 `A -> B`。

**数学定义**：

- 函数类型 $B^A$ 是所有从 $A$ 到 $B$ 的函数的集合
- 在Haskell中，`A -> B` 表示类型 $A$ 到类型 $B$ 的所有函数

**例子**：

```haskell
-- 函数类型
f :: Int -> Bool
f x = x > 0

-- 数学表示：f: Int → Bool
```

### 3.2 函数的性质

**单射 (Injection)**：

- 数学定义：$f(a_1) = f(a_2) \Rightarrow a_1 = a_2$
- Haskell中难以直接表达，但可以通过类型系统部分保证

**满射 (Surjection)**：

- 数学定义：$\forall b \in B, \exists a \in A, f(a) = b$
- Haskell中难以直接表达

**双射 (Bijection)**：

- 数学定义：既是单射又是满射
- 在Haskell中，同构类型对应双射

---

## 四、恒等函数与复合

### 4.1 恒等函数

**恒等函数** `id` 在Haskell中定义为：

```haskell
id :: a -> a
id x = x
```

**数学表示**：

- $1_A: A \to A$，$1_A(a) = a$
- 在Haskell中，`id :: A -> A` 对应 $1_A$

**性质**：

- **左恒等律**: `f . id = f`
- **右恒等律**: `id . f = f`

**数学证明**：

- $(f \circ 1_A)(a) = f(1_A(a)) = f(a)$
- $(1_B \circ f)(a) = 1_B(f(a)) = f(a)$

### 4.2 函数复合

**函数复合** `(.)` 在Haskell中定义为：

```haskell
(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g x = f (g x)
```

**数学表示**：

- $g \circ f: A \to C$，$(g \circ f)(a) = g(f(a))$
- 在Haskell中，`g . f` 对应 $g \circ f$

**性质**：

- **结合律**: `(h . g) . f = h . (g . f)`

**数学证明**：

- $((h \circ g) \circ f)(a) = (h \circ g)(f(a)) = h(g(f(a)))$
- $(h \circ (g \circ f))(a) = h((g \circ f)(a)) = h(g(f(a)))$

**例子**：

```haskell
-- 函数复合
f :: Int -> Bool
f x = x > 0

g :: Bool -> String
g True = "positive"
g False = "non-positive"

-- 复合函数
h = g . f  -- h :: Int -> String

-- 数学表示：h = g ∘ f: Int → String
```

---

**最后更新**: 2025年12月11日
**参考章节**: Chapter 1-2
