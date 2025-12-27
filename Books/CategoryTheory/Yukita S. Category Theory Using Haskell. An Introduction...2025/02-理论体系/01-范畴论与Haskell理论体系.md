# 范畴论与Haskell理论体系

**创建日期**: 2025年12月11日
**来源**: Category Theory Using Haskell, 全书
**主题编号**: CT.YUKITA.02.01

---

## 📑 目录

- [范畴论与Haskell理论体系](#范畴论与haskell理论体系)
  - [📑 目录](#-目录)
  - [一、基础理论](#一基础理论)
    - [1.1 范畴的定义](#11-范畴的定义)
    - [1.2 Hask范畴](#12-hask范畴)
  - [二、函子理论](#二函子理论)
    - [2.1 函子的定义](#21-函子的定义)
    - [2.2 Haskell中的函子](#22-haskell中的函子)
    - [2.3 协变函子与反变函子](#23-协变函子与反变函子)
  - [三、自然变换理论](#三自然变换理论)
    - [3.1 自然变换的定义](#31-自然变换的定义)
    - [3.2 Haskell中的自然变换](#32-haskell中的自然变换)
  - [四、泛性质理论](#四泛性质理论)
    - [4.1 终对象与始对象](#41-终对象与始对象)
    - [4.2 积与余积](#42-积与余积)
    - [4.3 极限与余极限](#43-极限与余极限)
  - [五、单子理论](#五单子理论)
    - [5.1 单子的定义](#51-单子的定义)
    - [5.2 Haskell中的单子](#52-haskell中的单子)
    - [5.3 单子的例子](#53-单子的例子)
  - [六、Yoneda引理](#六yoneda引理)
    - [6.1 Yoneda引理](#61-yoneda引理)
    - [6.2 Yoneda机器](#62-yoneda机器)
  - [七、伴随理论](#七伴随理论)
    - [7.1 伴随的定义](#71-伴随的定义)
    - [7.2 伴随与单子](#72-伴随与单子)

---

## 一、基础理论

### 1.1 范畴的定义

**范畴 (Category)** $\mathcal{C}$ 由以下数据组成：

1. **对象集合**: $\text{Ob}(\mathcal{C})$
2. **映射集合**: 对每对对象 $A, B$，集合 $\text{Hom}(A, B)$
3. **恒等映射**: 对每个对象 $A$，$1_A \in \text{Hom}(A, A)$
4. **复合运算**: 对 $f \in \text{Hom}(A, B)$ 和 $g \in \text{Hom}(B, C)$，$g \circ f \in \text{Hom}(A, C)$

**满足的规则**：

- **恒等律**: $f \circ 1_A = f$ 且 $1_B \circ f = f$
- **结合律**: $(h \circ g) \circ f = h \circ (g \circ f)$

### 1.2 Hask范畴

**Hask范畴**定义：

- **对象**: Haskell类型
- **映射**: Haskell函数 `f :: A -> B`
- **恒等映射**: `id :: A -> A`
- **复合**: `(.) :: (b -> c) -> (a -> b) -> (a -> c)`

**数学表示**：

- 对象：$A, B, C \in \text{Ob}(\mathbf{Hask})$
- 映射：$f: A \to B$ 对应 `f :: A -> B`
- 恒等：$1_A$ 对应 `id :: A -> A`
- 复合：$g \circ f$ 对应 `g . f`

---

## 二、函子理论

### 2.1 函子的定义

**函子 (Functor)** $F: \mathcal{C} \to \mathcal{D}$ 由以下数据组成：

1. **对象映射**: $F: \text{Ob}(\mathcal{C}) \to \text{Ob}(\mathcal{D})$
2. **映射映射**: 对 $f: A \to B$，$F(f): F(A) \to F(B)$

**满足的条件**：

- **恒等保持**: $F(1_A) = 1_{F(A)}$
- **复合保持**: $F(g \circ f) = F(g) \circ F(f)$

### 2.2 Haskell中的函子

**Functor类型类**：

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
```

**函子定律**：

1. `fmap id = id`（恒等保持）
2. `fmap (g . f) = fmap g . fmap f`（复合保持）

**数学对应**：

- `Functor f` 对应函子 $F: \mathbf{Hask} \to \mathbf{Hask}$
- `fmap` 对应映射映射 $F(f)$

### 2.3 协变函子与反变函子

**协变函子**: 保持映射方向 $A \to B$ 映射到 $F(A) \to F(B)$

**反变函子**: 反转映射方向 $A \to B$ 映射到 $F(B) \to F(A)$

**Haskell实现**：

- 协变函子：`Functor` 类型类
- 反变函子：`Contravariant` 类型类

---

## 三、自然变换理论

### 3.1 自然变换的定义

**自然变换 (Natural Transformation)** $\eta: F \Rightarrow G$ 是函子 $F, G: \mathcal{C} \to \mathcal{D}$ 之间的映射：

- **分量映射**: 对每个对象 $A$，$\eta_A: F(A) \to G(A)$
- **自然性条件**: 对任意 $f: A \to B$，$\eta_B \circ F(f) = G(f) \circ \eta_A$

### 3.2 Haskell中的自然变换

**多态函数作为自然变换**：

```haskell
type Nat f g = forall a. f a -> g a
```

**自然性条件**：

- 对任意函数 `f :: a -> b`，`fmap f . eta = eta . fmap f`
- `forall` 量化确保自然性条件自动满足

**例子**：

```haskell
maybeToList :: Nat Maybe []
maybeToList Nothing = []
maybeToList (Just x) = [x]
```

---

## 四、泛性质理论

### 4.1 终对象与始对象

**终对象 (Terminal Object)**: 对象 $T$ 使得对任意对象 $A$，存在唯一的映射 $A \to T$

**始对象 (Initial Object)**: 对象 $I$ 使得对任意对象 $A$，存在唯一的映射 $I \to A$

**Haskell对应**：

- 终对象：`()`（单位类型）
- 始对象：`Void`（空类型）

### 4.2 积与余积

**积 (Product)**: 对象 $A \times B$ 连同投影 $p_1: A \times B \to A$ 和 $p_2: A \times B \to B$，满足泛性质

**余积 (Coproduct)**: 对象 $A + B$ 连同包含 $i_1: A \to A + B$ 和 $i_2: B \to A + B$，满足泛性质

**Haskell对应**：

- 积：`(A, B)`（元组）
- 余积：`Either A B`（和类型）

### 4.3 极限与余极限

**极限 (Limit)**: 图的极限是满足泛性质的锥

**余极限 (Colimit)**: 图的余极限是满足泛性质的余锥

**Haskell对应**：

- 极限：积、等化子等
- 余极限：余积、余等化子等

---

## 五、单子理论

### 5.1 单子的定义

**单子 (Monad)** $(T, \eta, \mu)$ 由以下数据组成：

1. **函子**: $T: \mathcal{C} \to \mathcal{C}$
2. **单位自然变换**: $\eta: 1_{\mathcal{C}} \Rightarrow T$
3. **乘法自然变换**: $\mu: T \circ T \Rightarrow T$

**满足的条件**：

- **左单位律**: $\mu \circ (T \eta) = 1_T$
- **右单位律**: $\mu \circ (\eta T) = 1_T$
- **结合律**: $\mu \circ (T \mu) = \mu \circ (\mu T)$

### 5.2 Haskell中的单子

**Monad类型类**：

```haskell
class Functor m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b
```

**单子定律**：

1. `return x >>= f = f x`（左单位律）
2. `m >>= return = m`（右单位律）
3. `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`（结合律）

**数学对应**：

- `return` 对应 $\eta$
- `(>>=)` 对应Kleisli扩展
- `join` 对应 $\mu$

### 5.3 单子的例子

**Maybe单子**: 可能失败的计算

**List单子**: 非确定性计算

**IO单子**: 输入输出操作

**State单子**: 状态计算

---

## 六、Yoneda引理

### 6.1 Yoneda引理

**Yoneda引理**: 对函子 $F: \mathcal{C}^{\text{op}} \to \mathbf{Set}$ 和对象 $A \in \mathcal{C}$，有自然同构：

$$\text{Nat}(\text{Hom}(-, A), F) \cong F(A)$$

**Haskell对应**：

- `Nat (Hom (-, a)) f` 对应 `f a`
- Yoneda引理说明函子由其值唯一确定

### 6.2 Yoneda机器

**Yoneda机器**: 使用Yoneda引理进行反向工程

**应用**：

- 隐藏参数
- 隐藏数据结构
- 隐藏态射

---

## 七、伴随理论

### 7.1 伴随的定义

**伴随 (Adjoint)** 函子对 $F \dashv G: \mathcal{C} \to \mathcal{D}$ 满足：

$$\text{Hom}_{\mathcal{D}}(F(A), B) \cong \text{Hom}_{\mathcal{C}}(A, G(B))$$

**自然同构**: 对任意对象 $A \in \mathcal{C}$ 和 $B \in \mathcal{D}$

### 7.2 伴随与单子

**从伴随到单子**: 伴随 $F \dashv G$ 产生单子 $T = G \circ F$

**从单子到伴随**: 单子 $(T, \eta, \mu)$ 产生Kleisli伴随

**Haskell对应**：

- 自由函子与遗忘函子构成伴随
- List单子来自自由单子与遗忘函子的伴随

---

**最后更新**: 2025年12月11日
**参考章节**: 全书
