# Yoneda引理 (Yoneda Lemma)

**创建日期**: 2025年12月11日
**来源**: Category Theory Using Haskell, Chapter 7
**主题编号**: CT.YUKITA.01.05

---

## 📑 目录

- [Yoneda引理 (Yoneda Lemma)](#yoneda引理-yoneda-lemma)
  - [📑 目录](#-目录)
  - [一、Yoneda引理的数学表述](#一yoneda引理的数学表述)
    - [1.1 协变Yoneda引理](#11-协变yoneda引理)
    - [1.2 反变Yoneda引理](#12-反变yoneda引理)
    - [1.3 证明思路](#13-证明思路)
  - [二、Haskell中的Yoneda引理](#二haskell中的yoneda引理)
    - [2.1 Yoneda引理的Haskell对应](#21-yoneda引理的haskell对应)
    - [2.2 Yoneda引理的验证](#22-yoneda引理的验证)
  - [三、Yoneda机器](#三yoneda机器)
    - [3.1 Yoneda机器的定义](#31-yoneda机器的定义)
    - [3.2 隐藏参数](#32-隐藏参数)
    - [3.3 隐藏数据结构](#33-隐藏数据结构)
  - [四、Yoneda引理的应用](#四yoneda引理的应用)
    - [4.1 性能优化](#41-性能优化)
    - [4.2 反向工程](#42-反向工程)
    - [4.3 API设计](#43-api设计)

---

## 一、Yoneda引理的数学表述

### 1.1 协变Yoneda引理

**协变Yoneda引理**：对函子 $F: \mathcal{C} \to \mathbf{Set}$ 和对象 $A \in \mathcal{C}$，有自然同构：

$$\text{Nat}(\text{Hom}(A, -), F) \cong F(A)$$

**解释**：

- 左边：从 $\text{Hom}(A, -)$ 到 $F$ 的所有自然变换的集合
- 右边：函子 $F$ 在对象 $A$ 处的值
- 意义：函子由其值唯一确定

### 1.2 反变Yoneda引理

**反变Yoneda引理**：对函子 $F: \mathcal{C}^{\text{op}} \to \mathbf{Set}$ 和对象 $A \in \mathcal{C}$，有自然同构：

$$\text{Nat}(\text{Hom}(-, A), F) \cong F(A)$$

**解释**：

- 左边：从 $\text{Hom}(-, A)$ 到 $F$ 的所有自然变换的集合
- 右边：函子 $F$ 在对象 $A$ 处的值
- 意义：预层由其值唯一确定

### 1.3 证明思路

**协变Yoneda引理的证明**：

1. **构造映射** $\Phi: \text{Nat}(\text{Hom}(A, -), F) \to F(A)$：
   - 对自然变换 $\eta: \text{Hom}(A, -) \Rightarrow F$，定义 $\Phi(\eta) = \eta_A(1_A)$

2. **构造逆映射** $\Psi: F(A) \to \text{Nat}(\text{Hom}(A, -), F)$：
   - 对元素 $x \in F(A)$，定义自然变换 $\Psi(x)_B(f) = F(f)(x)$，其中 $f: A \to B$

3. **验证互逆**：
   - $\Phi(\Psi(x)) = \Psi(x)_A(1_A) = F(1_A)(x) = 1_{F(A)}(x) = x$
   - $\Psi(\Phi(\eta))_B(f) = F(f)(\eta_A(1_A)) = \eta_B(\text{Hom}(A, f)(1_A)) = \eta_B(f)$

因此，$\Phi$ 和 $\Psi$ 是互逆的，建立了自然同构。

---

## 二、Haskell中的Yoneda引理

### 2.1 Yoneda引理的Haskell对应

**Yoneda引理在Haskell中**：

```haskell
-- Yoneda引理：Nat (Hom (-, a)) f ≅ f a

-- 协变情况
newtype Yoneda f a = Yoneda (forall b. (a -> b) -> f b)

-- 从Yoneda恢复原始值
lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda y) = y id

-- 提升到Yoneda
liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda fa = Yoneda $ \f -> fmap f fa
```

**数学对应**：

- `Yoneda f a` 对应 $\text{Nat}(\text{Hom}(a, -), F)$
- `lowerYoneda` 对应 $\Phi: \text{Nat}(\text{Hom}(a, -), F) \to F(a)$
- `liftYoneda` 对应 $\Psi: F(a) \to \text{Nat}(\text{Hom}(a, -), F)$

### 2.2 Yoneda引理的验证

**验证互逆性**：

```haskell
-- lowerYoneda . liftYoneda = id
lowerYoneda (liftYoneda fa) = lowerYoneda (Yoneda $ \f -> fmap f fa)
                            = (\f -> fmap f fa) id
                            = fmap id fa
                            = fa  -- 使用函子恒等律

-- liftYoneda . lowerYoneda = id
liftYoneda (lowerYoneda (Yoneda y)) = liftYoneda (y id)
                                    = Yoneda $ \f -> fmap f (y id)
                                    = Yoneda $ \f -> y (f . id)
                                    = Yoneda $ \f -> y f
                                    = Yoneda y  -- 使用自然性条件
```

**数学证明**：

- 使用函子恒等律：$F(1_A) = 1_{F(A)}$
- 使用自然性条件：$\eta_B \circ F(f) = \text{Hom}(a, f) \circ \eta_A$

---

## 三、Yoneda机器

### 3.1 Yoneda机器的定义

**Yoneda机器**使用Yoneda引理进行反向工程和优化。

**基本思想**：

- 隐藏数据结构的具体实现
- 通过"行为"（自然变换）来操作数据
- 利用Yoneda引理进行优化

### 3.2 隐藏参数

**隐藏参数的Yoneda机器**：

```haskell
-- 隐藏参数a的机器
newtype Machine a = Machine (forall b. (a -> b) -> b)

-- 从机器恢复值
runMachine :: Machine a -> a
runMachine (Machine m) = m id

-- 构造机器
makeMachine :: a -> Machine a
makeMachine a = Machine $ \f -> f a

-- 使用机器
useMachine :: Machine a -> (a -> b) -> b
useMachine (Machine m) = m
```

**数学原理**：

- Yoneda引理：$\text{Nat}(\text{Hom}(a, -), 1_{\mathbf{Hask}}) \cong a$
- 机器隐藏了参数 $a$，但可以通过"行为"恢复

### 3.3 隐藏数据结构

**隐藏列表的Yoneda机器**：

```haskell
-- 隐藏列表的机器
newtype ListMachine a = ListMachine (forall b. (a -> b) -> [b])

-- 恢复列表
revealList :: ListMachine a -> [a]
revealList (ListMachine m) = m id

-- 构造机器
hideList :: [a] -> ListMachine a
hideList xs = ListMachine $ \f -> fmap f xs

-- 使用机器
useListMachine :: ListMachine a -> (a -> b) -> [b]
useListMachine (ListMachine m) = m
```

**数学原理**：

- Yoneda引理：$\text{Nat}(\text{Hom}(a, -), []) \cong [a]$
- 机器隐藏了列表的具体实现，但可以通过"行为"恢复

---

## 四、Yoneda引理的应用

### 4.1 性能优化

**Yoneda引理用于性能优化**：

```haskell
-- 使用Yoneda延迟fmap的应用
newtype Yoneda f a = Yoneda (forall b. (a -> b) -> f b)

instance Functor (Yoneda f) where
    fmap f (Yoneda y) = Yoneda $ \g -> y (g . f)

-- 多个fmap可以合并
-- fmap f . fmap g = fmap (f . g)
```

**数学原理**：

- Yoneda引理允许延迟计算
- 多个 `fmap` 操作可以合并为一个
- 提高性能，减少中间数据结构

### 4.2 反向工程

**使用Yoneda引理进行反向工程**：

```haskell
-- 从"行为"恢复"数据"
recoverFromBehavior :: (forall b. (a -> b) -> f b) -> f a
recoverFromBehavior behavior = behavior id
```

**数学原理**：

- Yoneda引理：$\text{Nat}(\text{Hom}(a, -), F) \cong F(a)$
- 从自然变换（行为）可以恢复函子值（数据）
- 这允许从接口恢复实现

### 4.3 API设计

**Yoneda引理指导API设计**：

```haskell
-- 使用Yoneda设计抽象API
class Functor f => YonedaLike f where
    yonedaMap :: (forall b. (a -> b) -> f b) -> f a

-- 实现
instance YonedaLike [] where
    yonedaMap y = y id
```

**数学原理**：

- Yoneda引理说明函子由其值唯一确定
- API设计可以利用这一点
- 提供抽象接口，隐藏实现细节

---

**最后更新**: 2025年12月11日
**参考章节**: Chapter 7
