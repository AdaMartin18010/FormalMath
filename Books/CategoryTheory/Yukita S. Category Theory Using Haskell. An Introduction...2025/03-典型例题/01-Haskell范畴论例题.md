# Haskell范畴论例题

**创建日期**: 2025年12月11日
**来源**: Category Theory Using Haskell, 全书
**主题编号**: CT.YUKITA.03.01

---

## 📑 目录

- [Haskell范畴论例题](#haskell范畴论例题)
  - [📑 目录](#-目录)
  - [一、函子例题](#一函子例题)
    - [例题1：验证Maybe是函子](#例题1验证maybe是函子)
    - [例题2：验证List是函子](#例题2验证list是函子)
  - [二、自然变换例题](#二自然变换例题)
    - [例题3：验证maybeToList是自然变换](#例题3验证maybetolist是自然变换)
    - [例题4：构造自然变换的复合](#例题4构造自然变换的复合)
  - [三、单子例题](#三单子例题)
    - [例题5：验证Maybe是单子](#例题5验证maybe是单子)
    - [例题6：使用单子进行错误处理](#例题6使用单子进行错误处理)
  - [四、极限例题](#四极限例题)
    - [例题7：计算积类型](#例题7计算积类型)
    - [例题8：计算余积类型](#例题8计算余积类型)
  - [五、形式证明方法总结](#五形式证明方法总结)
    - [5.1 证明方法分类](#51-证明方法分类)
    - [5.2 证明写作规范](#52-证明写作规范)

---

## 一、函子例题

### 例题1：验证Maybe是函子

**问题**：验证 `Maybe` 类型是函子，即实现 `Functor` 类型类并满足函子定律。

**解答**：

**步骤1**：实现 `Functor` 实例

```haskell
instance Functor Maybe where
    fmap f Nothing = Nothing
    fmap f (Just x) = Just (f x)
```

**步骤2**：验证恒等律

**恒等律**: `fmap id = id`

**证明**：

- `fmap id Nothing = Nothing = id Nothing` ✓
- `fmap id (Just x) = Just (id x) = Just x = id (Just x)` ✓

**步骤3**：验证复合律

**复合律**: `fmap (g . f) = fmap g . fmap f`

**证明**：

- `fmap (g . f) Nothing = Nothing`
- `(fmap g . fmap f) Nothing = fmap g Nothing = Nothing` ✓

- `fmap (g . f) (Just x) = Just ((g . f) x) = Just (g (f x))`
- `(fmap g . fmap f) (Just x) = fmap g (Just (f x)) = Just (g (f x))` ✓

**结论**：`Maybe` 是函子。

### 例题2：验证List是函子

**问题**：验证列表类型 `[]` 是函子。

**解答**：

**步骤1**：实现 `Functor` 实例

```haskell
instance Functor [] where
    fmap = map
```

**步骤2**：验证恒等律

**恒等律**: `fmap id = id`

**证明**：

- `fmap id [] = [] = id []` ✓
- `fmap id [x1, x2, ..., xn] = [id x1, id x2, ..., id xn] = [x1, x2, ..., xn] = id [x1, x2, ..., xn]` ✓

**步骤3**：验证复合律

**复合律**: `fmap (g . f) = fmap g . fmap f`

**证明**：

- `fmap (g . f) [x1, x2, ..., xn] = [(g . f) x1, (g . f) x2, ..., (g . f) xn] = [g (f x1), g (f x2), ..., g (f xn)]`
- `(fmap g . fmap f) [x1, x2, ..., xn] = fmap g [f x1, f x2, ..., f xn] = [g (f x1), g (f x2), ..., g (f xn)]` ✓

**结论**：`[]` 是函子。

---

## 二、自然变换例题

### 例题3：验证maybeToList是自然变换

**问题**：验证 `maybeToList :: Maybe a -> [a]` 是自然变换。

**解答**：

**步骤1**：定义自然变换

```haskell
maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]
```

**步骤2**：验证自然性条件

**自然性条件**: 对任意函数 `f :: a -> b`，`fmap f . maybeToList = maybeToList . fmap f`

**证明**：

- **左边**: `(fmap f . maybeToList) Nothing = fmap f [] = []`
- **右边**: `(maybeToList . fmap f) Nothing = maybeToList Nothing = []` ✓

- **左边**: `(fmap f . maybeToList) (Just x) = fmap f [x] = [f x]`
- **右边**: `(maybeToList . fmap f) (Just x) = maybeToList (Just (f x)) = [f x]` ✓

**结论**：`maybeToList` 是自然变换 $\eta: \text{Maybe} \Rightarrow []$。

### 例题4：构造自然变换的复合

**问题**：给定自然变换 `maybeToList :: Nat Maybe []` 和 `listToSet :: Nat [] Set`，构造复合自然变换 `maybeToSet :: Nat Maybe Set`。

**解答**：

**步骤1**：定义复合自然变换

```haskell
maybeToSet :: Maybe a -> Set a
maybeToSet = listToSet . maybeToList
```

**步骤2**：验证自然性条件

**自然性条件**: 对任意函数 `f :: a -> b`，`fmap f . maybeToSet = maybeToSet . fmap f`

**证明**：

- `(fmap f . maybeToSet) = fmap f . listToSet . maybeToList`
- `(maybeToSet . fmap f) = listToSet . maybeToList . fmap f`

由于 `maybeToList` 和 `listToSet` 都是自然变换，有：

- `maybeToList . fmap f = fmap f . maybeToList`
- `listToSet . fmap f = fmap f . listToSet`

因此：

- `listToSet . maybeToList . fmap f = listToSet . fmap f . maybeToList = fmap f . listToSet . maybeToList` ✓

**结论**：自然变换的复合是自然变换。

---

## 三、单子例题

### 例题5：验证Maybe是单子

**问题**：验证 `Maybe` 是单子，即实现 `Monad` 类型类并满足单子定律。

**解答**：

**步骤1**：实现 `Monad` 实例

```haskell
instance Monad Maybe where
    return x = Just x
    Nothing >>= f = Nothing
    Just x >>= f = f x
```

**步骤2**：验证左单位律

**左单位律**: `return x >>= f = f x`

**证明**：

- `return x >>= f = Just x >>= f = f x` ✓

**步骤3**：验证右单位律

**右单位律**: `m >>= return = m`

**证明**：

- `Nothing >>= return = Nothing` ✓
- `Just x >>= return = return x = Just x` ✓

**步骤4**：验证结合律

**结合律**: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`

**证明**：

- **情况1**: `m = Nothing`
  - 左边：`(Nothing >>= f) >>= g = Nothing >>= g = Nothing`
  - 右边：`Nothing >>= (\x -> f x >>= g) = Nothing` ✓

- **情况2**: `m = Just x`
  - 左边：`(Just x >>= f) >>= g = f x >>= g`
  - 右边：`Just x >>= (\x -> f x >>= g) = (\x -> f x >>= g) x = f x >>= g` ✓

**结论**：`Maybe` 是单子。

### 例题6：使用单子进行错误处理

**问题**：使用 `Maybe` 单子实现安全的除法运算。

**解答**：

**步骤1**：定义安全除法

```haskell
safeDiv :: Double -> Double -> Maybe Double
safeDiv x y = if y == 0 then Nothing else Just (x / y)
```

**步骤2**：使用单子进行链式计算

```haskell
-- 计算 (a / b) / c
chainDiv :: Double -> Double -> Double -> Maybe Double
chainDiv a b c = safeDiv a b >>= \x -> safeDiv x c

-- 使用do记号
chainDiv' :: Double -> Double -> Double -> Maybe Double
chainDiv' a b c = do
    x <- safeDiv a b
    safeDiv x c
```

**步骤3**：验证

- `chainDiv 10 2 5 = Just 1.0` ✓
- `chainDiv 10 0 5 = Nothing` ✓（除以零）
- `chainDiv 10 2 0 = Nothing` ✓（除以零）

**结论**：单子提供了一种优雅的错误处理方式。

---

## 四、极限例题

### 例题7：计算积类型

**问题**：在Haskell中，积类型 `(A, B)` 是范畴论中积的实现。验证它满足积的泛性质。

**解答**：

**步骤1**：定义投影函数

```haskell
fst :: (a, b) -> a
fst (x, y) = x

snd :: (a, b) -> b
snd (x, y) = y
```

**步骤2**：验证泛性质

**泛性质**: 对任意对象 $X$ 和映射 $f: X \to A$，$g: X \to B$，存在唯一的映射 $h: X \to (A, B)$ 使得 $fst \circ h = f$ 且 $snd \circ h = g$。

**构造**：

```haskell
h :: X -> (A, B)
h x = (f x, g x)
```

**验证**：

- `fst . h = fst . (\x -> (f x, g x)) = \x -> f x = f` ✓
- `snd . h = snd . (\x -> (f x, g x)) = \x -> g x = g` ✓

**唯一性**：如果存在另一个映射 $h': X \to (A, B)$ 满足条件，则：

- `fst . h' = f` 且 `snd . h' = g`
- 因此 `h' x = (fst (h' x), snd (h' x)) = (f x, g x) = h x`
- 所以 $h' = h$ ✓

**结论**：`(A, B)` 满足积的泛性质。

### 例题8：计算余积类型

**问题**：在Haskell中，`Either A B` 是范畴论中余积的实现。验证它满足余积的泛性质。

**解答**：

**步骤1**：定义包含函数

```haskell
Left :: a -> Either a b
Left = Left

Right :: b -> Either a b
Right = Right
```

**步骤2**：验证泛性质

**泛性质**: 对任意对象 $X$ 和映射 $f: A \to X$，$g: B \to X$，存在唯一的映射 $h: \text{Either } A B \to X$ 使得 $h \circ \text{Left} = f$ 且 $h \circ \text{Right} = g$。

**构造**：

```haskell
h :: Either a b -> x
h (Left x) = f x
h (Right y) = g y
```

**验证**：

- `h . Left = h . (\x -> Left x) = \x -> h (Left x) = \x -> f x = f` ✓
- `h . Right = h . (\y -> Right y) = \y -> h (Right y) = \y -> g y = g` ✓

**唯一性**：如果存在另一个映射 $h': \text{Either } A B \to X$ 满足条件，则：

- `h' . Left = f` 且 `h' . Right = g`
- 因此 `h' (Left x) = (h' . Left) x = f x = h (Left x)`
- `h' (Right y) = (h' . Right) y = g y = h (Right y)`
- 所以 $h' = h$ ✓

**结论**：`Either A B` 满足余积的泛性质。

---

## 五、形式证明方法总结

### 5.1 证明方法分类

**直接证明**：从已知条件直接推导出结论

- 例子：例题1-2（函子验证）、例题5（单子验证）

**构造性证明**：通过构造具体例子来证明存在性

- 例子：例题3-4（自然变换）、例题7-8（极限/余极限）

**验证性证明**：通过验证定律来证明

- 例子：例题1-2（函子定律）、例题5（单子定律）

### 5.2 证明写作规范

**标准结构**：

1. 陈述问题
2. 实现类型类实例
3. 验证定律
4. 得出结论
5. 验证结果

**参考资源**：

- Wikipedia: [范畴论](https://zh.wikipedia.org/wiki/%E8%8C%83%E7%95%B4%E8%AE%BA)
- Haskell Wiki: [Category Theory](https://wiki.haskell.org/Category_theory)
- MIT 18.701: Abstract Algebra
- Stanford CS242: Programming Languages

---

**最后更新**: 2025年12月11日
**参考章节**: 全书
**参考资源**: Wikipedia, Haskell Wiki, MIT 18.701, Stanford CS242
