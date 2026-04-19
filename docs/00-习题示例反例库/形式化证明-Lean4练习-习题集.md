---
msc_primary: 68-XX
msc_secondary:
  - 68Vxx
processed_at: '2026-04-20'
title: 形式化证明·Lean 4 练习习题集
---

# 形式化证明·Lean 4 练习习题集

> 覆盖基础证明策略、归纳法、`rw`、`linarith`、`ring` 及结构化证明。共 15 题。

---

### 题1. 自然数的加法交换律
**题目**：在 Lean 4 中证明对任意自然数 $n,m$，有 $n+m=m+n$。

**难度**：★★☆☆☆

**解答**：
```lean
theorem add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    simp [Nat.zero_add, Nat.add_zero]
  | succ n ih =>
    simp [Nat.succ_add, ih]
```
**推导说明**：对 $n$ 归纳。基例 $n=0$：`Nat.zero_add` 给出 $0+m=m$，`Nat.add_zero` 给出 $m+0=m$。归纳步：$(n+1)+m$ 由 `Nat.succ_add` 等于 $(n+m)+1$，归纳假设 $n+m=m+n$，再用 `Nat.add_succ` 得 $m+(n+1)$。

---

### 题2. 列表长度的反转不变性
**题目**：证明对任意列表 `xs : List α`，`List.length (List.reverse xs) = List.length xs`。

**难度**：★★☆☆☆

**解答**：
```lean
theorem length_reverse (xs : List α) : (xs.reverse).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.reverse_cons, List.length_append, ih]
    <;> linarith
```
**推导说明**：基例空列表显然。归纳步：`x :: xs` 的反转等于 `reverse xs ++ [x]`。其长度为 `length (reverse xs) + 1`，由归纳假设等于 `length xs + 1 = length (x :: xs)`。`simp` 展开定义，`linarith` 处理算术。

---

### 题3. 算术-几何平均不等式（二元）
**题目**：对非负实数 $a,b$，证明 $\frac{a+b}{2}\ge\sqrt{ab}$。

**难度**：★★★☆☆

**解答**：
```lean
theorem am_gm_2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have h : ((a + b) / 2) ^ 2 ≥ a * b := by
    linarith [sq_nonneg (a - b)]
  have h2 : Real.sqrt (((a + b) / 2) ^ 2) = (a + b) / 2 := by
    apply Real.sqrt_sq (by linarith)
  have h3 : Real.sqrt (a * b) ≤ Real.sqrt (((a + b) / 2) ^ 2) := by
    apply Real.sqrt_le_sqrt (by linarith)
  rw [h2] at h3
  exact h3
```
**推导说明**：两边平方，$(a+b)^2/4\ge ab$ 等价于 $(a-b)^2\ge 0$。`sq_nonneg` 提供非负性，`linarith` 推导不等式。再利用 $\sqrt{x^2}=x$（$x\ge 0$）及 $\sqrt{}$ 的单调性传递不等式。

---

### 题4. 集合的 De Morgan 律
**题目**：证明对类型 `α` 的任意集合 `A,B : Set α`，有 $(A \cup B)^\complement = A^\complement \cap B^\complement$。

**难度**：★★☆☆☆

**解答**：
```lean
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp [Set.mem_compl_iff, Set.mem_union, Set.mem_inter]
  apply not_or
```
**推导说明**：`ext x` 进行外延证明（证两集合有相同元素）。`simp` 展开成员关系定义：$x\in(A\cup B)^\complement$ 即 $\neg(x\in A\cup B)$，等价于 $\neg(x\in A\lor x\in B)$。`not_or`（即 De Morgan 律在命题逻辑中）给出 $\neg(x\in A)\land\neg(x\in B)$，即 $x\in A^\complement\cap B^\complement$。

---

### 题5. 数学归纳法的强形式
**题目**：证明对任意自然数 $n$，前 $n$ 个自然数之和为 $\frac{n(n+1)}{2}$。

**难度**：★★☆☆☆

**解答**：
```lean
theorem sum_n (n : Nat) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Nat.mul_add, Nat.add_mul]
    ring_nf
    <;> omega
```
**推导说明**：基例 $n=0$：和为 $0$，公式给出 $0$。归纳步：$\sum_{i=0}^{n+1}i=(n+1)+\sum_{i=0}^n i$。由归纳假设代入 $\frac{n(n+1)}{2}$，得 $(n+1)+\frac{n(n+1)}{2}=\frac{(n+1)(n+2)}{2}$。`ring_nf` 整理多项式，`omega` 处理自然数除法与不等式。

---

### 题6. 函数的单射与左逆
**题目**：证明函数 $f : \alpha \to \beta$ 为单射当且仅当存在 $g : \beta \to \alpha$ 使得 $g \circ f = \operatorname{id}$（需选择公理或 `Inhabited` 条件）。

**难度**：★★★☆☆

**解答**：
```lean
theorem injective_iff_left_inverse {α β : Type*} [Inhabited α] (f : α → β) :
    Function.Injective f ↔ ∃ g : β → α, g ∘ f = id := by
  constructor
  · intro h
    let g : β → α := fun y =>
      if h' : ∃ x, f x = y then h'.choose else default
    use g
    funext x
    have hx : ∃ z, f z = f x := ⟨x, rfl⟩
    simp [g, hx, h hx.choose_spec]
  · rintro ⟨g, hg⟩ x y hf
    have : g (f x) = g (f y) := by rw [hf]
    simpa [Function.comp_apply] using this
```
**推导说明**：`→`：对单射 $f$，构造左逆：若 $y\in\operatorname{im}f$，取原像（由 `choose`）；否则取默认值。由单射性，原像唯一。`←`：若 $g\circ f=\operatorname{id}$，则 $f(x)=f(y)$ 推出 $g(f(x))=g(f(y))$ 即 $x=y$。

---

### 题7. 群论：子群的交仍为子群
**题目**：设 `G` 为群，`H,K` 为子群。证明 `H ∩ K` 为子群。

**难度**：★★★☆☆

**解答**：
```lean
theorem Subgroup.inter {G : Type*} [Group G] (H K : Subgroup G) :
    IsSubgroup (H.carrier ∩ K.carrier) := by
  constructor
  · -- 包含单位元
    simp [H.one_mem, K.one_mem]
  · -- 对乘法封闭
    intro x y hx hy
    simp at hx hy ⊢
    constructor
    · exact H.mul_mem hx.1 hy.1
    · exact K.mul_mem hx.2 hy.2
  · -- 对逆元封闭
    intro x hx
    simp at hx ⊢
    constructor
    · exact H.inv_mem hx.1
    · exact K.inv_mem hx.2
```
**推导说明**：子群判定三公理：含单位元、对乘法封闭、对取逆封闭。`H.carrier ∩ K.carrier` 中的元素满足同时在 `H` 和 `K` 中。分别调用子群的对应性质即得。

---

### 题8. 逻辑：排中律的双否定
**题目**：在 Lean 的经典逻辑下，证明对任意命题 $P$，$\neg\neg P \to P$。

**难度**：★★☆☆☆

**解答**：
```lean
theorem not_not_em (P : Prop) : ¬¬P → P := by
  intro h
  by_cases hp : P
  · exact hp
  · contradiction
```
**推导说明**：`by_cases` 应用排中律 $P\lor\neg P$。若 $P$ 成立，直接得证。若 $\neg P$ 成立，与假设 $\neg\neg P$ 矛盾（`contradiction` 自动消解）。注意此证明依赖经典逻辑；在构造逻辑中不可证。

---

### 题9. 线性不等式的自动求解
**题目**：设实数 $x,y,z$ 满足 $x+y+z=6$，$x\ge 0$，$y\ge 1$，$z\ge 2$。证明 $x^2+y^2+z^2\ge 14$。

**难度**：★★★☆☆

**解答**：
```lean
theorem ineq_linarith (x y z : ℝ) (h : x + y + z = 6)
    (hx : 0 ≤ x) (hy : 1 ≤ y) (hz : 2 ≤ z) :
    x^2 + y^2 + z^2 ≥ 14 := by
  have h1 : y = 6 - x - z := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 2), sq_nonneg (x - z + 1)]
```
**推导说明**：消元后 $y=6-x-z$。代入目标并展开：$x^2+(6-x-z)^2+z^2-14$。利用约束条件，最小值在边界达到。`nlinarith`（非线性算术求解器）结合平方非负性提示自动证明。提示 `sq_nonneg` 提供配方方向：$x\ge 0,z\ge 2$ 且 $y\ge 1$ 推出 $x+z\le 5$。

---

### 题10. 数论：欧几里得算法
**题目**：在 Lean 中证明对自然数 $a,b$，$\gcd(a,b)=\gcd(b,a\bmod b)$。

**难度**：★★★☆☆

**解答**：
```lean
theorem gcd_mod (a b : Nat) (hb : b > 0) : a.gcd b = b.gcd (a % b) := by
  rw [Nat.gcd_comm a b]
  rw [Nat.gcd_rec a b]
  rw [Nat.gcd_comm b (a % b)]
```
**推导说明**：`Nat.gcd_rec` 是 Mathlib 中欧几里得算法的核心引理：`gcd a b = gcd b (a % b)`。此处用 `gcd_comm` 调整顺序以匹配定义。实际证明中，`Nat.gcd` 的定义即基于此递归，故可直接调用库引理。

---

### 题11. 类型论：等价关系的商类型
**题目**：设 `α` 为类型，`r : α → α → Prop` 为等价关系。在 Lean 中构造商类型 `Quot r` 并证明其泛性质：任何与 `r` 相容的函数 `f : α → β` 可唯一通过商分解。

**难度**：★★★★☆

**解答**：
```lean
variable {α β : Type*} (r : α → α → Prop) [Equivalence r]

theorem quotient_universal (f : α → β)
    (hf : ∀ x y, r x y → f x = f y) :
    ∃! g : Quot r → β, g ∘ Quot.mk r = f := by
  let g : Quot r → β := Quot.lift f hf
  use g
  constructor
  · -- 分解性质
    funext x
    rfl
  · -- 唯一性
    intro g' h
    funext q
    induction q using Quot.ind with
    | mk x =>
      have : g' (Quot.mk r x) = f x := by
        rw [← Function.comp_apply g' (Quot.mk r) x, h]
      rw [this]
      rfl
```
**推导说明**：`Quot.lift` 构造商映射。存在性由 `lift` 直接给出。唯一性：对商元素 `q`，用 `Quot.ind` 归纳到代表元 `x`，则 `g' (Quot.mk r x) = (g' ∘ Quot.mk r) x = f x = g (Quot.mk r x)`。

---

### 题12. 拓扑：开集的并仍为开集
**题目**：在 Lean 的拓扑空间框架中，证明任意开集族的并仍为开集。

**难度**：★★☆☆☆

**解答**：
```lean
theorem isOpen_sUnion {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (h : ∀ s ∈ S, IsOpen s) : IsOpen (⋃₀ S) := by
  apply isOpen_sUnion
  exact h
```
**推导说明**：此即为拓扑空间公理之一。在 Mathlib 中，`TopologicalSpace` 类型类已包含此公理为 `isOpen_sUnion`（或 `isOpen_iUnion` 对指标族）。证明直接应用公理。若从公理化定义出发：
```lean
rw [TopologicalSpace.isOpen_sUnion]
exact h
```

---

### 题13. 实数的完备性：Cauchy 序列收敛
**题目**：在 Lean 中陈述并证明：实数中每个 Cauchy 序列收敛。

**难度**：★★★★☆

**解答**：
```lean
theorem complete_reals (seq : Nat → ℝ) (h : CauchySeq seq) :
    ∃ x, Tendsto seq atTop (𝓝 x) := by
  exact complete_space_provider seq h
```
**推导说明**：Mathlib 中 `ℝ` 已实例化为 `CompleteSpace`，故 `CauchySeq seq` 直接蕴含收敛。若从头证明：
1. Cauchy 序列有界（取 $\varepsilon=1$，则某尾项后波动 $<1$）。
2. 有界序列有收敛子列（Bolzano-Weierstrass，需紧致性）。
3. Cauchy 序列若有收敛子列则自身收敛于同一极限。

Lean 形式化 Bolzano-Weierstrass 需序拓扑的紧致性：`Icc a b` 为紧致，覆盖论证得有限子覆盖，构造单调子列。

---

### 题14. 代数：多项式环的整性
**题目**：证明若 $R$ 为整环，则多项式环 $R[X]$ 也是整环。

**难度**：★★★☆☆

**解答**：
```lean
theorem polynomial_integral_domain {R : Type*} [CommRing R] [IsDomain R] :
    IsDomain R[X] := by
  apply NoZeroDivisors.to_isDomain
  intro f g hfg
  by_contra h
  push_neg at h
  rcases h with ⟨hf, hg⟩
  have hlead : (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff := by
    rw [leadingCoeff_mul']
    exact mul_ne_zero
      (leadingCoeff_ne_zero.mpr hf)
      (leadingCoeff_ne_zero.mpr hg)
  have hzero : (f * g).leadingCoeff = 0 := by
    rw [hfg]
    simp
  rw [hzero] at hlead
  exact (mul_ne_zero
    (leadingCoeff_ne_zero.mpr hf)
    (leadingCoeff_ne_zero.mpr hg)) hlead
```
**推导说明**：反证法。设 $f,g\neq 0$ 但 $fg=0$。首项系数乘积 $(\operatorname{lead}f)(\operatorname{lead}g)$ 等于 $fg$ 的首项系数（因整环上首项不抵消）。但 $fg=0$ 推出首项系数为 $0$，与 $R$ 无零因子矛盾（两非零元乘积非零）。`leadingCoeff_mul'` 给出首项系数乘积公式。

---

### 题15. 归纳类型：二叉树的高度与节点数
**题目**：定义二叉树归纳类型 `BinTree α`，证明对任意树 `t`，`size t + 1 ≤ 2^(height t + 1)`。

**难度**：★★★★☆

**解答**：
```lean
inductive BinTree (α : Type*)
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α

def BinTree.height : BinTree α → Nat
  | leaf _ => 0
  | node l r => 1 + max l.height r.height

def BinTree.size : BinTree α → Nat
  | leaf _ => 1
  | node l r => 1 + l.size + r.size

theorem size_bound (t : BinTree α) : t.size + 1 ≤ 2 ^ (t.height + 1) := by
  induction t with
  | leaf _ => simp [BinTree.size, BinTree.height]
  | node l r ihl ihr =>
    simp [BinTree.size, BinTree.height]
    have h1 : l.size + 1 ≤ 2 ^ (l.height + 1) := ihl
    have h2 : r.size + 1 ≤ 2 ^ (r.height + 1) := ihr
    have h3 : 2 + l.size + r.size ≤ 2 ^ (max l.height r.height + 1 + 1) := by
      have hl : l.size + 1 ≤ 2 ^ (max l.height r.height + 1) := by
        have : l.height + 1 ≤ max l.height r.height + 1 := by simp
        have : 2 ^ (l.height + 1) ≤ 2 ^ (max l.height r.height + 1) :=
          Nat.pow_le_pow_of_le_right (by norm_num) this
        linarith
      have hr : r.size + 1 ≤ 2 ^ (max l.height r.height + 1) := by
        have : r.height + 1 ≤ max l.height r.height + 1 := by simp
        have : 2 ^ (r.height + 1) ≤ 2 ^ (max l.height r.height + 1) :=
          Nat.pow_le_pow_of_le_right (by norm_num) this
        linarith
      have : 2 + l.size + r.size = (l.size + 1) + (r.size + 1) := by ring
      rw [this]
      linarith
    linarith
```
**推导说明**：基例：叶子 `size=1`，`height=0`，$1+1\le 2^{1}=2$ 成立。归纳步：`node l r` 的 `size = 1 + l.size + r.size`，`height = 1 + max(height l, height r)`。对归纳假设，利用 $2^{h+1}+2^{h+1}=2^{h+2}$ 及 $\max$ 的单调性，将两边放大到统一高度后相加。
