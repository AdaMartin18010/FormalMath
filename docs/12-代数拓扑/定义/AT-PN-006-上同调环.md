---
university: Princeton
synonym: [Cohomology Ring, 杯积, 分次环]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐⭐
concept_dependency: [上同调, 杯积, 分次代数]
prerequisite_concepts: [奇异同调, 对偶, 张量积]
prerequisite_theorems: [万有系数定理]
course_context: MAT 365 Topology
msc2010: [55N10, 55U15, 57T10]
related_concepts: [上同调运算, Steenrod平方, Poincaré对偶]
---

# AT-PN-006: 上同调环 (Cohomology Ring)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 3, Section 2, p. 206-213
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 上同调论

---

## 定义

### 上同调群

设 $X$ 是拓扑空间，$R$ 是环（通常为 $\mathbb{Z}, \mathbb{Q}, \mathbb{Z}/p, \mathbb{R}$）。

**定义**：$X$ 的**奇异 $n$-上链群** $C^n(X; R) = \text{Hom}(C_n(X), R)$ 是奇异 $n$-链群的对偶。

**上边缘算子** $\delta^n: C^n(X; R) \to C^{n+1}(X; R)$：

$$(\delta^n \varphi)(\sigma) = \varphi(\partial_{n+1} \sigma)$$

对 $\varphi \in C^n(X; R)$，$\sigma: \Delta^{n+1} \to X$。

**性质**：$\delta^{n+1} \circ \delta^n = 0$（因为 $\partial^2 = 0$）。

**上同调群**：
$$H^n(X; R) = \frac{\ker \delta^n}{\text{im } \delta^{n-1}}$$

### 杯积

**定义**：设 $\varphi \in C^i(X; R)$，$\psi \in C^j(X; R)$。**杯积** $\varphi \smile \psi \in C^{i+j}(X; R)$ 定义为：

$$(\varphi \smile \psi)(\sigma) = \varphi(\sigma|_{[v_0, \ldots, v_i]}) \cdot \psi(\sigma|_{[v_i, \ldots, v_{i+j}]})$$

对奇异 $(i+j)$-单形 $\sigma: [v_0, \ldots, v_{i+j}] \to X$，其中：

- $\sigma|_{[v_0, \ldots, v_i]}$ 是前 $i+1$ 个顶点张成的面
- $\sigma|_{[v_i, \ldots, v_{i+j}]}$ 是后 $j+1$ 个顶点张成的面

### 杯积的性质

**引理**（Leibniz法则）：$\delta(\varphi \smile \psi) = \delta\varphi \smile \psi + (-1)^i \varphi \smile \delta\psi$

**推论**：杯积诱导上同调层次的良定义乘法：
$$\smile: H^i(X; R) \times H^j(X; R) \to H^{i+j}(X; R)$$

### 上同调环

**定义**：$X$ 的**上同调环**（cohomology ring）是分次环：

$$H^*(X; R) = \bigoplus_{n=0}^\infty H^n(X; R)$$

配备：

- 加法：各分次的加法
- 乘法：杯积 $\smile$

### 分次交换性

**定理**：对 $[\alpha] \in H^i(X; R)$，$[\beta] \in H^j(X; R)$：

$$[\alpha] \smile [\beta] = (-1)^{ij} [\beta] \smile [\alpha]$$

**注**：这意味着上同调环是**反交换**（graded-commutative）的。

---

## 例子

### 例1：射影空间 $\mathbb{C}P^n$

**定理**：$H^*(\mathbb{C}P^n; \mathbb{Z}) \cong \mathbb{Z}[\alpha]/(\alpha^{n+1})$，其中 $|\alpha| = 2$。

即 $H^*(\mathbb{C}P^n)$ 是由2维生成元生成的截断多项式环。

**生成元**：$\alpha \in H^2(\mathbb{C}P^n)$ 可取为超平面类的Poincaré对偶。

### 例2：环面 $T^2 = S^1 \times S^1$

**定理**：$H^*(T^2; \mathbb{Z}) \cong \Lambda(a, b)$，外代数，其中 $|a| = |b| = 1$，$a^2 = b^2 = 0$，$ab = -ba$。

具体：

- $H^0 = \mathbb{Z}$
- $H^1 = \mathbb{Z}a \oplus \mathbb{Z}b$
- $H^2 = \mathbb{Z}(a \smile b)$

### 例3：球面 $S^n$

**定理**：$H^*(S^n; \mathbb{Z}) = \mathbb{Z}[x]/(x^2)$，$|x| = n$。

即 $H^0 \cong H^n \cong \mathbb{Z}$，其他为0，且非零元的杯积为0（因为维数限制）。

### 例4：实射影空间 $\mathbb{R}P^n$

**定理**：$H^*(\mathbb{R}P^n; \mathbb{Z}/2) \cong (\mathbb{Z}/2)[x]/(x^{n+1})$，$|x| = 1$。

注意系数为 $\mathbb{Z}/2$ 时，反交换性变为交换性（因为 $(-1)^{ij} = 1$ 在特征2）。

---

## 性质

### 函子性

**定理**：连续映射 $f: X \to Y$ 诱导环同态 $f^*: H^*(Y; R) \to H^*(X; R)$：

- $f^*(\alpha \smile \beta) = f^*\alpha \smile f^*\beta$
- $(f \circ g)^* = g^* \circ f^*$

### 同伦不变性

**定理**：同伦等价的映射诱导上同调环的同构。

### Kunneth公式（杯积视角）

对空间 $X, Y$，外积 $H^*(X) \otimes H^*(Y) \to H^*(X \times Y)$ 是环同态（配备适当的张量积分次乘法）。

### 与基本群的关系

**定理**：$H^1(X; G) \cong \text{Hom}(\pi_1(X), G)$ 对Abel群 $G$。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 上同调理论
- `docs/格洛腾迪克/03-上同调理论/` — 层上同调（相关）

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 上同调环 | `代数拓扑/上同调环` |
| 杯积 | `代数拓扑/杯积` |
| 分次交换 | `代数学/分次代数` |

### Lean 4形式化参考

```lean
-- 分次代数和杯积
-- 需要定义GradedAlgebra结构
structure GradedRing (R : Type) where
  components : ℕ → Type
  add : ∀ n, Add (components n)
  mul : ∀ i j, components i → components j → components (i + j)
  graded_comm : ∀ i j (a : components i) (b : components j),
    mul i j a b = (-1)^(i*j) • mul j i b a
```

### 交叉引用

- **前序定义**: AT-PN-004 (奇异同调)
- **后续定义**: AT-PN-008 (示性类)
- **相关定理**: Poincaré对偶、万有系数定理

---

## Hatcher参考

- **章节**: Chapter 3, Section 2, "Cup Product", p. 206-213
- **关键内容**：
  - 杯积的定义 (p. 206)
  - 分次交换性证明 (p. 210-211)
  - 上同调环的例子 (p. 212-218)
- **关键习题**:
  - Exercise 3.2.1: 计算 $S^1 \times S^1 \times S^1$ 的上同调环
  - Exercise 3.2.6: 证明 $\mathbb{H}P^n$ 的上同调环结构

---

## 总结

上同调环是上同调理论的乘法结构，它提供了比同调群更精细的不变量。

**关键要点**：

1. 杯积是上同调的乘法结构
2. 分次交换性：$\alpha \smile \beta = (-1)^{ij} \beta \smile \alpha$
3. 上同调环是比同调群更强的不变量
4. 可以区分具有相同同调群的空间
