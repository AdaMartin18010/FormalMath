---
university: Princeton
synonym: [Characteristic Classes, Stiefel-Whitney类, Chern类, Pontryagin类]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐⭐
concept_dependency: [向量丛, 上同调环, Grassmann流形]
prerequisite_concepts: [向量丛, 上同调环, 分类空间]
prerequisite_theorems: [Gysin序列, Thom同构]
course_context: MAT 365 Topology
msc2010: [57R20, 55R40, 55N20]
related_concepts: [Euler类, Thom类, 指标定理]
---

# AT-PN-008: 示性类 (Characteristic Classes)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 3, Section 3, p. 225-244
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 示性类理论

---

## 定义

### 向量丛

**定义**：拓扑空间 $B$ 上的**实秩 $n$ 向量丛**（real rank $n$ vector bundle）是映射 $p: E \to B$，使得：

- 每点 $b \in B$ 的纤维 $E_b = p^{-1}(b) \cong \mathbb{R}^n$
- 局部平凡：$B$ 有开覆盖 $\{U_\alpha\}$，使 $p^{-1}(U_\alpha) \cong U_\alpha \times \mathbb{R}^n$

类似可定义**复向量丛**（纤维为 $\mathbb{C}^n$）。

### Stiefel-Whitney类

**定义**：实向量丛 $\xi$ 的**全Stiefel-Whitney类**是：

$$w(\xi) = 1 + w_1(\xi) + w_2(\xi) + \cdots \in H^*(B; \mathbb{Z}/2)$$

其中 $w_i(\xi) \in H^i(B; \mathbb{Z}/2)$ 是**第 $i$ Stiefel-Whitney类**。

**公理化**：

1. $w_0(\xi) = 1$，$w_i(\xi) = 0$ 对 $i > \text{rank}(\xi)$
2. **自然性**：$w(f^*\xi) = f^*w(\xi)$
3. **Whitney和公式**：$w(\xi \oplus \eta) = w(\xi) \smile w(\eta)$
4. **非平凡性**：对 tautological线丛 $\gamma^1$ 在 $\mathbb{R}P^1 \cong S^1$ 上，$w_1(\gamma^1) \neq 0$

### Chern类

**定义**：复向量丛 $\xi$ 的**全Chern类**是：

$$c(\xi) = 1 + c_1(\xi) + c_2(\xi) + \cdots \in H^*(B; \mathbb{Z})$$

其中 $c_i(\xi) \in H^{2i}(B; \mathbb{Z})$ 是**第 $i$ Chern类**。

**公理化**：类似Stiefel-Whitney类，但系数为 $\mathbb{Z}$，且 Chern类为偶数维。

### 其他示性类

| 示性类 | 定义域 | 系数 | 维数 |
|--------|--------|------|------|
| Stiefel-Whitney $w_i$ | 实向量丛 | $\mathbb{Z}/2$ | $i$ |
| Chern $c_i$ | 复向量丛 | $\mathbb{Z}$ | $2i$ |
| Pontryagin $p_i$ | 实向量丛 | $\mathbb{Z}$ | $4i$ |
| Euler $e$ | 可定向实丛 | $\mathbb{Z}$ | rank |

**Pontryagin类**：对实向量丛 $\xi$，定义 $p_i(\xi) = (-1)^i c_{2i}(\xi \otimes \mathbb{C})$。

---

## 例子

### 例1：球面的切丛

**球面 $S^n$ 的切丛** $\tau_{S^n}$：

- $w(\tau_{S^n}) = 1$（对 $n$ 为奇数）
- $w(\tau_{S^n}) = 1 + w_n$（对 $n$ 为偶数）

**推论**（Hairy Ball Theorem）：$S^{2n}$ 没有处处非零的连续切向量场（因为 $w_{2n}(\tau) \neq 0$）。

### 例2：复射影空间的 tautological丛

**定理**：设 $\gamma^1$ 是 $\mathbb{C}P^n$ 上的 tautological线丛。则：

$$c(\gamma^1) = 1 + \alpha \in H^*(\mathbb{C}P^n; \mathbb{Z})$$

其中 $\alpha \in H^2(\mathbb{C}P^n)$ 是标准生成元。

### 例3：切丛的全Chern类

**定理**：对 $\mathbb{C}P^n$ 的切丛 $\tau$：

$$c(\tau) = (1 + \alpha)^{n+1} = \sum_{i=0}^n \binom{n+1}{i} \alpha^i$$

因此 $c_i(\tau) = \binom{n+1}{i} \alpha^i$。

### 例4：曲面的切丛

**亏格 $g$ 闭定向曲面 $M_g$**：

- Euler类：$\langle e(\tau), [M_g] \rangle = \chi(M_g) = 2 - 2g$
- Pontryagin类：$p_1 = 0$（因为维数为2）

---

## 性质

### 示性类的拓扑意义

| 示性类 | 几何意义 |
|--------|---------|
| $w_1$ | 可定向性：$w_1 = 0 \Leftrightarrow$ 丛可定向 |
| $w_2$ | 自旋结构的存在性（与物理相关） |
| $c_1$ | 复线丛的"扭曲程度" |
| $e$ | Euler示性数的推广 |

### Whitney和公式的应用

若丛分裂为线丛的直和 $\xi = \lambda_1 \oplus \cdots \oplus \lambda_n$，则：

$$c(\xi) = \prod_{i=1}^n (1 + c_1(\lambda_i))$$

展开可得：

- $c_1(\xi) = \sum c_1(\lambda_i)$
- $c_2(\xi) = \sum_{i<j} c_1(\lambda_i)c_1(\lambda_j)$

### 与分类空间的关系

**定理**：示性类对应于分类空间的上同调类：

$$H^*(BO(n); \mathbb{Z}/2) = \mathbb{Z}/2[w_1, \ldots, w_n]$$

$$H^*(BU(n); \mathbb{Z}) = \mathbb{Z}[c_1, \ldots, c_n]$$

---

## FormalMath对应

### 主要文档

- `docs/14-微分几何/03-微分几何深度扩展版.md` — 示性类理论
- `docs/00-习题示例反例库/拓扑/TOP-059-示性类-Stiefel-Whitney类.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| Stiefel-Whitney类 | `微分几何/Stiefel-Whitney类` |
| Chern类 | `微分几何/Chern类` |
| 示性类 | `代数拓扑/示性类` |

### Lean 4形式化参考

```lean
-- 示性类的形式化需要向量丛理论
-- 可以使用fiber bundle的框架
```

### 交叉引用

- **前序定义**: AT-PN-006 (上同调环)
- **相关领域**: 微分几何、指标理论
- **应用**: 指标定理、 anomaly cancellation

---

## Hatcher参考

- **章节**: Chapter 3, Section 3, "Characteristic Classes", p. 225-244
- **关键内容**：
  - Stiefel-Whitney类的公理和构造 (p. 225-232)
  - Chern类的定义 (p. 240-244)
  - Euler类 (p. 97-99 in Section 3.2)
- **关键习题**:
  - Exercise 3.3.1: 计算 $\mathbb{R}P^n$ 的切丛的Stiefel-Whitney类
  - Exercise 3.3.5: 利用示性类证明可除代数维数定理

---

## 总结

示性类是向量丛的拓扑不变量，将几何对象（丛）映射到代数对象（上同调类），是连接几何与拓扑的桥梁。

**关键要点**：

1. Stiefel-Whitney类：实丛，系数 $\mathbb{Z}/2$
2. Chern类：复丛，系数 $\mathbb{Z}$
3. 公理化定义保证唯一性
4. 在分类问题和可定向性问题中有重要应用
