# ∞-范畴论：具体例子

> 从拟范畴到稳定∞-范畴的具体实现与计算

---

## 1. 拟范畴 (Quasicategories) 的具体例子

### 1.1 基本定义回顾

**定义** (拟范畴)

一个**拟范畴** (quasicategory) 是满足**内Kan条件**的单纯集合 $X: \Delta^{\text{op}} \to \text{Set}$：

对于所有 $0 < i < n$，任何内角 $\Lambda^n_i \to X$ 都可以填充为 $n$-单形 $\Delta^n \to X$。

### 1.2 经典例子

**例 1.2.1** (Nerve of a Category)

对于普通范畴 $\mathcal{C}$，其**nerve** $N\mathcal{C}$ 是一个拟范畴。

构造：

- $(N\mathcal{C})_n = \{\text{长度为 } n \text{ 的态射链}\}$
- 面映射和退化映射由复合和恒等给出

**验证拟范畴条件**：

- 对于 $0 < i < n$，填充 $n$-单形对应于选择适当的复合
- 对于普通范畴，复合是唯一的，因此填充唯一

**例 1.2.2** (拓扑空间的奇异单纯集合)

对于拓扑空间 $X$，定义**奇异单纯集合** $\text{Sing}(X)$：
$$\text{Sing}(X)_n = C(\Delta^n_{\text{top}}, X)$$
其中 $\Delta^n_{\text{top}}$ 是拓扑 $n$-单形。

**定理**：$\text{Sing}(X)$ 是一个拟范畴（实际上是Kan复形，因此也是拟范畴）。

*证明概要*：

- 拓扑单形的角可以被填充（因为 $\Delta^n_{\text{top}}$ 是可缩的）
- 通过连续性，这诱导了 $\text{Sing}(X)$ 上的填充

**例 1.2.3** (单纯集合的∞-范畴)

设 $\text{sSet}$ 是单纯集合的范畴。定义 $N^{\text{hc}}(\text{sSet})$ 为**同伦凝聚nerve**。

**性质**：

- 对象：单纯集合
- 1-态射：单纯映射
- 2-态射：单纯同伦
- 高阶态射：高阶同伦

---

### 1.3 非平凡例子

**例 1.3.1** (导出∞-范畴的底层拟范畴)

设 $\mathcal{A}$ 是Abel范畴。构造导出∞-范畴 $D_\infty(\mathcal{A})$ 如下：

- 对象：链复形 $C_\bullet$
- 1-态射：链映射
- 2-态射：链同伦
- 3-态射：链同伦的同伦
- ...

**具体构造**：

考虑范畴 $\text{Ch}(\mathcal{A})$ 的**Dwyer-Kan 局部化**在拟范畴的意义下：
$$D_\infty(\mathcal{A}) = N^{\text{hc}}(\text{Ch}(\mathcal{A})[W^{-1}])$$
其中 $W$ 是拟同构的类。

**例 1.3.2** (Kan复形作为∞-群胚)

每个**Kan复形**都是一个∞-群胚（所有1-态射可逆的∞-范畴）。

**具体例子**：

- **Eilenberg-MacLane空间**：$K(A, n)$ 对应只有一个非平凡同伦群 $\pi_n = A$ 的∞-群胚
- **球面**：$\text{Sing}(S^n)$ 是基本群非平凡的∞-群胚

---

## 2. ∞-群胚 (∞-Groupoids) 的实现

### 2.1 基本概念

**定义** (∞-群胚)

一个**∞-群胚**是所有1-态射都是等价（可逆的直到同伦）的∞-范畴。

### 2.2 从拓扑空间到∞-群胚

**Grothendieck假设**（已被证明）：

∞-群胚的范畴等价于拓扑空间的同伦范畴（在弱等价下的局部化）：
$$\infty\text{-}\mathbf{Gpd} \simeq \mathbf{Top}[W^{-1}]$$

**具体实现**:

| 拓扑空间 | 对应的∞-群胚 |
|---------|-------------|
| 点 $*$ | 终对象 |
| $S^1$ | 圆，$\pi_1 = \mathbb{Z}$，高阶平凡 |
| $S^n$ | $n$-球面，$\pi_n = \mathbb{Z}$ |
| $K(A, n)$ | 只有一个非平凡同伦群 $A$ |
| $\mathbb{RP}^\infty$ | 无穷阶循环群 |

**例 2.2.1** (圆的基本群胚)

拓扑空间 $S^1$ 对应∞-群胚具有以下性质：

- 对象：单点（因为 $S^1$ 连通）
- 自同态空间：$\text{Map}(*, *) \simeq \Omega S^1 \simeq \mathbb{Z}$
- 作为离散群，这给出：$B\mathbb{Z} = $ 带一个对象，自同态为 $\mathbb{Z}$ 的群胚

**验证**：$\pi_0 = 0$，$\pi_1 = \mathbb{Z}$，$\pi_n = 0$ ($n \geq 2$)

**例 2.2.2** (高阶Eilenberg-MacLane空间)

对于阿贝尔群 $A$ 和 $n \geq 1$，空间 $K(A, n)$ 对应的∞-群胚满足：
$$\pi_i = \begin{cases} A & i = n \\ 0 & \text{其他} \end{cases}$$

在∞-群胚的语言中：

- $n$-态射空间同构于 $A$
- 所有其他非平凡的同伦群消失

---

### 2.3 代数模型

**例 2.3.1** (链复形模型)

对于阿贝尔群 $A$，可以构造链复形：
$$C_\bullet = \begin{cases} A & \bullet = n \\ 0 & \text{其他} \end{cases}$$

对应的**Dold-Kan**对应给出单纯阿贝尔群，再取nerve得到∞-群胚。

**Dold-Kan对应**:
$$\text{Ch}_{\geq 0}(\text{Ab}) \xrightarrow{\simeq} \text{Fun}(\Delta^{\text{op}}, \text{Ab}) \to \infty\text{-}\mathbf{Gpd}$$

**例 2.3.2** (交叉复形)

对于非阿贝尔情形，使用**交叉复形** (crossed complexes)：

$$\cdots \to C_n \to C_{n-1} \to \cdots \to C_2 \to C_1 \rightrightarrows C_0$$

这给出了∞-群胚的代数描述。

---

## 3. 稳定∞-范畴 (Stable ∞-Categories) 的例子

### 3.1 定义与动机

**定义** (稳定∞-范畴)

一个∞-范畴 $\mathcal{C}$ 是**稳定的**，如果：

1. 有零对象 $0$
2. 每个态射有纤维和余纤维
3. 三角形既是纤维序列又是余纤维序列

**等价刻画**：

- 存在悬挂等价 $\Sigma: \mathcal{C} \to \mathcal{C}$
- $\mathcal{C}$ 是**预可加**的
- 序列 $A \to B \to C$ 是纤维序列当且仅当 $C \to \Sigma A$ 是纤维序列（旋转公理）

### 3.2 谱 (Spectra) 的∞-范畴

**例 3.2.1** (谱的稳定∞-范畴)

设 $\mathbf{Sp}$ 是**谱**的稳定∞-范畴。

**对象**：谱 $E = \{E_n, \sigma_n: \Sigma E_n \to E_{n+1}\}$

**映射空间**：
$$\text{Map}_{\mathbf{Sp}}(E, F) = \varprojlim_n \text{Map}_*(E_n, F_n)^{\text{h\Omega}}$$

**稳定性来源**：
$$\Omega^\infty: \mathbf{Sp} \rightleftarrows \mathbf{Top}_*: \Sigma^\infty_+$$
形成伴随对，且 $\mathbf{Sp}$ 是稳定化的结果。

**例 3.2.2** (球谱)

**球谱** $\mathbb{S}$ 是 $\mathbf{Sp}$ 的单位元：
$$\mathbb{S}_n = S^n$$
结构映射是恒等。

作为稳定∞-范畴的对象，它代表稳定同伦群：
$$\pi_n^{\text{st}} = \pi_n(\mathbb{S}) = \text{Ext}^{-n}_{\mathbf{Sp}}(\mathbb{S}, \mathbb{S})$$

### 3.3 导出∞-范畴

**例 3.3.1** (链复形的导出∞-范畴)

设 $R$ 是环。定义 $D_\infty(R)$ 为 $R$-模链复形的导出∞-范畴。

**构造**：

1. 从 $\text{Ch}(R)$ 开始（链复形的普通范畴）
2. 取 Dwyer-Kan 局部化在拟同构处
3. 结果是一个稳定∞-范畴

**稳定性验证**：

- 零对象：零复形
- 纤维/余纤维：映射锥/映射柱
- 旋转公理：来自长正合序列

**例 3.3.2** (拟凝聚层的导出∞-范畴)

设 $X$ 是概形。定义 $D_\infty(\text{QCoh}(X))$：

- 对象：拟凝聚层的复形
- 态射：导出意义下的态射
- 三角形：导出正合三角形

这是代数几何中导出范畴的现代框架。

---

## 4. 与导出范畴的联系

### 4.1 从∞-范畴到三角范畴

**定理** (Lurie)

稳定∞-范畴 $\mathcal{C}$ 的**同伦范畴** $h\mathcal{C}$ 自然具有三角范畴的结构。

**三角结构**：

- **平移函子** $\Sigma$ 来自稳定∞-范畴的悬挂
- **distinguished triangles**：来自纤维序列 $A \to B \to C$

### 4.2 具体例子

**例 4.2.1** ($D_\infty(R)$ vs $D(R)$)

对于环 $R$：

- $D_\infty(R)$：稳定∞-范畴
- $hD_\infty(R) \cong D(R)$：经典导出范畴

**联系**：

- 对象相同（拟同构类）
- $D(R)$ 丢失高阶信息（Ext的导出结构）
- $D_\infty(R)$ 保留完整的映射空间

**具体计算**：

对于 $R$-模 $M, N$，考虑为 $D_\infty(R)$ 中的对象（集中在度数0）：
$$\text{Map}_{D_\infty(R)}(M, N[n]) = \text{Ext}^n_R(M, N)$$

但 $D_\infty(R)$ 还包含：

- $\pi_k(\text{Map}(M, N[n]))$ 对于 $k > 0$
- 这些对应于高阶Ext群

**例 4.2.2** (谱的同伦群)

在 $\mathbf{Sp}$ 中：
$$\pi_n(\text{Map}_{\mathbf{Sp}}(E, F)) = [E, F]_{-n}$$
是稳定同伦群。

---

### 4.3 优势比较

| 特性 | 经典导出范畴 | 导出∞-范畴 |
|-----|-------------|-----------|
| 对象 | 链复形/层 | 相同 |
| 态射 | Ext群 | 映射空间 |
| 正合性 | 在三角中 | 在纤维序列中 |
| 正合函子 | 导出函子 | 可直接定义 |
| 泛性质 | 较弱 | 极强 |
| 技术难度 | 需要替换 | 概念上更直接 |

**关键优势**：

在导出∞-范畴中，可以严格地定义：

- 导出张量积 $-\otimes^L-$
- 导出Hom $R\text{Hom}(-,-)$
- 这些满足真正的函子性（而非导出意义下）

---

## 5. 其他重要例子

### 5.1 代数K-理论的∞-范畴

**例 5.1.1** (代数K-理论的 Waldhausen 范畴)

对于Waldhausen范畴 $\mathcal{C}$，可以定义其**代数K-理论谱** $K(\mathcal{C})$。

在∞-范畴框架下，这可以描述为：
$$K(\mathcal{C}) = \Omega^\infty|N_\bullet w S_\bullet \mathcal{C}|$$
其中 $S_\bullet$ 是Waldhausen的$S$-构造。

**例 5.1.2** (非交换 motive)

Tabuada等人的工作：使用∞-范畴定义非交换 motive：
$$\mathcal{M}_{\text{dg}} = \text{Stab}(\text{Cat}_{\text{dg}}^{\text{perf}})$$

### 5.2 因子化代数与拓扑场论

**例 5.2.1** (因子化代数的∞-范畴)

在拓扑场论中，**因子化代数**自然构成∞-范畴。

**具体例子**：

- 在 $\mathbb{R}^n$ 上，局部常值因子化代数 $\leftrightarrow$ $E_n$-代数
- 这是 Lurie 对拓扑场论的代数描述

### 5.3 导出代数几何

**例 5.3.1** (谱概形)

Lurie的导出代数几何：

- **谱环**：$E_\infty$-环谱
- **谱概形**：局部是仿射的环化∞-topos
- **例子**：导出射影空间 $\mathbb{P}^n_{\text{der}}$

**例 5.3.2** (完美复形)

在概形 $X$ 上，**完美复形**的∞-范畴：
$$\text{Perf}(X) \subset D_\infty(\text{QCoh}(X))$$
这是非交换几何的基本对象。

---

## 6. 计算技术

### 6.1 同伦极限与余极限

**例 6.1.1** (同伦拉回)

在拟范畴中，拉回是**同伦拉回**：

给定 $A \to C \leftarrow B$，同伦拉回是：
$$A \times_C^h B = A \times_C C^I \times_C B$$
其中 $C^I = \text{Map}(I, C)$ 是路径空间。

**具体计算**：

在拓扑空间情形，这对应于同伦纤维积。

### 6.2 局部化

**例 6.2.1** (Dwyer-Kan局部化)

给定范畴 $\mathcal{C}$ 和态射子类 $W$，Dwyer-Kan局部化 $\mathcal{C}[W^{-1}]$ 是一个拟范畴，满足泛性质。

**关键例子**：
$$\text{Top}[\text{WE}^{-1}] \simeq \infty\text{-}\mathbf{Gpd}$$
其中 WE 是弱等价。

---

## 参考文献

1. Lurie, J. "Higher Topos Theory", Annals of Math Studies 170
2. Lurie, J. "Higher Algebra"
3. Riehl, E., Verity, D. "Elements of ∞-Category Theory"
4. Cisinski, D-C. "Higher Categories and Homotopical Algebra"
5. Goerss, P., Jardine, J. "Simplicial Homotopy Theory"
