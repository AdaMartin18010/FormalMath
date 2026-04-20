---
msc_primary: 00A99
习题编号: TOP-118
学科: 拓扑
知识点: 拓扑-motivic同伦
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Motivic 同伦论

## 题目

**(a)** 定义 motivic 稳定同伦范畴 $\mathbf{SH}(k)$。

**(b)** 证明 motivic Adams 谱序列及其收敛性。

**(c)** 讨论 motivic 同伦与代数 K-理论的关系。

## 解答

### (a) Motivic 稳定同伦范畴的定义

**不稳定 motivic 同伦范畴 $\mathbf{H}(k)$**：

Morel-Voevodsky（1999）构造了代数簇的 $\mathbb{A}^1$-同伦论。出发点是对光滑 $k$-概形 $Sm/k$ 上的 Nisnevich 层进行局部化。

**Nisnevich 拓扑**：比 Zariski 细但比 étale 粗的 Grothendieck 拓扑。覆盖 $\{U_i \to X\}$ 满足：
1. 集合论覆盖：$\bigcup_i U_i \to X$ 是满射
2. 对任意 $x \in X$，存在 $i$ 和 $u \in U_i$ 映到 $x$，且剩余域扩张 $k(x) \to k(u)$ 是纯不可分的

Nisnevich 拓扑的关键性质：**Mayer-Vietoris** 对 Zariski 开覆盖成立，且** noetherian 归纳**有效。

**$\mathbb{A}^1$-局部化**：在单纯 Nisnevich 层的同伦范畴中，将投影 $X \times \mathbb{A}^1 \to X$ 强制为弱等价。形式地，$\mathbf{H}(k)$ 是单纯层范畴关于 $\mathbb{A}^1$-局部等价局部化的结果。

**Motivic 球面（Motivic Spheres）**：

在 $\mathbf{H}(k)$ 中，有两个基本的"圆"：
- **拓扑圆**：$S^{1,0} = S^1$（通常的单纯圆）
- **Tate 圆**：$S^{1,1} = \mathbb{G}_m = \mathbb{A}^1 \setminus \{0\}$

一般 motivic 球面：
$$S^{p,q} = (S^1)^{\wedge(p-q)} \wedge (\mathbb{G}_m)^{\wedge q}, \quad p \geq q$$

**Motivic 稳定同伦范畴 $\mathbf{SH}(k)$**：

对 motivic 谱 $E = (E_n)_{n \geq 0}$，$E_n \in \mathbf{H}(k)$，带 bonding maps：
$$S^{2,1} \wedge E_n \to E_{n+1}$$

其中 $S^{2,1} = \mathbb{P}^1$（在 $\mathbf{H}(k)$ 中 $S^{2,1} \simeq S^{1,1} \wedge S^{1,0}$）。

$\mathbf{SH}(k)$ 是 motivic 谱的范畴，态射由映射锥的归纳极限给出：
$$[E, F]_{\mathbf{SH}(k)} = \varinjlim_n [S^{2n,n} \wedge E_n, F_n]_{\mathbf{H}(k)}$$

**Motivic 同伦群**：
$$\pi_{p,q}(E) = [S^{p,q}, E]_{\mathbf{SH}(k)}$$

**与经典拓扑同伦的关系**：
- 对 $k = \mathbb{C}$，复实现函子 $R_{\mathbb{C}}: \mathbf{SH}(\mathbb{C}) \to \mathbf{SH}^{\text{top}}$ 将 $S^{p,q} \mapsto S^p$（拓扑 $p$-球）。
- 对 $k = \mathbb{R}$，实实现给出 $S^{p,q} \mapsto S^{p-q}$（通常球）。

### (b) Motivic Adams 谱序列

**Motivic Steenrod 代数 $\mathcal{A}^{*,*}$**：

对特征 $\neq 2$ 的域 $k$，Voevodsky 定义了 motivic 上同调 $H^{*,*}(X, \mathbb{Z}/2)$ 上的 Steenrod 运算：
$$Sq^{2i}: H^{p,q}(X, \mathbb{Z}/2) \to H^{p+2i, q+i}(X, \mathbb{Z}/2)$$

**关键区别**：运算有双次 $(2i, i)$，反映 motivic 上同调的权（Tate twist）。

**定理（Voevodsky）**：$\mathcal{A}^{*,*} = \mathcal{A}^{*,*}(k, \mathbb{Z}/2)$ 作为 $\mathbb{F}_2[\tau]$-代数，其中 $\tau \in H^{0,1}(\text{Spec}(k), \mathbb{F}_2) \cong \mu_2(k)$，由 $Sq^{2^i}$ 生成，带有与拓扑 Steenrod 代数类似的 Adem 关系（但含权移位）。

**Motivic Adams 谱序列**：对 $X \in \mathbf{SH}(k)$，有谱序列：
$$E_2^{s,t,u} = \text{Ext}_{\mathcal{A}^{*,*}}^{s,t,u}(H^{*,*}(X, \mathbb{F}_2), H^{*,*}(S^{0,0}, \mathbb{F}_2)) \Rightarrow \pi_{t-s,u}(X)_2^\wedge$$

其中 $s$ 是 Adams filtration，$t$ 是拓扑度，$u$ 是权。

**收敛性**：在适当的完备性条件下（如 $X$ 是有限型 cellular 谱），motivic Adams 谱序列收敛到 2-完备 motivic 同伦群。

**Milnor 猜想中的应用**：

**定理（Voevodsky, 1996-2001）**：$K_n^M(k)/2 \cong H^n(k, \mu_2^{\otimes n})$。

Voevodsky 的证明策略：
1. 构造 motivic Eilenberg-MacLane 谱 $H\mathbb{Z}/2$，其上同调为 motivic 上同调。
2. 计算 $H^{*,*}(H\mathbb{Z}/2, \mathbb{F}_2)$，证明其作为 $\mathcal{A}^{*,*}$-模是自由模（或恰当扭曲的）。
3. 通过 motivic Adams 谱序列计算 $\pi_{*,*}(S^{0,0})$，识别 Milnor K-理论为特定同伦群。

**Bloch-Kato 猜想（Voevodsky-Rost）**：
对一般 $\ell$（非 2 的素数），类似的 motivic Steenrod 代数和 Adams 谱序列给出：
$$K_n^M(k)/\ell \cong H^n_{\text{ét}}(k, \mu_\ell^{\otimes n})$$
这是 Voevodsky 获 Fields 奖的核心工作。

### (c) Motivic 同伦与代数 K-理论

**代数 K-理论的谱表示**：在 motivic 同伦论中，代数 K-理论由 **KGL 谱**（K-theory Grassmannian spectrum）表示：
$$KGL_n = \mathbb{Z} \times BGL$$
（更精确地，由代数 K-理论的 $\mathbb{P}^1$-谱给出）。

对 $X \in Sm/k$：
$$K_i(X) = \pi_{i,0}(KGL \wedge X_+)$$

**Bott 周期性**：在 motivic 稳定同伦中，存在 Bott 元 $\beta \in \pi_{2,1}(KGL)$（对应于 $\mathbb{P}^1$ 上的约化典范丛）。乘法给出周期性：
$$KGL \simeq \bigvee_{n \in \mathbb{Z}} \Sigma^{2n,n} kgl$$
其中 $kgl$ 是 connective K-理论谱（$\pi_{i,0}(kgl) = K_i$，$i \geq 0$）。

**Bloch-Lichtenbaum 谱序列**：
$$E_2^{p,q} = H^{p-q}_{\mathcal{M}}(X, \mathbb{Z}(-q)) \Rightarrow K_{-p-q}(X)$$

这是从 motivic 上同调到代数 K-理论的谱序列。在 motivic 同伦论框架下，这由 KGL 的 motivic Postnikov 塔（或 slice filtration）给出：
$$E_2^{p,q} = \pi_{-p-q,0}(s_q(KGL) \wedge X_+) \Rightarrow K_{-p-q}(X)$$

其中 $s_q(KGL)$ 是 KGL 的第 $q$ 个 slice。Voevodsky 猜想（后被证明）：$s_q(KGL) \simeq \Sigma^{2q,q} H\mathbb{Z}$，即 slices 是 motivic Eilenberg-MacLane 谱的 Tate  twist。

**现代发展**：
- **$\eta$-完备 motivic 同伦**（Andrews-Miller 等）：研究 $\eta \in \pi_{1,1}(S^{0,0})$（Hopf 映射的 motivic 类比）的可逆性。
- **étale motivic 同伦**：Bachmann 证明 $L_{\text{ét}}\mathbf{SH}(k) \cong \mathbf{SH}_{\text{ét}}(k)$，与 étale K-理论等价。

**常见错误**：
- **Motivic 双次混淆**：$\pi_{p,q}$ 中 $p$ 是拓扑度（cohomological degree），$q$ 是权（Tate twist）。Chow 群 $CH^q(X)$ 对应 $H^{2q,q}(X, \mathbb{Z})$。
- **$\tau$ 的可逆性**：在 $\mathbf{SH}(\mathbb{C})$ 中，$\tau$ 可逆给出拓扑稳定同伦范畴；在 $\mathbf{SH}(\mathbb{R})$ 中 $\tau$ 部分可逆，反映 Galois 作用。
- **Motivic 球的"维数"**：$S^{p,q}$ 的拓扑维数是 $p$，但 motivic 上同调 $H^{p,q}$ 的权为 $q$。两者不可混淆。

**参考文献**：
- F. Morel, V. Voevodsky, "$\mathbb{A}^1$-homotopy theory of schemes", *Publ. Math. IHÉS* 1999
- V. Voevodsky, "Motivic cohomology with $\mathbb{Z}/2$-coefficients", *Publ. Math. IHÉS* 2003
- M. Hoyois, "The six operations in equivariant motivic homotopy theory", *Adv. Math.* 2017
- T. Bachmann, "$\eta$-periodic motivic stable homotopy theory over fields", 2020
