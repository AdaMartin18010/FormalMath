---
msc_primary: 18B99
msc_secondary:
  - 18A40
  - 18F10
  - 55U35
  - 03G30
---

# nLab 深度对齐：范畴论与高等数学

nLab 是范畴论与高等数学的协作式 wiki，由 Urs Schreiber 等人维护，涵盖范畴论、高阶范畴、Topos 理论、同伦类型论与 ∞-范畴等前沿领域。本节对齐 nLab 的核心主题与 FormalMath 的内容，并提供严格的数学材料。

## 1. 范畴论核心概念

### 1.1 范畴的基本定义

**定义 1.1（范畴）**. 范畴 $\mathcal{C}$ 由以下资料组成：

- 对象类 $\operatorname{Ob}(\mathcal{C})$；
- 对任意对象 $X, Y \in \operatorname{Ob}(\mathcal{C})$，态射集 $\operatorname{Hom}_{\mathcal{C}}(X, Y)$；
- 复合运算 $\circ: \operatorname{Hom}(Y, Z) \times \operatorname{Hom}(X, Y) \to \operatorname{Hom}(X, Z)$，满足结合律与单位元公理。

**例子 1.2**.

- $\mathbf{Set}$：集合与映射；
- $\mathbf{Grp}$：群与群同态；
- $\mathbf{Top}$：拓扑空间与连续映射；
- 对环 $R$，$R\text{-}\mathbf{Mod}$：左 $R$-模与模同态。

### 1.2 伴随函子

**定义 1.3（伴随）**. 函子 $F: \mathcal{C} \to \mathcal{D}$ 与 $G: \mathcal{D} \to \mathcal{C}$ 伴随（记作 $F \dashv G$），若存在自然同构
$$\mathcal{D}(F(X), Y) \cong \mathcal{C}(X, G(Y))$$
对所有 $X \in \mathcal{C}, Y \in \mathcal{D}$ 成立。

**定理 1.4**. 左伴随保持余极限，右伴随保持极限。

*证明*. 设 $F \dashv G$，$\{X_i\}$ 为 $\mathcal{C}$ 中的图。对任意 $Y \in \mathcal{D}$：
$$\begin{aligned}
\mathcal{D}(F(\operatorname{colim} X_i), Y) &\cong \mathcal{C}(\operatorname{colim} X_i, G(Y)) \\
&\cong \lim \mathcal{C}(X_i, G(Y)) \\
&\cong \lim \mathcal{D}(F(X_i), Y) \\
&\cong \mathcal{D}(\operatorname{colim} F(X_i), Y).
\end{aligned}$$
由 Yoneda 引理，$F(\operatorname{colim} X_i) \cong \operatorname{colim} F(X_i)$。$\square$

### 1.3 高阶范畴

**定义 1.5（2-范畴）**. 2-范畴 $\mathcal{C}$ 包含对象、1-态射和 2-态射，配备水平复合 $\circ$ 与垂直复合 $\cdot$，满足严格的结合律与单位律。

**定义 1.6（∞-范畴的单纯模型）**. 准范畴（quasi-category）是满足内 Kan 条件的单纯集：每个内角 $\Lambda^n_k$（$0 < k < n$）均可填充。

## 2. Topos 理论

### 2.1 Grothendieck Topos

**定义 2.1（Grothendieck Topos）**. Grothendieck topos 是范畴等价于某小范畴 $\mathcal{C}$ 上预层范畴 $\mathbf{PSh}(\mathcal{C})$ 的左正合局部化。

等价地，topos 是满足 Giraud 公理的范畴（见定理 2.2）。Topos 同时推广了拓扑空间上的层范畴与集合论 universe，是几何与逻辑的交汇点。

**定理 2.2（Giraud）**. 范畴 $\mathcal{E}$ 是 Grothendieck topos 当且仅当它满足：
1. $\mathcal{E}$ 完备且余完备；
2. 指数对象存在（局部笛卡尔闭）；
3. 有子对象分类子 $\Omega$；
4. 有小的生成族。

**例子 2.3（集合的 Topos）**. $\mathbf{Set}$ 是最基本的 topos，子对象分类子为 $\Omega = \{0, 1\}$，真值映射 $\top: 1 \to \Omega$ 对应 $1 \mapsto 1$。

**例子 2.4（层 Topos）**. 对拓扑空间 $X$，$\mathbf{Sh}(X)$ 为 $X$ 上的层范畴，是 Grothendieck topos。子对象分类子 $\Omega$ 在开集 $U$ 上的截面为 $U$ 的开子集族。

### 2.2 几何态射

**定义 2.5**. 几何态射 $f: \mathcal{F} \to \mathcal{E}$ 是伴随对 $f^* \dashv f_*$，其中 $f^*: \mathcal{E} \to \mathcal{F}$ 保持有限极限。

几何态射是 topos 之间的"连续映射"，推广了拓扑空间之间的连续映射诱导的层拉回-前推对。

## 3. ∞-范畴与同伦类型论

### 3.1 单纯集与同伦相干

**定义 3.1（Kan 复形）**. Kan 复形是满足所有 Horn 填充条件的单纯集，构成 ∞-群胚的模型：0-单形为对象，1-单形为态射，高维单形为高阶同伦。

**定理 3.2（Joyal）**. 准范畴中的映射 $f: X \to Y$ 是等价当且仅当它在同伦范畴 $\mathrm{h}\mathcal{C}$ 中诱导同构，且满足提升性质。

### 3.2 同伦类型论（HoTT）

同伦类型论为 Martin-Löf 类型论赋予同伦论解释：
- 类型 ↔ 空间
- 项 $a: A$ ↔ 点 $a \in A$
- 恒等类型 $\operatorname{Id}_A(a, b)$ ↔ 路径空间
- 公理 K 的否定 ↔ 高阶路径存在

**单值性公理（Univalence Axiom）**. 对宇宙 $\mathcal{U}$，典范映射
$$(A =_{\mathcal{U}} B) \to (A \simeq B)$$
是等价。这意味着同伦等价的类型在逻辑上不可区分。

## 4. 例子与应用

### 4.1 导出范畴

对 Abel 范畴 $\mathcal{A}$，其链复形范畴 $\operatorname{Ch}(\mathcal{A})$ 的导出范畴 $D(\mathcal{A})$ 通过局部化拟同构得到。导出范畴是研究同调代数的自然框架，其中的映射是 roof 图：
$$X \xleftarrow{\sim} Z \to Y.$$

### 4.2 谱序列

**定理 4.1**.  filtered 复形 $(C^\bullet, F)$ 诱导谱序列 $\{E_r^{p,q}\}$，满足
$$E_1^{p,q} = H^{p+q}(F^p C / F^{p+1} C) \Rightarrow H^{p+q}(C).$$

Grothendieck 谱序列：对左正合函子的复合 $F \circ G$，有
$$E_2^{p,q} = R^p F(R^q G(A)) \Rightarrow R^{p+q}(F \circ G)(A).$$

## 5. 交叉引用

- [范畴论](docs/01-基础数学/范畴论-基础.md) — 基础范畴论
- [类型论](docs/01-基础数学/类型论-基础.md) — 依值类型与 ∞-范畴
- [层论](docs/02-代数结构/02-核心理论/代数几何/05-层与上同调-深度版.md) — 层的范畴性质
- [代数几何](docs/02-代数结构/02-核心理论/代数几何/01-代数几何基础.md) — 概形与 topos
- [同伦论](docs/04-几何与拓扑/03-代数拓扑/同伦论基础.md) — Kan 复形与模型范畴

---

**适用**：docs/04-International-Alignment/
