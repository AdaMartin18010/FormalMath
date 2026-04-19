---
msc_primary: 97A99
msc_secondary:
  - 00A99
---

# nLab 深度对齐：范畴论与高等数学

nLab 是范畴论与高等数学的协作式 wiki，由 Urs Schreiber 等人维护。本节对齐 nLab 的核心主题与 FormalMath 的内容，并提供严格的数学材料。

## 1. 范畴论核心概念

### 1.1 伴随函子

**定义 1.1（伴随）**. 函子 $F: \mathcal{C} \to \mathcal{D}$ 与 $G: \mathcal{D} \to \mathcal{C}$ 伴随（$F \dashv G$），若存在自然同构 $\mathcal{D}(F(X), Y) \cong \mathcal{C}(X, G(Y))$。

**定理 1.2**. 左伴随保持余极限，右伴随保持极限。

### 1.2 高阶范畴

**定义 1.3（2-范畴）**. 2-范畴 $\mathcal{C}$ 包含对象、1-态射和2-态射，配备水平与垂直复合。

## 2. Topos 理论

**定义 2.1（Grothendieck Topos）**. Grothendieck topos 是范畴等价于某小范畴上预层范畴的左正合局部化。

**定理 2.2（Giraud）**. 范畴 $\mathcal{E}$ 是 Grothendieck topos 当且仅当它满足：
1. $\mathcal{E}$ 完备且余完备；
2. 指数对象存在；
3. 有子对象分类子；
4. 有小的生成族。

## 3. ∞-范畴

**定义 3.1（准范畴）**. 准范畴（quasi-category）是满足内 Kan 条件的单纯集：每个内角均可填充。

## 4. 例子

### 4.1 例子：集合的 Topos

$\mathbf{Set}$ 是最基本的 topos，子对象分类子为 $\Omega = \{0, 1\}$。

### 4.2 例子：层 Topos

对拓扑空间 $X$，$\mathbf{Sh}(X)$ 为 $X$ 上的层范畴，是 Grothendieck topos。

## 5. 交叉引用

- [范畴论](docs/01-基础数学/范畴论-基础.md) — 基础范畴论
- [类型论](docs/01-基础数学/类型论-基础.md) — 依值类型与 ∞-范畴
- [层论](docs/02-代数结构/02-核心理论/代数几何/05-层与上同调-深度版.md) — 层的范畴性质
- [代数几何](docs/02-代数结构/02-核心理论/代数几何/01-代数几何基础.md) — 概形与 topos

---

**适用**：docs/04-International-Alignment/
