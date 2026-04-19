---
title: "代数结构"
msc_primary: 20

  - 20A05
msc_secondary: ['13A99', '16D99', '12F99']
processed_at: '2026-04-05'
references:
  textbooks:
    - id: artin_algebra
      type: textbook
      title: Algebra
      authors:
      - Michael Artin
      publisher: Pearson
      edition: 2nd
      year: 2011
      isbn: 978-0132413770
      msc: 16-01
      chapters: 
      url: ~
    - id: strang_la
      type: textbook
      title: Introduction to Linear Algebra
      authors:
      - Gilbert Strang
      publisher: Wellesley-Cambridge Press
      edition: 5th
      year: 2016
      isbn: 978-0980232776
      msc: 15-01
      chapters: 
      url: ~
    - id: dummit_foote_aa
      type: textbook
      title: Abstract Algebra
      authors:
      - David S. Dummit
      - Richard M. Foote
      publisher: Wiley
      edition: 3rd
      year: 2003
      isbn: 978-0471433347
      msc: 13-01
      chapters: 
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 代数结构 (Algebraic Structures)

**最后更新**: 2026年4月5日  
**MSC分类**: 20-00 (群论), 13-00 (环论), 16-00 (结合环), 12-00 (域论)

---

## 1. 引言

代数结构是现代数学的核心支柱，研究具有运算的集合及其性质。从群的抽象对称性到环的算术结构，从域的代数封闭性到模的线性作用，代数结构为整个数学提供了统一的语言和强有力的工具。

---

## 2. 群论 (Group Theory)

### 2.1 基本定义

**定义 2.1** (群): 群 $(G, \cdot)$ 是集合 $G$ 配备二元运算 $\cdot: G \times G \to G$，满足：

1. **结合律**: $(ab)c = a(bc)$, $\forall a, b, c \in G$
2. **单位元**: $\exists e \in G$ 使得 $ea = ae = a$, $\forall a \in G$
3. **逆元**: $\forall a \in G, \exists a^{-1} \in G$ 使得 $aa^{-1} = a^{-1}a = e$

**定义 2.2** (阿贝尔群): 若群 $G$ 满足交换律 $ab = ba$，则称 $G$ 为阿贝尔群。

**定义 2.3** (子群): 子集 $H \subseteq G$ 是子群，若 $H$ 在 $G$ 的运算下成群，记作 $H \leq G$。

**定理 2.1** (子群判别法): 非空子集 $H \subseteq G$ 是子群当且仅当：
$$\forall a, b \in H, ab^{-1} \in H$$

---

### 2.2 群同态与同构

**定义 2.4** (群同态): 映射 $\varphi: G \to H$ 是群同态，若：
$$\varphi(ab) = \varphi(a)\varphi(b), \quad \forall a, b \in G$$

**定义 2.5** (核与像):
- 核: $\ker \varphi = \{g \in G : \varphi(g) = e_H\}$
- 像: $\operatorname{im} \varphi = \{\varphi(g) : g \in G\}$

**定理 2.2** (同态基本定理): 设 $\varphi: G \to H$ 是群同态，则：
$$G / \ker \varphi \cong \operatorname{im} \varphi$$

**证明**: 定义 $\bar{\varphi}: G/\ker\varphi \to \operatorname{im}\varphi$ 为 $\bar{\varphi}(gK) = \varphi(g)$。
- **良定性**: 若 $gK = hK$，则 $h^{-1}g \in K$，故 $\varphi(h^{-1}g) = e$，即 $\varphi(g) = \varphi(h)$
- **同态性**: $\bar{\varphi}(gK \cdot hK) = \bar{\varphi}(ghK) = \varphi(gh) = \varphi(g)\varphi(h) = \bar{\varphi}(gK)\bar{\varphi}(hK)$
- **双射**: 显然满射；若 $\bar{\varphi}(gK) = e$，则 $g \in K$，故 $gK = K$（单射）$\square$

---

### 2.3 循环群与置换群

**定义 2.6** (循环群): 群 $G$ 是循环群，若 $\exists g \in G$ 使得 $G = \langle g \rangle = \{g^n : n \in \mathbb{Z}\}$。

**定理 2.3**: 无限循环群同构于 $(\mathbb{Z}, +)$；$n$ 阶循环群同构于 $(\mathbb{Z}_n, +)$。

**定义 2.7** (对称群): $n$ 元集合上的所有置换构成的群称为对称群 $S_n$，阶为 $n!$。

**定理 2.4** (Cayley定理): 每个群都同构于某个对称群的子群。

---

## 3. 环论 (Ring Theory)

### 3.1 基本定义

**定义 3.1** (环): 环 $(R, +, \cdot)$ 是集合 $R$ 配备加法和乘法，满足：
1. $(R, +)$ 是阿贝尔群
2. 乘法结合律: $(ab)c = a(bc)$
3. 分配律: $a(b+c) = ab + ac$, $(a+b)c = ac + bc$

**定义 3.2** (交换环): 若乘法可交换，则称 $R$ 为交换环。

**定义 3.3** (含幺环): 若存在乘法单位元 $1 \in R$ 使得 $1a = a1 = a$，则称 $R$ 为含幺环。

**定义 3.4** (整环): 交换含幺环 $R$ 是整环，若 $1 \neq 0$ 且无零因子：
$$ab = 0 \Rightarrow a = 0 \lor b = 0$$

---

### 3.2 理想与商环

**定义 3.5** (理想): 子集 $I \subseteq R$ 是理想，若：
1. $(I, +)$ 是 $(R, +)$ 的子群
2. 吸收性: $\forall r \in R, a \in I, ra \in I$ 且 $ar \in I$

**定义 3.6** (商环): 理想 $I$ 确定商环 $R/I = \{a + I : a \in R\}$，运算为：
- $(a + I) + (b + I) = (a + b) + I$
- $(a + I)(b + I) = ab + I$

**定理 3.1** (环同态基本定理): 设 $\varphi: R \to S$ 是环同态，则：
$$R / \ker \varphi \cong \operatorname{im} \varphi$$

---

### 3.3 主理想整环与唯一分解

**定义 3.7** (主理想整环/PID): 整环 $R$ 是PID，若每个理想都是主理想 $I = (a) = Ra$。

**定义 3.8** (唯一分解整环/UFD): 整环 $R$ 是UFD，若每个非零非单位元可唯一分解为不可约元的乘积（在相伴意义下）。

**定理 3.2**: 每个PID都是UFD。

**定理 3.3** (Bezout等式): 在PID中，设 $d = \gcd(a, b)$，则存在 $x, y \in R$ 使得：
$$ax + by = d$$

---

## 4. 域论 (Field Theory)

### 4.1 基本定义

**定义 4.1** (域): 域 $(F, +, \cdot)$ 是交换含幺环，且每个非零元都有乘法逆元。

**定义 4.2** (域的特征): 域 $F$ 的特征是最小正整数 $p$ 使得 $p \cdot 1 = 0$，或0（若不存在这样的 $p$）。

**定理 4.1**: 域的特征为0或素数 $p$。

---

### 4.2 域扩张

**定义 4.3** (域扩张): 若 $F \subseteq E$ 是子域，则称 $E/F$ 为域扩张。

**定义 4.4** (代数元与超越元): 设 $E/F$ 是域扩张，$\alpha \in E$：
- 若存在非零多项式 $f(x) \in F[x]$ 使得 $f(\alpha) = 0$，则称 $\alpha$ 在 $F$ 上代数
- 否则称 $\alpha$ 在 $F$ 上超越

**定义 4.5** (扩张次数): 扩张 $E/F$ 的次数定义为：
$$[E : F] = \dim_F E$$

**定理 4.2** (塔律): 设 $F \subseteq E \subseteq K$，则：
$$[K : F] = [K : E][E : F]$$

---

### 4.3 代数闭包与分裂域

**定义 4.6** (代数闭域): 域 $F$ 是代数闭域，若每个非常数多项式 $f(x) \in F[x]$ 在 $F$ 中有根。

**定理 4.3** (代数基本定理): 复数域 $\mathbb{C}$ 是代数闭域。

**定义 4.7** (多项式的分裂域): $f(x) \in F[x]$ 的分裂域是包含 $f$ 所有根的最小域扩张。

**定理 4.4**: 任意多项式 $f(x) \in F[x]$ 的分裂域存在且在 $F$-同构意义下唯一。

---

## 5. 模论基础 (Module Theory)

### 5.1 基本定义

**定义 5.1** (模): 设 $R$ 是环，左 $R$-模是阿贝尔群 $(M, +)$ 配备标量乘法 $R \times M \to M$，满足：
1. $r(m + n) = rm + rn$
2. $(r + s)m = rm + sm$
3. $(rs)m = r(sm)$
4. $1m = m$（若 $R$ 含幺）

**定义 5.2** (子模): 子集 $N \subseteq M$ 是子模，若 $N$ 在 $R$-作用下封闭。

**定理 5.1** (模同态基本定理): 同态 $\varphi: M \to N$ 满足 $M/\ker\varphi \cong \operatorname{im}\varphi$。

---

## 6. 目录结构

```
docs/02-代数结构/
├── 00-README.md                    # 本文件
├── 01-群论/
│   ├── 01-群的基本概念.md
│   ├── 02-子群与陪集.md
│   ├── 03-同态与同构.md
│   ├── 04-群作用.md
│   ├── 05-Sylow定理.md
│   └── 06-阿贝尔群结构.md
├── 02-环论/
│   ├── 01-环的定义与性质.md
│   ├── 02-理想与商环.md
│   ├── 03-多项式环.md
│   └── 04-唯一分解整环.md
├── 03-域论/
│   ├── 01-域的基本性质.md
│   ├── 02-域扩张.md
│   ├── 03-伽罗瓦理论.md
│   └── 04-有限域.md
├── 04-模论/
│   ├── 01-模的定义.md
│   └── 02-自由模与直和分解.md
└── 02-核心理论/                    # 高级主题
    ├── 交换代数/
    ├── 同调代数深化-扩展/
    ├── 表示论/
    └── 代数几何/
```

---

## 7. 学习路径

### 7.1 基础路径
**群论基础** → **环论基础** → **域论基础** → **模论入门**

### 7.2 进阶路径
- **群表示论**: 群论 + 线性代数
- **伽罗瓦理论**: 域论 + 群论
- **代数几何**: 交换代数 + 几何直观
- **同调代数**: 模论 + 范畴论

---

## 8. 核心定理索引

| 定理 | 领域 | 重要性 | 文档位置 |
|------|------|--------|----------|
| Lagrange定理 | 群论 | ⭐⭐⭐ | 01-群论/02-子群与陪集.md |
| Sylow定理 | 群论 | ⭐⭐⭐⭐ | 01-群论/05-Sylow定理.md |
| 同态基本定理 | 群/环/模 | ⭐⭐⭐⭐⭐ | 各基础文档 |
| 理想对应定理 | 环论 | ⭐⭐⭐⭐ | 02-环论/02-理想与商环.md |
| 代数基本定理 | 域论 | ⭐⭐⭐⭐⭐ | 03-域论/01-域的基本性质.md |
| Galois基本定理 | 域论 | ⭐⭐⭐⭐⭐ | 03-域论/03-伽罗瓦理论.md |

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
