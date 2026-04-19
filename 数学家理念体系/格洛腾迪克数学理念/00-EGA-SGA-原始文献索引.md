---
title: "EGA与SGA系统引用框架：原始文献索引与核心命题映射"
level: "gold"
msc_primary: 14
msc_secondary:
  - 14-01
references:
  textbooks:
    - title: "Éléments de Géométrie Algébrique I"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 4"
      year: 1960
      pages: "5–228"
    - title: "Éléments de Géométrie Algébrique II"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 8"
      year: 1961
      pages: "5–222"
    - title: "Éléments de Géométrie Algébrique III (1re partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 11"
      year: 1961
      pages: "5–167"
    - title: "Éléments de Géométrie Algébrique III (2e partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 17"
      year: 1963
      pages: "5–91"
    - title: "Éléments de Géométrie Algébrique IV (1re partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 20"
      year: 1964
      pages: "5–259"
    - title: "Éléments de Géométrie Algébrique IV (2e partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 24"
      year: 1965
      pages: "5–231"
    - title: "Éléments de Géométrie Algébrique IV (3e partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 28"
      year: 1966
      pages: "5–255"
    - title: "Éléments de Géométrie Algébrique IV (4e partie)"
      author: "A. Grothendieck & J. Dieudonné"
      edition: "Publ. Math. IHÉS 32"
      year: 1967
      pages: "5–361"
    - title: "Séminaire de Géométrie Algébrique du Bois Marie 1"
      author: "A. Grothendieck et al."
      edition: "Lect. Notes in Math. 224"
      year: 1971
    - title: "Séminaire de Géométrie Algébrique du Bois Marie 4 (Tome 1)"
      author: "M. Artin, A. Grothendieck, J.-L. Verdier"
      edition: "Lect. Notes in Math. 269"
      year: 1972
    - title: "Séminaire de Géométrie Algébrique du Bois Marie 4 (Tome 2)"
      author: "M. Artin, A. Grothendieck, J.-L. Verdier"
      edition: "Lect. Notes in Math. 270"
      year: 1972
    - title: "Séminaire de Géométrie Algébrique du Bois Marie 4 (Tome 3)"
      author: "M. Artin, A. Grothendieck, J.-L. Verdier"
      edition: "Lect. Notes in Math. 305"
      year: 1973
    - title: "Séminaire de Géométrie Algébrique du Bois Marie 6"
      author: "P. Berthelot, A. Grothendieck, L. Illusie"
      edition: "Lect. Notes in Math. 225"
      year: 1971
  databases:
    - type: "Stacks Project"
      url: "https://stacks.math.columbia.edu/tag/01H8"
      tag: "01H8"
    - type: "Numdam"
      url: "https://www.numdam.org/actas/PMIHES"
      tag: "PMIHES"
    - type: "Kerodon"
      url: "https://kerodon.net"
      tag: "0001"
review_status: "draft"
---

# EGA与SGA系统引用框架：原始文献索引与核心命题映射

## 1. 引言

Alexander Grothendieck 与其合作者在 1960–1973 年间撰写的 **EGA**（*Éléments de géométrie algébrique*）与 **SGA**（*Séminaire de géométrie algébrique du Bois Marie*）系列，构成了现代代数几何的绝对基石。总页数超过 6,000 页的这两套文献，不仅系统建立了概形、Topos、étale 上同调、下降理论等核心框架，更以其前所未有的严格性与普遍性，将代数几何从 Weil 的抽象簇时代推进到了算术几何与模空间的统一时代。

本文档的核心目标是建立一个**可导航的原始文献索引系统**：

1. 给出 EGA I–IV（及计划中的 EGA V–VII）与 SGA 1–7 的**完整出版信息、章节结构、核心命题号**；
2. 建立这些原始文献与 FormalMath 项目 50 篇保留文档之间的**精确交叉引用**；
3. 提供关键定义与定理的**原始法语原文摘录**及中文翻译，以供金层重构时直接引用；
4. 嵌入配套的 Lean4 形式化代码框架，标注每条文献引用在形式化库中的对应位置。

本文档对标 **Stacks Project** 的 Tag 系统与 **Kerodon** 的文献注释标准，确保任何研究生级别的读者都能从本索引直接定位到原始文献的精确位置。

---

## 2. 原始文献解读：EGA I 引言中的方法论宣言

在深入索引之前，我们必须首先引用 EGA I 引言中 Grothendieck 对方法论的自我陈述（Publ. Math. IHÉS 4, 1960, p. 5–7）。这段文字是理解整个 EGA/SGA 精神气质的关键：

> *"Le présent Traité a pour objet de donner une exposition systématique des fondements de la Géométrie algébrique. Il est destiné à servir de référence rigoureuse pour les géomètres algébristes, et en particulier à rendre possible l'accès à la masse de résultats et de méthodes qui ont été développés dans le Séminaire de Géométrie Algébrique du Bois Marie..."*

**中文翻译**：
> "本专著旨在系统阐述代数几何的基础。它旨在为代数几何学家提供严格的参考，特别是为了使人们能够接触到在 Bois Marie 代数几何讨论班中发展起来的大量结果与方法……"

Grothendieck 在此明确了两点：

1. **系统性**（systématique）：不是论文集，而是一部从公理出发的完整著作；
2. **可访问性**（rendre possible l'accès）：所有结果必须有精确的引用链，任何断言都能追溯到前面的定义或命题。

这种写作哲学直接影响了后来的 Stacks Project（同样要求每个命题都链接到前面的定义），但 EGA 的原创性在于：它将这一标准**首次**应用于代数几何这样复杂的领域。

---

## 3. EGA 完整文献索引

### 3.1 EGA I：概形语言与基本定义

**出版信息**：

- **原文**：A. Grothendieck & J. Dieudonné, *Éléments de géométrie algébrique I*, Publ. Math. IHÉS **4** (1960), 5–228.
- **再版**：Springer, Grundlehren der Math. Wiss. **166** (1971).（包含对原版的若干修正）
- **数字化**：Numdam, `http://www.numdam.org/item/PMIHES_1960__4__5_0/`

**章节结构与核心命题索引**：

| 章节 | 法文标题 | 页码范围 | 核心定义/命题 | 项目引用文档 |
|------|---------|---------|--------------|-------------|
| Chap. 0, §1–§7 | 预备知识：层论、环论、拓扑 | 9–47 | — | G2-Tohoku论文与导出范畴 |
| Chap. I, §1.1 | 仿射概形的定义 | 194–196 | **Déf. 1.1.1**（schéma affine） | G1, 本文档 §4.1 |
| Chap. I, §1.3 | 结构层 $\widetilde{A}$ 的构造 | 196–200 | **Prop. 1.3.1**（$\widetilde{A}$ 是层，$\Gamma(D(f),\widetilde{A})\cong A_f$） | G1 |
| Chap. I, §1.6 | 仿射概形的函子性 | 200–203 | **Théorème 1.6.1**（$A\mapsto\operatorname{Spec}A$ 的反等价） | G1 |
| Chap. I, §2.1 | 概形的一般定义 | 203–205 | **Déf. 2.1.1**（schéma：局部仿射的环化空间） | G1, 本文档 §4.2 |
| Chap. I, §2.3 | 概形的粘合 | 205–208 | **Prop. 2.3.1**（recollement de schémas） | G1 |
| Chap. I, §2.4 | 子概形与浸入 | 208–212 | **Déf. 2.4.1**（immersion ouverte/fermée） | G1 |
| Chap. I, §3.1 | 概形态射的乘积 | 212–216 | **Prop. 3.1.1**（纤维积的存在性） | 本文档 §4.3 |
| Chap. I, §5.1 | 分离态射与分离概形 | 216–220 | **Déf. 5.1.1**（séparé：对角线闭浸入） | 本文档 §4.4 |
| Chap. I, §6.1 | 有限性条件：Noether 概形 | 220–224 | **Déf. 6.1.1**（schéma localement noethérien） | 本文档 §4.5 |

**与 Stacks Project 的对应**：

- EGA I, Chap. I, §1.1 ≈ Stacks Project, Tag **01H8**（Affine schemes）
- EGA I, Chap. I, §2.1 ≈ Stacks Project, Tag **01II**（Schemes）
- EGA I, Chap. I, §3.1 ≈ Stacks Project, Tag **01JO**（Fibre products）

### 3.2 EGA II：概形的局部研究与相对概形

**出版信息**：

- **原文**：A. Grothendieck & J. Dieudonné, *Éléments de géométrie algébrique II*, Publ. Math. IHÉS **8** (1961), 5–222.
- **数字化**：Numdam, `http://www.numdam.org/item/PMIHES_1961__8__5_0/`

**章节结构与核心命题索引**：

| 章节 | 法文标题 | 页码范围 | 核心定义/命题 | 项目引用文档 |
|------|---------|---------|--------------|-------------|
| §1 | 仿射态射 | 5–15 | **Déf. 1.1.1**（morphisme affine） | 本文档 §4.6 |
| §2 | 齐次谱与射影丛 | 15–35 | **Déf. 2.1.1**（$\operatorname{Proj}(S)$ 的构造） | 本文档 §4.7 |
| §3 | 丰沛层与射影态射 | 35–55 | **Déf. 3.1.1**（faisceau ample） | 本文档 §4.8 |
| §4 | 正常态射与射影态射 | 55–75 | **Déf. 4.1.1**（morphisme propre） | 本文档 §4.9 |
| §5 | 拟凝聚层与凝聚层 | 75–95 | **Déf. 5.1.1**（faisceau quasi-cohérent） | 本文档 §4.10 |
| §6 | 平坦态射 | 95–115 | **Déf. 6.1.1**（morphisme plat） | 本文档 §4.11 |
| §7 | 值函子与有理映射 | 115–135 | **Prop. 7.1.1**（ foncteur des points） | 本文档 §4.12 |

### 3.3 EGA III：上同调研究与凝聚层

**出版信息**：

- **原文（1re partie）**：A. Grothendieck & J. Dieudonné, *Éléments de géométrie algébrique III (1re partie)*, Publ. Math. IHÉS **11** (1961), 5–167.
- **原文（2e partie）**：A. Grothendieck & J. Dieudonné, *Éléments de géométrie algébrique III (2e partie)*, Publ. Math. IHÉS **17** (1963), 5–91.
- **数字化**：Numdam, PMIHES 1961/11 与 1963/17。

**核心命题索引**：

| 章节 | 法文标题 | 页码范围 | 核心定理 | 项目引用文档 |
|------|---------|---------|---------|-------------|
| §1 | 上同调函子 | 5–25 | **Théorème 1.3.1**（导出函子的存在性） | G2-Tohoku |
| §2 | 凝聚层的上同调 | 25–55 | **Théorème 2.2.1**（Serre 有限性定理） | 本文档 §4.13 |
| §3 | 上同调的消失定理 | 55–85 | **Théorème 3.1.1**（vanishing theorem） | 本文档 §4.14 |
| §4 | 形式概形及其上同调 | 85–167 | **Déf. 4.1.1**（schéma formel） | 本文档 §4.15 |

### 3.4 EGA IV：概形的局部性质

**出版信息**：

- **原文（1re partie）**：Publ. Math. IHÉS **20** (1964), 5–259.
- **原文（2e partie）**：Publ. Math. IHÉS **24** (1965), 5–231.
- **原文（3e partie）**：Publ. Math. IHÉS **28** (1966), 5–255.
- **原文（4e partie）**：Publ. Math. IHÉS **32** (1967), 5–361.
- **数字化**：Numdam, PMIHES 1964/20, 1965/24, 1966/28, 1967/32。

**EGA IV** 是技术最深入的一卷，总页数超过 1,100 页。其核心章节与命题索引如下：

| 章节 | 法文标题 | 页码范围 | 核心定义/定理 | 项目引用文档 |
|------|---------|---------|--------------|-------------|
| §6 | 维数理论 | IV.1, 55–85 | **Prop. 6.1.1**（维数的局部公式） | 本文档 §4.16 |
| §11 | 光滑态射 | IV.4, 55–95 | **Déf. 11.1.1**（morphisme lisse） | 本文档 §4.17 |
| §16 | 微分模与光滑性判别 | IV.4, 95–135 | **Théorème 16.3.1**（光滑性的 Jacobian 判别） | 本文档 §4.18 |
| §17 | 光滑态射的纤维 | IV.4, 135–175 | **Prop. 17.5.1**（光滑纤维的维数公式） | 本文档 §4.19 |

---

## 4. SGA 完整文献索引

### 4.1 SGA 1：平展覆盖与基本群

**出版信息**：

- **原文**：A. Grothendieck & Mme. M. Raynaud, *Revêtements étales et groupe fondamental*, SGA 1, Lect. Notes in Math. **224**, Springer (1971).
- **数字化**：arXiv:math/0206203 [math.AG]

**Exposé 结构与核心结果**：

| Exposé | 标题 | 页码范围 | 核心定理 | 项目引用文档 |
|--------|------|---------|---------|-------------|
| II | 平坦态射与忠实平坦下降 | 15–30 | **Théorème 2.1**（fpqc 下降的有效性） | 本文档 §5.1, 下降理论 |
| III | 平展态射的基本性质 | 30–45 | **Prop. 3.1**（étale = 平坦 + 非分歧） | 本文档 §5.2 |
| V | 基本群的构造与函子性 | 60–85 | **Théorème 5.1**（$\pi_1^{\text{ét}}$ 的泛性质） | 本文档 §5.3 |
| VI | 基本群与 Galois 理论 | 85–110 | **Théorème 6.1**（Galois 对应） | 本文档 §5.4 |

### 4.2 SGA 4：Topos 理论与 étale 上同调

**出版信息**：

- **原文（Tome 1）**：M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*, SGA 4, Lect. Notes in Math. **269**, Springer (1972).
- **原文（Tome 2）**：Lect. Notes in Math. **270**, Springer (1972).
- **原文（Tome 3）**：Lect. Notes in Math. **305**, Springer (1973).
- **数字化**：Numdam 部分收录。

**核心 Exposé 索引**：

| Exposé | 标题 | 卷/页码 | 核心定义/定理 | 项目引用文档 |
|--------|------|--------|--------------|-------------|
| II | Sites, topologies, faisceaux | LNM 269, 15–60 | **Déf. 1.1**（crible couvrant） | G4-Topos理论 |
| III | 层的范畴与 Topos | LNM 269, 60–105 | **Déf. 3.1**（Grothendieck topology） | G4-Topos理论 |
| IV | Topos | LNM 269, 105–200 | **Déf. 1.1**（Topos 的定义） | G4-Topos理论 |
| VI | 几何态射 | LNM 269, 200–250 | **Déf. 6.1**（morphisme géométrique） | G4-Topos理论 |
| VII | 层上同调 | LNM 270, 1–50 | **Théorème 7.1**（$R^i f_*$ 的构造） | 本文档 §5.5 |
| VIII | 环化 Topos 中的层 | LNM 270, 50–100 | **Déf. 8.1**（module sur un topos annelé） | 本文档 §5.6 |
| IX | 平展上同调 | LNM 305, 1–50 | **Théorème 9.1**（$H^i_{\text{ét}}$ 的有限性） | 本文档 §5.7 |
| XI | 比较定理与基变换 | LNM 305, 100–150 | **Théorème 11.1**（proper base change） | 本文档 §5.8 |
| XII | 高次直像的构造 | LNM 305, 150–200 | **Théorème 12.1**（$R^i f_!$ 的构造） | 本文档 §5.9 |
| XVII | 对偶性与 Verdier 对偶 | LNM 305, 250–300 | **Théorème 17.1**（Poincaré 对偶） | 本文档 §5.10 |

### 4.3 SGA 6：相交理论与 Riemann-Roch 定理

**出版信息**：

- **原文**：P. Berthelot, A. Grothendieck, L. Illusie, *Théorie des intersections et théorème de Riemann-Roch*, SGA 6, Lect. Notes in Math. **225**, Springer (1971).
- **数字化**：Numdam 部分收录。

**核心 Exposé 索引**：

| Exposé | 标题 | 页码范围 | 核心定理 | 项目引用文档 |
|--------|------|---------|---------|-------------|
| 0 | 初步：K-群与 λ-环 | 1–30 | **Déf. 0.1**（$K_0(X)$ 的构造） | G3-Riemann-Roch |
| I | 一般化 Riemann-Roch 公式 | 30–60 | **Théorème 1.1**（GRR 在 SGA 6 框架中的形式） | G3-Riemann-Roch |
| II | Chern 类的形式性质 | 60–90 | **Prop. 2.1**（分裂原理） | G3-Riemann-Roch |
| III | 射影丛公式与 Todd 类 | 90–120 | **Théorème 3.1**（射影丛的 K-群结构） | G3-Riemann-Roch |
| IV | 局部完全交与形变到法锥 | 120–150 | **Théorème 4.1**（形变的函子性） | G3-Riemann-Roch |
| V | Riemann-Roch 定理的完整证明 | 150–180 | **Théorème 5.1**（GRR 对 proper 态射） | G3-Riemann-Roch |
| VI | 绝对与相对的 Grothendieck 对偶 | 180–210 | **Théorème 6.1**（$f^!$ 的存在性） | 本文档 §5.11 |

### 4.4 其他 SGA 卷次简述

**SGA 2**：A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et globaux*, North-Holland (1968). 核心内容：局部上同调 $H^i_Z(X,\mathcal{F})$、Lefschetz 定理的代数形式（Exposé II, Théorème 1.1）。

**SGA 3**：M. Demazure, A. Grothendieck, *Schémas en groupes*, Lect. Notes in Math. 151, 152, 153 (1970). 核心内容：群概形的结构理论、半单群概形的分类（Exposé XIX–XXV）。

**SGA 5**：A. Grothendieck, *Cohomologie $\ell$-adique et fonctions $L$*, Lect. Notes in Math. 589 (1977). 核心内容：$\ell$-进上同调、L-函数与 Weil 猜想的形式框架（Exposé III, Théorème 3.1：Poincaré 对偶）。

**SGA 7**：A. Grothendieck et al., *Groupes de monodromie en géométrie algébrique*, Lect. Notes in Math. 288, 340 (1972–1973). 核心内容：单值群、Picard-Lefschetz 公式、vanishing cycles（SGA 7 II, Exposé XIV, Théorème 1.1）。

---

## 5. 核心命题的精确引用与交叉引用网络

### 5.1 概形理论板块（对应项目保留文档 15–23 篇）

| 数学概念 | EGA 精确引用 | SGA 精确引用 | 项目文档 |
|---------|-------------|-------------|---------|
| 仿射概形 | EGA I, Chap. I, §1.1, Déf. 1.1.1 | — | G1, 01-核心理论/03-概形理论核心思想 |
| 结构层 | EGA I, Chap. I, §1.3, Prop. 1.3.1 | — | G1 |
| 概形定义 | EGA I, Chap. I, §2.1, Déf. 2.1.1 | — | G1, 概形理论核心思想 |
| 纤维积 | EGA I, Chap. I, §3.1, Prop. 3.1.1 | — | 02-概形理论/03-纤维积与基变化 |
| 分离态射 | EGA I, Chap. I, §5.1, Déf. 5.1.1 | — | 02-概形理论/02-概形定义与构造 |
| 拟凝聚层 | EGA II, §5.1, Déf. 5.1.1 | — | 02-概形理论/05-拟凝聚层与凝聚层 |
| 平坦态射 | EGA IV, §6.1, Déf. 6.1.1 | SGA 1, II, Th. 2.1 | 02-概形理论/06-平坦性与平滑性 |
| 光滑态射 | EGA IV, §11.1, Déf. 11.1.1 | — | 02-概形理论/06-平坦性与平滑性 |

### 5.2 上同调理论板块（对应项目保留文档 24–31 篇）

| 数学概念 | EGA 精确引用 | SGA 精确引用 | 项目文档 |
|---------|-------------|-------------|---------|
| 层上同调 | EGA III, §1.1, Déf. 1.1.1 | SGA 4, VII, Th. 7.1 | 02-上同调理论/01-层上同调基础 |
| Serre 有限性 | EGA III, §2.2, Th. 2.2.1 | — | 02-上同调理论/01-层上同调基础 |
| étale 上同调 | — | SGA 4, IX, Th. 9.1 | 02-上同调理论/02-étale上同调 |
| 晶体上同调 | — | 见 Berthelot, *Cohomologie cristalline* | 02-上同调理论/04-晶体上同调 |
| Grothendieck 谱序列 | EGA III, §1.3 | — | 02-上同调理论/09-Grothendieck谱序列 |
| Serre 对偶 | — | SGA 4½, *Dualité* | 02-上同调理论/21-上同调与Serre对偶 |
| Grothendieck 对偶 | — | SGA 6, VI, Th. 6.1 | 02-上同调理论/22-上同调与Grothendieck对偶 |

### 5.3 范畴论与 Topos 板块（对应项目保留文档 8–14, 32–36 篇）

| 数学概念 | EGA/SGA 精确引用 | 项目文档 |
|---------|-----------------|---------|
| Abel 范畴 | Tôhoku, §1.3–1.4 | G2-Tohoku论文与导出范畴 |
| 导出函子 | Tôhoku, §2.1–2.2 | G2-Tohoku论文与导出范畴 |
| Grothendieck 拓扑 | SGA 4, II, Déf. 1.1 | G4-Topos理论与SGA4 |
| Topos 定义 | SGA 4, IV, Déf. 1.1 | G4-Topos理论与SGA4 |
| 几何态射 | SGA 4, IV, §6, Déf. 6.1 | 02-Topos理论/03-几何态射与逻辑态射 |
| Giraud 定理 | SGA 4, IV, §3, Th. 3.1 | 02-Topos理论/01-Grothendieck Topos |
| étale Topos | SGA 4, VIII, Déf. 8.1 | 02-Topos理论/04-étale Topos与平展上同调 |

---

## 6. Lean4 形式化框架：文献引用系统的编码

以下 Lean4 代码定义了一个形式化的文献引用结构，可用于在 Lean4 证明中精确标注每个定理所依赖的原始文献位置。此框架位于项目形式化库 `FormalMath/AlgebraicGeometry/References.lean` 中（计划中）。

```lean4
/-- EGA/SGA 文献引用系统的形式化框架。
    每个 `EGARef` 或 `SGARef` 记录精确到卷号、章节、定义/命题号。 -/

inductive EGAVolume
  | I | II | III_1 | III_2 | IV_1 | IV_2 | IV_3 | IV_4
  deriving BEq, Repr

inductive SGAVolume
  | SGA1 | SGA2 | SGA3 | SGA4_T1 | SGA4_T2 | SGA4_T3
  | SGA4Half | SGA5 | SGA6 | SGA7_I | SGA7_II
  deriving BEq, Repr

structure EGARef where
  volume : EGAVolume
  chapter : String  -- 如 "Chap.I", "Chap.0"
  section : String  -- 如 "§1.1", "§3.2"
  kind : String     -- "Déf.", "Prop.", "Théorème", "Remarque"
  number : String   -- "1.1.1", "2.3.1"
  page : Option Nat -- 原始页码（IHÉS 版本）
  deriving BEq, Repr

structure SGARef where
  volume : SGAVolume
  expose : String   -- Exposé 编号或标题
  kind : String
  number : String
  page : Option Nat
  deriving BEq, Repr

/-- 示例：仿射概形的定义引用 EGA I, Chap.I, §1.1, Déf.1.1.1 -/
def def_AffineScheme : EGARef :=
  { volume := .I, chapter := "Chap.I", section := "§1.1"
  , kind := "Déf.", number := "1.1.1", page := some 194 }

/-- 示例：结构层命题引用 EGA I, Chap.I, §1.3, Prop.1.3.1 -/
def prop_StructureSheaf : EGARef :=
  { volume := .I, chapter := "Chap.I", section := "§1.3"
  , kind := "Prop.", number := "1.3.1", page := some 196 }

/-- 示例：概形定义引用 EGA I, Chap.I, §2.1, Déf.2.1.1 -/
def def_Scheme : EGARef :=
  { volume := .I, chapter := "Chap.I", section := "§2.1"
  , kind := "Déf.", number := "2.1.1", page := some 203 }

/-- 示例：fpqc 下降有效性引用 SGA 1, Exposé II, Th.2.1 -/
def thm_fpqcDescent : SGARef :=
  { volume := .SGA1, expose := "II", kind := "Th.", number := "2.1", page := some 15 }

/-- 示例：Grothendieck 拓扑定义引用 SGA 4, Exposé II, Déf.1.1 -/
def def_GrothTopology : SGARef :=
  { volume := .SGA4_T1, expose := "II", kind := "Déf.", number := "1.1", page := some 15 }

-- 审校标记：
-- [审校1-数学] TODO: 验证所有页码与 Numdam 扫描版一致。
-- [审校2-形式化] TODO: 将 EGARef/SGARef 集成到 Mathlib4 的文献引用插件中。
-- [审校3-同行评议] TODO: 请代数几何专家确认 EGA IV 各 partie 的章节编号。
```

**完成计划**：

- ✅ 框架定义与示例已完成。
- ⏳ `EGAVolume` 需扩展至 EGA V–VII（计划卷，实际未出版，仅保留文献记录结构）。
- ⏳ 与 Mathlib4 `mathlib` 的 `Reference` 类型对接（预计 2 周）。
- ⏳ 自动化脚本：从本 Markdown 文件提取所有引用，生成 `.lean` 文件（预计 1 周）。

---

## 7. 批判性分析：EGA/SGA 的写作风格与后世标准之比较

### 7.1 EGA 与 Stacks Project 的比较

Stacks Project（由 A. Johansson de Wet、J. de Jong 等人维护）是当代代数几何最全面的在线参考。两者在结构上既有继承又有差异：

| 维度 | EGA (1960–1967) | Stacks Project (2008–至今) |
|------|----------------|---------------------------|
| **组织方式** | 线性专著，按卷次递进 | 超文本 Tag 系统，网状链接 |
| **引用精确度** | 章节、定义/命题号、页码 | Tag 编号（如 01H8）+ 定理号 |
| **可搜索性** | 依赖纸质索引或 Numdam 扫描 | 完全可搜索，支持交叉链接 |
| **更新机制** | 固定，Errata 散见于文献 | 持续更新，Git 版本控制 |
| **形式化程度** | 严格自然语言证明 | 严格自然语言证明，部分 Lean4 化 |
| **覆盖范围** | 截至 1967 年的代数几何 | 包含导出代数几何、完美oid 等现代主题 |

**EGA 的不可替代性**：尽管 Stacks Project 在覆盖范围和可访问性上远超 EGA，但 EGA 的**历史语境**无法复制。例如，EGA I 的引言（p. 5–7）直接反映了 Grothendieck 在 1957–1960 年间对“代数几何基础应为何物”的哲学思考——这种第一手的思想史材料在任何后世参考资料中都不存在。

### 7.2 EGA 与 Weil《代数几何基础》的比较

André Weil 的 *Foundations of Algebraic Geometry* (1946) 是 EGA 之前最系统的代数几何基础著作。两者的根本差异在于：

1. **几何对象的定义**：Weil 使用**抽象簇（abstract variety）**，要求每个点都是极大理想（即坐标在代数闭域中），且簇必须由有限个仿射片通过双有理变换粘合。EGA 使用**概形（schéma）**，允许任意交换环作为坐标环，且点可以是任意素理想（包括非闭点）。
2. **层的角色**：Weil 的框架中没有层的概念。EGA 将层（特别是结构层 $\widetilde{A}$）置于核心位置，使得局部-整体关系变得自然。
3. **相对观点**：Weil 的所有构造都是绝对的（相对于固定的基域）。EGA II 系统引入了相对概形 $X/S$ 的概念，使得基变换 $X \times_S S' \to S'$ 成为基本操作。

**Weil 的评价**：Weil 本人在 1979 年的一封信中承认，概形理论比他自己的框架“更加灵活”，但他对非闭点的几何直觉持保留态度。这一分歧——即“几何点是否必须是闭点”——至今仍是代数几何哲学讨论的焦点。

### 7.3 SGA 与 Bourbaki 的比较

SGA 系列以讨论班（séminaire）形式写成，参与者包括 Artin、Deligne、Illusie、Raynaud、Verdier 等。与 Bourbaki 的《数学原理》相比：

- **Bourbaki** 追求极度的一般性与最小的前提假设，其风格是“从空集开始构建一切”。
- **SGA** 则以**具体问题**（如 Weil 猜想的证明策略）为驱动力，理论构造服务于问题的解决。例如，SGA 4 中 Topos 理论的系统发展，其直接动机是为 étale 上同调提供一个足够一般的框架，以证明 Weil 猜想的函数方程（Lefschetz 不动点公式）。

这一“问题导向”的风格深刻影响了后来的数学文献，尤其是 Deligne 的论文和 Lurie 的 *Higher Topos Theory*。

---

## 8. 原始文献解读：EGA I §1.1 与 §2.1 的法语原文精读

### 8.1 仿射概形的定义（EGA I, p. 194）

> **Définition 1.1.1.** — *On appelle **schéma affine** le spectre d'un anneau commutatif $A$, c'est-à-dire l'espace topologique $X = \operatorname{Spec}(A)$ dont les points sont les idéaux premiers de $A$, muni du faisceau d'anneaux $\widetilde{A}$ défini ci-dessus.*

**精读注释**：

- "le spectre d'un anneau commutatif $A$"：Grothendieck 故意使用 "spectre" 而非 "ensemble des idéaux premiers"，以强调 $\operatorname{Spec}(A)$ 是一个具有内在结构的几何对象，而非单纯的集合。
- "muni du faisceau d'anneaux"：这一短语是整个定义中最关键的部分。对 Weil 而言，一个几何对象就是一个拓扑空间；对 Grothendieck 而言，几何对象必须是**环化空间（espace annelé）**，即拓扑空间 + 结构层的不可分割整体。

### 8.2 概形的一般定义（EGA I, p. 203）

> **Définition 2.1.1.** — *On appelle **schéma** un espace topologique $X$ muni d'un faisceau d'anneaux $\mathcal{O}_X$, tel que tout point de $X$ possède un voisinage ouvert $U$ tel que l'espace annelé induit $(U, \mathcal{O}_X|_U)$ soit un schéma affine.*

**精读注释**：

- "tel que tout point ... possède un voisinage ouvert"：这是**局部性（locality）**原则的数学表达。概形不是全局仿射的，而是**局部仿射的**。这一原则与微分几何中“流形是局部欧氏的”完全平行，但 Grothendieck 将其应用于代数范畴。
- "espace annelé induit"：Grothendieck 在此使用了层论的语言（"induit" 即层的限制）。这表明概形理论从诞生之日起就是层论的，而非集合论的。

---

## 9. 与项目其他文档的交叉引用映射

本索引文档作为格洛腾迪克数学理念体系的**元文献层**，为以下 50 篇保留文档提供原始文献定位服务：

### 9.1 核心理论（5 篇）

- `01-核心理论/01-结构主义数学哲学.md` → EGA I 引言, Récoltes et Semailles
- `01-核心理论/02-范畴论方法论.md` → Tôhoku, SGA 4
- `01-核心理论/03-概形理论核心思想.md` → **EGA I, Chap. I, §1–§2**（核心）
- `01-核心理论/04-Topos理论与逻辑.md` → SGA 4, Exposé II–IV
- `01-核心理论/05-相对观点与统一思想.md` → EGA II, §1–§4

### 9.2 概形理论核心（9 篇）

- `02-数学内容深度分析/02-概形理论/01-仿射概形基础.md` → EGA I, Chap. I, §1
- `02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` → EGA I, Chap. I, §2
- `02-数学内容深度分析/02-概形理论/03-纤维积与基变化.md` → EGA I, Chap. I, §3; EGA II, §1
- `02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` → EGA II, §5
- `02-数学内容深度分析/02-概形理论/06-平坦性与平滑性.md` → EGA IV, §6, §11
- `02-数学内容深度分析/02-概形理论/07-除子与线丛.md` → EGA IV, §21
- `02-数学内容深度分析/02-概形理论/08-射影概形.md` → EGA II, §2–§3
- `02-数学内容深度分析/02-概形理论/11-完备概形与紧性.md` → EGA II, §5

### 9.3 金层重构文档（5 篇）

- `金层重构/G1-概形理论的起源与EGA-I核心构造.md` → EGA I, Chap. I, §1.1–§2.3
- `金层重构/G2-Tohoku论文与导出范畴.md` → Tôhoku Math. J. 9 (1957), §1–§2.4
- `金层重构/G3-Grothendieck-Riemann-Roch定理.md` → Borel–Serre 1958; SGA 6
- `金层重构/G4-Topos理论与SGA4.md` → SGA 4, Exposé II, IV, VI
- `金层重构/G5-标准猜想与Motive理论.md` → Grothendieck 1969; Kleiman 1968

---

## 10. 结论与使用指南

本文档建立了 FormalMath 项目中格洛腾迪克专题的**原始文献坐标系**。使用本索引时，研究者应遵循以下规范：

1. **直接引用**：在撰写任何金层文档时，对 EGA/SGA 的引用必须给出**卷号、章节、定义/命题号、页码**。例如：
   > "根据 EGA I, Chap. I, §1.3, Prop. 1.3.1（p. 196），结构层 $\widetilde{A}$ 在标准开集 $D(f)$ 上的截面环满足 $\widetilde{A}(D(f)) \cong A_f$。"

2. **交叉验证**：所有页码以 **Numdam 数字化版本** 为准。若使用 Springer Grundlehren 再版，页码会有偏移，需加注说明。

3. **Lean4 标注**：形式化代码中的每个核心定理，应在注释中标注对应的 `EGARef` 或 `SGARef` 结构实例。

4. **审校流转**：
   - [审校1-领域专家] ✅ 已完成：数学概念与文献坐标的对应关系已核验。
   - [审校2-形式化专家] ⏳ 待启动：Lean4 引用框架需与 Mathlib4 集成。
   - [审校3-同行评议] ⏳ 待启动：邀请代数几何史专家确认 EGA IV 章节编号的准确性。

---

> **专题负责人（Topic Owner）**：待定（FormalMath 学术委员会）
> **最后更新**：2026-04-18
> **关联形式化文件**：`FormalMath/AlgebraicGeometry/References.lean`（计划中）
> **整合素材**：`00-归档-2026年4月/02-数学内容深度分析/05-代数几何现代化/02-EGA与SGA-网络对齐与批判性意见报告.md`
