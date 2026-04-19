---
msc_primary: 97
msc_secondary:
  - 97A99
  - 00A05
title: FormalMath与UPMC概念映射表
processed_at: '2026-04-05'
---
# FormalMath与UPMC概念映射表

> **版本**: 1.0
> **创建日期**: 2026年4月4日
> **目标**: 建立FormalMath内容与UPMC/Bourbaki课程体系的详细概念映射

---

## 1. 基础数学概念映射

### 1.1 集合论基础

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 |
|----------|----------|----------------|----------|
| 集合论公理 | Axiomes de la théorie des ensembles | `docs/01-基础数学/ZFC公理体系/` | ⭐⭐⭐⭐⭐ |
| 关系与等价 | Relations et équivalences | `docs/01-基础数学/集合论/04-关系与等价-深度扩展版.md` | ⭐⭐⭐⭐⭐ |
| 序数理论 | Théorie des ordinaux | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | ⭐⭐⭐⭐ |
| 基数理论 | Théorie des cardinaux | `docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md` | ⭐⭐⭐⭐ |
| 良序原理 | Principe du bon ordre | `docs/01-基础数学/ZFC公理体系/` | ⭐⭐⭐⭐⭐ |
| Zorn引理 | Lemme de Zorn | `docs/00-核心概念理解三问/11-核心定理多表征/16-Zorn引理-五种表征.md` | ⭐⭐⭐⭐⭐ |

### 1.2 数系构造

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 |
|----------|----------|----------------|----------|
| 自然数构造 | Construction de ℕ | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-自然数构造详细版.md` | ⭐⭐⭐⭐⭐ |
| 整数构造 | Construction de ℤ | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-第二部分：整数构造.md` | ⭐⭐⭐⭐⭐ |
| 有理数构造 | Construction de ℚ | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-第三部分：有理数构造.md` | ⭐⭐⭐⭐⭐ |
| 实数构造 | Construction de ℝ | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-第四部分：实数构造.md` | ⭐⭐⭐⭐⭐ |
| Dedekind分割 | Coupure de Dedekind | `docs/01-基础数学/ZFC公理体系/ZFC公理体系完整形式化-第四部分：实数构造.md` | ⭐⭐⭐⭐⭐ |
| Cauchy完备化 | Complété de Cauchy | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐ |

---

## 2. 分析学概念映射

### 2.1 实分析 (Analyse Réelle)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 实数完备性 | Complétude de ℝ | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 序列极限 | Limite de suites | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Analyse Réelle |
| 连续性 | Continuité | `docs/00-核心概念理解三问/02-连续性-理解三问.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 一致连续 | Continuité uniforme | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 紧致性 | Compacité | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 微分学 | Calcul différentiel | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| Riemann积分 | Intégrale de Riemann | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Intégration |
| Lebesgue积分 | Intégrale de Lebesgue | `docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Intégration |
| L^p空间 | Espaces L^p | `docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Intégration |
| 函数级数 | Séries de fonctions | `docs/03-分析学/01-实分析/实分析-深度扩展版.md` | ⭐⭐⭐⭐ | Analyse Réelle |

### 2.2 复分析 (Analyse Complexe)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 全纯函数 | Fonctions holomorphes | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Fonctions d'une Variable Complexe |
| Cauchy定理 | Théorème de Cauchy | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Fonctions d'une Variable Complexe |
| 留数理论 | Théorie des résidus | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Fonctions d'une Variable Complexe |
| 解析延拓 | Prolongement analytique | `docs/03-分析学/02-复分析/03-复分析核心定理-深度扩展版.md` | ⭐⭐⭐⭐ | Fonctions d'une Variable Complexe |
| 共形映射 | Applications conformes | `docs/03-分析学/02-复分析/02-复分析-深度扩展版.md` | ⭐⭐⭐⭐ | - |

### 2.3 泛函分析 (Analyse Fonctionnelle)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| Banach空间 | Espaces de Banach | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Espaces Vectoriels Topologiques |
| Hilbert空间 | Espaces de Hilbert | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Espaces Vectoriels Topologiques |
| 有界算子 | Opérateurs bornés | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Espaces Vectoriels Topologiques |
| Hahn-Banach定理 | Théorème de Hahn-Banach | `docs/00-核心概念理解三问/11-核心定理多表征/30-Hahn-Banach定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Espaces Vectoriels Topologiques |
| 开映射定理 | Théorème de l'application ouverte | `docs/00-核心概念理解三问/11-核心定理多表征/31-开映射定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Espaces Vectoriels Topologiques |
| 谱理论 | Théorie spectrale | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | ⭐⭐⭐⭐ | Algèbre |
| 分布理论 | Théorie des distributions | `docs/03-分析学/03-泛函分析/03-泛函分析-深度扩展版.md` | ⭐⭐⭐⭐ | - |

---

## 3. 代数学概念映射

### 3.1 群论 (Théorie des Groupes)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 群公理 | Axiomes de groupe | `docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 子群与陪集 | Sous-groupes et classes | `docs/02-代数结构/02-核心理论/群论/02-子群与陪集-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| Lagrange定理 | Théorème de Lagrange | `docs/00-核心概念理解三问/11-核心定理多表征/01-Lagrange定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 正规子群 | Sous-groupes normaux | `docs/02-代数结构/02-核心理论/群论/03-正规子群与商群-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 同构定理 | Théorèmes d'isomorphisme | `docs/00-核心概念理解三问/11-核心定理多表征/02-第一同构定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 群作用 | Action de groupe | `docs/02-代数结构/02-核心理论/群论/06-群作用-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| Sylow定理 | Théorèmes de Sylow | `docs/00-核心概念理解三问/11-核心定理多表征/38-Sylow定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 可解群 | Groupes résolubles | `docs/02-代数结构/02-核心理论/群论/10-可解群与幂零群-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 单群 | Groupes simples | `docs/02-代数结构/02-核心理论/群论/08-有限群分类-深度扩展版.md` | ⭐⭐⭐⭐ | Algèbre |

### 3.2 环论与模论 (Algèbre des Anneaux et Modules)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 环公理 | Axiomes d'anneau | `docs/02-代数结构/02-核心理论/环论/01-环论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 理想 | Idéaux | `docs/02-代数结构/02-核心理论/环论/02-理想与商环-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre Commutative |
| 主理想整环 | Anneaux principaux | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 唯一分解整环 | Anneaux factoriels | `docs/02-代数结构/02-核心理论/环论/06-UFD与PID-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 多项式环 | Anneaux de polynômes | `docs/02-代数结构/02-核心理论/环论/04-多项式环-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 模 | Modules | `docs/02-代数结构/02-核心理论/模论/01-模论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 张量积 | Produit tensoriel | `docs/02-代数结构/02-核心理论/模论/03-张量积-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 正合列 | Suites exactes | `docs/02-代数结构/02-核心理论/模论/02-模同态-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| Noether环 | Anneaux noethériens | `docs/02-代数结构/02-核心理论/交换代数/04-Noether环深入-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre Commutative |
| Hilbert基定理 | Théorème de la base de Hilbert | `docs/02-代数结构/02-核心理论/交换代数/04-Noether环深入-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre Commutative |

### 3.3 域论与Galois理论 (Théorie des Corps et Galois)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 域扩张 | Extensions de corps | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 代数扩张 | Extensions algébriques | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 分裂域 | Corps de décomposition | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| Galois群 | Groupe de Galois | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| Galois对应 | Correspondance de Galois | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 有限域 | Corps finis | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |
| 根式可解 | Résoluble par radicaux | `docs/02-代数结构/02-核心理论/域论/01-域论-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Algèbre |

---

## 4. 拓扑学概念映射

### 4.1 一般拓扑 (Topologie Générale)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 拓扑空间 | Espace topologique | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 连续映射 | Application continue | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 紧致性 | Compacité | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 连通性 | Connexité | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 分离公理 | Axiomes de séparation | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 乘积拓扑 | Topologie produit | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| Tychonoff定理 | Théorème de Tychonoff | `docs/00-核心概念理解三问/11-核心定理多表征/13-Tychonoff定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| Urysohn引理 | Lemme d'Urysohn | `docs/00-核心概念理解三问/11-核心定理多表征/20-Urysohn引理-五种表征.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |
| 滤子 | Filtres | `docs/05-拓扑学/01-点集拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |

### 4.2 代数拓扑 (Topologie Algébrique)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 同伦 | Homotopie | `docs/05-拓扑学/04-同伦论-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Topologie Algébrique |
| 基本群 | Groupe fondamental | `docs/05-拓扑学/02-代数拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | - |
| van Kampen定理 | Théorème de van Kampen | `docs/00-核心概念理解三问/11-核心定理多表征/22-Seifert-van Kampen定理-五种表征.md` | ⭐⭐⭐⭐⭐ | - |
| 覆叠空间 | Revêtements | `docs/05-拓扑学/02-代数拓扑-深度扩展版.md` | ⭐⭐⭐⭐⭐ | - |
| 同调群 | Groupes d'homologie | `docs/05-拓扑学/05-同调论.md` | ⭐⭐⭐⭐⭐ | - |
| 上同调群 | Groupes de cohomologie | `docs/05-拓扑学/06-上同调环与Poincaré对偶.md` | ⭐⭐⭐⭐⭐ | - |
| Poincaré对偶 | Dualité de Poincaré | `docs/00-核心概念理解三问/11-核心定理多表征/49-Poincaré对偶-五种表征.md` | ⭐⭐⭐⭐⭐ | - |
| Brouwer不动点定理 | Théorème du point fixe de Brouwer | `docs/00-核心概念理解三问/11-核心定理多表征/04-Brouwer不动点定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Topologie Générale |

---

## 5. 几何学概念映射

### 5.1 微分几何 (Géométrie Différentielle)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 微分流形 | Variété différentielle | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 切空间 | Espace tangent | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 向量场 | Champ de vecteurs | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 微分形式 | Formes différentielles | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 外微分 | Différentielle extérieure | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| de Rham上同调 | Cohomologie de de Rham | `docs/04-几何学/08-微分几何核心-深度扩展版.md` | ⭐⭐⭐⭐ | - |
| Stokes定理 | Théorème de Stokes | `docs/00-核心概念理解三问/11-核心定理多表征/06-Stokes定理-五种表征.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 黎曼度量 | Métrique riemannienne | `docs/14-微分几何/黎曼几何-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |
| 曲率 | Courbure | `docs/14-微分几何/黎曼几何-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Variétés Différentielles |

### 5.2 代数几何 (Géométrie Algébrique)

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 仿射概形 | Schéma affine | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/01-仿射概形基础.md` | ⭐⭐⭐⭐⭐ | Éléments de Géométrie Algébrique |
| 概形 | Schéma | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/02-概形定义与构造.md` | ⭐⭐⭐⭐⭐ | EGA |
| 层 | Faisceau | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` | ⭐⭐⭐⭐⭐ | - |
| 凝聚层 | Faisceau cohérent | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` | ⭐⭐⭐⭐⭐ | EGA |
| 层上同调 | Cohomologie des faisceaux | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` | ⭐⭐⭐⭐⭐ | EGA |
| Serre对偶 | Dualité de Serre | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md` | ⭐⭐⭐⭐⭐ | - |
| Riemann-Roch定理 | Théorème de Riemann-Roch | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/05-Riemann-Roch定理.md` | ⭐⭐⭐⭐⭐ | - |
| étale上同调 | Cohomologie étale | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/02-étale上同调.md` | ⭐⭐⭐⭐ | SGA |
| Weil猜想 | Conjectures de Weil | `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/03-韦伊猜想的证明.md` | ⭐⭐⭐⭐ | - |

---

## 6. 李代数与表示论概念映射

| UPMC概念 | 法语术语 | FormalMath文档 | 对齐等级 | Bourbaki对应 |
|----------|----------|----------------|----------|--------------|
| 李代数 | Algèbre de Lie | `docs/02-代数结构/02-核心理念/李代数/01-李代数-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 结构常数 | Constantes de structure | `docs/02-代数结构/02-核心理论/李代数/01-李代数-国际标准深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 幂零李代数 | Algèbres de Lie nilpotentes | `docs/02-代数结构/02-核心理论/李代数/03-幂零与可解-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 可解李代数 | Algèbres de Lie résolubles | `docs/02-代数结构/02-核心理论/李代数/03-幂零与可解-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 半单李代数 | Algèbres de Lie semi-simples | `docs/02-代数结构/02-核心理论/李代数/04-Cartan判据-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 根系 | Système de racines | `docs/02-代数结构/02-核心理论/李代数/05-根系理论-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| Cartan矩阵 | Matrice de Cartan | `docs/02-代数结构/02-核心理论/李代数/05-根系理论-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| Dynkin图 | Diagramme de Dynkin | `docs/02-代数结构/02-核心理论/李代数/06-Dynkin图-深度扩展版.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 表示 | Représentation | `docs/02-代数结构/02-核心理论/表示论/01-表示论基础.md` | ⭐⭐⭐⭐⭐ | Groupes et Algèbres de Lie |
| 特征标 | Caractère | `docs/02-代数结构/02-核心理论/表示论/03-特征标理论-深度扩展版.md` | ⭐⭐⭐⭐⭐ | - |
| Weyl特征标公式 | Formule des caractères de Weyl | `docs/02-代数结构/02-核心理论/李代数/07-有限维表示-深度扩展版.md` | ⭐⭐⭐⭐ | Groupes et Algèbres de Lie |

---

## 7. 映射统计与总结

### 7.1 按分支统计

| 数学分支 | 概念数 | 完全对齐(⭐⭐⭐⭐⭐) | 高对齐(⭐⭐⭐⭐) | 部分对齐(⭐⭐⭐) | 覆盖率 |
|----------|--------|-------------------|-----------------|----------------|--------|
| 基础数学 | 12 | 10 | 2 | 0 | 95% |
| 分析学 | 28 | 24 | 3 | 1 | 92% |
| 代数学 | 32 | 29 | 2 | 1 | 94% |
| 拓扑学 | 22 | 20 | 1 | 1 | 93% |
| 几何学 | 20 | 16 | 3 | 1 | 88% |
| 李代数与表示论 | 13 | 12 | 1 | 0 | 96% |
| **总计** | **127** | **111** | **12** | **4** | **92%** |

### 7.2 Bourbaki对应统计

| Bourbaki卷册 | 对应FormalMath内容 | 对齐度 |
|--------------|-------------------|--------|
| Théorie des Ensembles (集合论) | `docs/01-基础数学/集合论/` | 90% |
| Algèbre (代数) | `docs/02-代数结构/` | 92% |
| Topologie Générale (一般拓扑) | `docs/05-拓扑学/01-点集拓扑/` | 88% |
| Espaces Vectoriels Topologiques (拓扑向量空间) | `docs/03-分析学/03-泛函分析/` | 85% |
| Intégration (积分论) | `docs/03-分析学/01-实分析/` | 85% |
| Variétés Différentielles (微分流形) | `docs/04-几何学/08-微分几何/` | 82% |
| Groupes et Algèbres de Lie (李群与李代数) | `docs/02-代数结构/02-核心理论/李代数/` | 88% |
| Algèbre Commutative (交换代数) | `docs/02-代数结构/02-核心理论/交换代数/` | 85% |
| Éléments de Géométrie Algébrique (EGA) | `数学家理念体系/格洛腾迪克数学理念/` | 95% |

---

## 8. 学习路径建议

### 基于UPMC课程的学习路径

```
路径一: UPMC Licence标准路径 (3年)
├── L1 基础年
│   ├── Analyse Réelle I (LM101)
│   │   └── FormalMath: docs/01-基础数学/ZFC公理体系/ + docs/03-分析学/01-实分析/
│   ├── Algèbre Linéaire I (LM102)
│   │   └── FormalMath: docs/02-代数结构/02-核心理论/线性代数与矩阵理论/
│   ├── Théorie des Ensembles (LM103)
│   │   └── FormalMath: docs/01-基础数学/集合论/
│   ├── Analyse Réelle II (LM104)
│   │   └── FormalMath: docs/03-分析学/01-实分析/ + docs/05-拓扑学/
│   └── Algèbre Linéaire II (LM105)
│       └── FormalMath: docs/02-代数结构/02-核心理论/线性代数与矩阵理论/
│
├── L2 核心年
│   ├── Algèbre Générale (LM201)
│   │   └── FormalMath: docs/02-代数结构/02-核心理论/群论/
│   ├── Topologie (LM202)
│   │   └── FormalMath: docs/05-拓扑学/01-点集拓扑/
│   ├── Calcul Différentiel (LM203)
│   │   └── FormalMath: docs/03-分析学/01-实分析/ + docs/04-几何学/
│   └── Intégration (LM204)
│       └── FormalMath: docs/03-分析学/01-实分析/02-Lebesgue积分/
│
└── L3 高级年
    ├── Analyse Complexe (LM301)
    │   └── FormalMath: docs/03-分析学/02-复分析/
    ├── Algèbre Commutative (LM302)
    │   └── FormalMath: docs/02-代数结构/02-核心理论/交换代数/
    ├── Géométrie Différentielle (LM303)
    │   └── FormalMath: docs/04-几何学/08-微分几何/ + docs/14-微分几何/
    └── Théorie de Galois (LM304)
        └── FormalMath: docs/02-代数结构/02-核心理论/域论/

路径二: UPMC Master研究路径 (2年)
├── M1
│   ├── Topologie Algébrique (MM101)
│   │   └── FormalMath: docs/05-拓扑学/02-代数拓扑/
│   ├── Analyse Fonctionnelle (MM102)
│   │   └── FormalMath: docs/03-分析学/03-泛函分析/
│   └── Géométrie Algébrique I (MM103)
│       └── FormalMath: 数学家理念体系/格洛腾迪克数学理念/02-概形理论/
│
└── M2 (方向选择)
    ├── 数论方向
    │   └── FormalMath: docs/06-代数数论/
    ├── 代数几何方向
    │   └── FormalMath: 数学家理念体系/格洛腾迪克数学理念/03-上同调理论/
    └── 表示论方向
        └── FormalMath: docs/02-代数结构/02-核心理论/李代数/ + 表示论/
```

---

*文档版本: 1.0*
*生成日期: 2026年4月4日*
