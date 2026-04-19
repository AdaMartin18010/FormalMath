---
msc_primary: 00
msc_secondary:
  - 00A99
  - 97A99
title: Stanford FOAG与FormalMath深度映射表
processed_at: '2026-04-05'
---
# Stanford FOAG与FormalMath深度映射表

**文档类型**：国际权威教材对齐 · 章节级详细对应
**创建日期**：2026年4月3日
**最后更新**：2026年4月3日
**FOAG版本**：2025年10月21日（FOAGoct2125public.pdf）
**权威来源**：math.stanford.edu/~vakil/216blog/
**关联文档**：

- [00-国际课程与机构对齐对照表-2026年4月](00-国际课程与机构对齐对照表-2026年4月.md)
- [Harvard-course-mapping-detailed.md](Harvard-course-mapping-detailed.md)
- [Harvard-Stanford-comparison.md](Harvard-Stanford-comparison.md)

---

## 目录

- [Stanford FOAG与FormalMath深度映射表](#stanford-foag与formalmath深度映射表)
  - [目录](#目录)
  - [一、FOAG概述与特色](#一foag概述与特色)
    - [1.1 FOAG简介](#11-foag简介)
    - [1.2 FOAG的教学特色](#12-foag的教学特色)
    - [1.3 与FormalMath的整体对应](#13-与formalmath的整体对应)
  - [二、Part 0: 预述与动机](#二part-0-预述与动机)
    - [Chapter 0: 引言](#chapter-0-引言)
  - [三、Part I: 预备知识](#三part-i-预备知识)
    - [Chapter 1: 范畴论（Category Theory）](#chapter-1-范畴论category-theory)
    - [Chapter 2: 层与拓扑空间（Sheaves and Topological Spaces）](#chapter-2-层与拓扑空间sheaves-and-topological-spaces)
    - [Chapter 3: 仿射概形初步（Toward Affine Schemes）](#chapter-3-仿射概形初步toward-affine-schemes)
  - [四、Part II: 概形](#四part-ii-概形)
    - [Chapter 4: 概形的定义（The Definition of Schemes）](#chapter-4-概形的定义the-definition-of-schemes)
    - [Chapter 5: 概形的性质（Properties of Schemes）](#chapter-5-概形的性质properties-of-schemes)
    - [Chapter 6: 态射的局部性质（Morphisms of Schemes: Local Properties）](#chapter-6-态射的局部性质morphisms-of-schemes-local-properties)
  - [五、Part III: 态射](#五part-iii-态射)
    - [Chapter 7: 有用的态射类（Useful Classes of Morphisms）](#chapter-7-有用的态射类useful-classes-of-morphisms)
    - [Chapter 8: 纤维积与基变换（Fibered Products of Schemes）](#chapter-8-纤维积与基变换fibered-products-of-schemes)
    - [Chapter 9: 分离与真态射（Separated and Proper Morphisms）](#chapter-9-分离与真态射separated-and-proper-morphisms)
    - [Chapter 10: （非）光滑态射与（非）分离态射](#chapter-10-非光滑态射与非分离态射)
  - [六、Part IV: 几何性质](#六part-iv-几何性质)
    - [Chapter 11: 维数与光滑性（Dimension and Smoothness）](#chapter-11-维数与光滑性dimension-and-smoothness)
    - [Chapter 12: 正规化与双有理几何（Normalization and Birational Geometry）](#chapter-12-正规化与双有理几何normalization-and-birational-geometry)
    - [Chapter 13: 除子与线丛（Divisors and Line Bundles）](#chapter-13-除子与线丛divisors-and-line-bundles)
    - [Chapter 14: 层上同调导论（Introduction to Sheaf Cohomology）](#chapter-14-层上同调导论introduction-to-sheaf-cohomology)
  - [七、Part V: 上同调与对偶](#七part-v-上同调与对偶)
    - [Chapter 15: 上同调的深入性质（More on Cohomology）](#chapter-15-上同调的深入性质more-on-cohomology)
    - [Chapter 16: 凝聚层上同调（Cohomology of Coherent Sheaves）](#chapter-16-凝聚层上同调cohomology-of-coherent-sheaves)
    - [Chapter 17: 对偶理论（Duality Theory）](#chapter-17-对偶理论duality-theory)
    - [Chapter 18: 曲线（Curves）](#chapter-18-曲线curves)
    - [Chapter 19: 曲面初步（Introduction to the Geometry of Surfaces）](#chapter-19-曲面初步introduction-to-the-geometry-of-surfaces)
  - [八、Part VI: 进一步专题](#八part-vi-进一步专题)
    - [Chapter 20: 高级专题（Advanced Topics）](#chapter-20-高级专题advanced-topics)
  - [九、Mathlib4形式化对应](#九mathlib4形式化对应)
    - [9.1 概形基础（Schemes）](#91-概形基础schemes)
    - [9.2 上同调（Cohomology）](#92-上同调cohomology)
    - [9.3 使用Mathlib4学习FOAG](#93-使用mathlib4学习foag)
  - [十、FOAG学习路径建议](#十foag学习路径建议)
    - [10.1 标准学习路径](#101-标准学习路径)
    - [10.2 与Harvard Math 232ar/br的对比学习](#102-与harvard-math-232arbr的对比学习)
    - [10.3 练习建议](#103-练习建议)
  - [附录](#附录)
    - [A. FOAG版本历史](#a-foag版本历史)
    - [B. 相关资源链接](#b-相关资源链接)
    - [C. 版本记录](#c-版本记录)

---

## 一、FOAG概述与特色

### 1.1 FOAG简介

**FOAG**（Foundations of Algebraic Geometry）是Stanford大学Ravi Vakil教授的代数几何基础教材，被广泛认为是学习现代代数几何的**最佳入门资源**之一。

| 属性 | 详情 |
|------|------|
| **作者** | Ravi Vakil (Stanford University) |
| **课程** | Stanford Math 216 |
| **最新版本** | October 21, 2025 |
| **页数** | 约800页（持续增长） |
| **获取地址** | http://math.stanford.edu/~vakil/216blog/ |
| **授权** | 免费下载，允许个人使用 |

### 1.2 FOAG的教学特色

| 特色 | 说明 | FormalMath对应 |
|------|------|---------------|
| **直观与形式并重** | 每个概念先有直观解释，再给出严格定义 | `思维表征.md` 系列文档 |
| **丰富的例子** | 大量具体例子支撑抽象概念 | `docs/工作示例/` |
| **历史脉络** | 融入数学史和思想发展 | `数学家理念体系/XX-历史与传记/` |
| **渐进式难度** | 从具体簇过渡到抽象概形 | 基础→增强→深度扩展版结构 |
| **练习设计** | 难度分级明确（★到★★★） | `docs/评估系统/` |

### 1.3 与FormalMath的整体对应

```
FOAG结构 → FormalMath对应

Part 0: 预述 → docs/13-代数几何/（本科入门）
Part I: 预备 → 格洛腾迪克/01-范畴论与函子理论/ + 02-概形理论/基础
Part II: 概形 → 格洛腾迪克/02-概形理论/
Part III: 态射 → 格洛腾迪克/02-概形理论/态射相关篇目
Part IV: 几何性质 → 格洛腾迪克/02-概形理论/几何性质篇目
Part V: 上同调 → 格洛腾迪克/03-上同调理论/
Part VI: 专题 → 格洛腾迪克/05-代数几何现代化/ + 06-其他数学贡献/
```

---

## 二、Part 0: 预述与动机

### Chapter 0: 引言

| FOAG内容 | FormalMath对应 | 学习建议 |
|----------|---------------|----------|
| 代数几何是什么 | `docs/13-代数几何/00-README.md` | 了解学科概览 |
| 经典问题选讲 | `docs/13-代数几何/01-代数几何基础.md` §1 | 建立兴趣 |
| 历史发展脉络 | `数学家理念体系/格洛腾迪克/04-历史与传记/` | 了解Grothendieck革命 |
| 为什么需要概形 | `docs/13-代数几何/03-代数几何深度扩展版.md` §3 | 理解概形的必要性 |

**关键洞察**：FOAG开篇强调概形的自然性和必要性，与FormalMath格洛腾迪克体系中"从经典到现代"的叙述方式一致。

---

## 三、Part I: 预备知识

### Chapter 1: 范畴论（Category Theory）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 1.1 | 动机与例子 | `01-范畴论与函子理论/01-范畴论基础-思维表征.md` | 集合、群、拓扑空间范畴 |
| 1.2 | 范畴的定义 | `01-范畴论与函子理论/01-范畴论基础.md` | 对象、态射、复合 |
| 1.3 | 函子 | `01-范畴论与函子理论/02-函子与自然变换.md` | 协变/逆变函子 |
| 1.4 | 自然变换 | `01-范畴论与函子理论/02-函子与自然变换.md` §3 | 函子间的态射 |
| 1.5 | 等价与伴随 | `01-范畴论与函子理论/05-伴随函子.md` | 伴随函子对 |
| 1.6 | (协)极限 | `01-范畴论与函子理论/03-极限与余极限.md` | 泛性质 |
| 1.7 | 可表函子 | `01-范畴论与函子理论/04-可表函子与Yoneda引理.md` | Yoneda引理 |

**学习建议**：

- 先修：`docs/01-基础数学/` 中的集合论和逻辑基础
- 推荐顺序：思维表征 → 主文档 → 网络对齐报告
- 练习：完成FOAG本章练习（★到★★）验证理解

---

### Chapter 2: 层与拓扑空间（Sheaves and Topological Spaces）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 2.1 | 拓扑空间 | `docs/05-拓扑学/01-点集拓扑.md` | 开集、闭包、连续性 |
| 2.2 | 层的定义 | `03-上同调理论/01-层上同调基础.md` §1 | 预层、层公理 |
| 2.3 | 层的例子 | `03-上同调理论/01-层上同调基础-思维表征.md` | 连续函数层、全纯函数层 |
| 2.4 | 茎与层化 | `03-上同调理论/01-层上同调基础.md` §2 | stalk、层化函子 |
| 2.5 | 层的操作 | `03-上同调理论/01-层上同调基础.md` §3 | 直像、逆像 |
| 2.6 | 局部环化空间 | `02-概形理论/02-概形定义与构造.md` §3 | 局部环、极大理想 |

**学习建议**：

- 本章是代数几何的**核心预备知识**
- 与 `docs/05-拓扑学/01-点集拓扑.md` 并行学习
- 层论是理解概形结构的**关键**

---

### Chapter 3: 仿射概形初步（Toward Affine Schemes）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 3.1 | 从函数到几何 | `02-概形理论/01-仿射概形基础-思维表征.md` | 几何与代数的对应 |
| 3.2 | 素谱构造 | `02-概形理论/01-仿射概形基础.md` §1 | Spec、Zariski拓扑 |
| 3.3 | 结构层 | `02-概形理论/01-仿射概形基础.md` §2 | 结构层O_X |
| 3.4 | 同态与态射 | `02-概形理论/01-仿射概形基础.md` §3 | 环同态诱导概形态射 |

**关键洞察**：FOAG第3章与FormalMath `02-概形理论/01-仿射概形基础.md` 几乎**逐节对应**，可以同步阅读。

---

## 四、Part II: 概形

### Chapter 4: 概形的定义（The Definition of Schemes）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 4.1 | 概形的定义 | `02-概形理论/02-概形定义与构造.md` §1 | 局部环化空间、局部同构于仿射概形 |
| 4.2 | 概形的例子 | `02-概形理论/02-概形定义与构造-思维表征.md` | 射影直线、不交并 |
| 4.3 | 仿射概形是概形 | `02-概形理论/02-概形定义与构造.md` §2 | 验证定义 |
| 4.4 | 投影与纤维积 | `02-概形理论/03-纤维积与基变化.md` §1 | 纤维积存在性 |
| 4.5 | 射影空间 | `02-概形理论/08-射影概形.md` §1 | Proj构造 |

**Mathlib4对应**：

- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum`

---

### Chapter 5: 概形的性质（Properties of Schemes）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 5.1 | 拓扑性质 | `02-概形理论/02-概形定义与构造.md` §4 | 连通、紧性、不可约 |
| 5.2 | 约化概形 | `02-概形理论/09-正规概形与约化概形.md` §2 | 无幂零元 |
| 5.3 | 整概形 | `02-概形理论/09-正规概形与约化概形.md` §1 | 不可约+约化 |
| 5.4 | 局部Noether性质 | `02-概形理论/10-Noether概形与有限性.md` §1 | Noether拓扑 |
| 5.5 | 拟紧与分离 | `02-概形理论/02-概形定义与构造.md` §4 | 分离公理 |

---

### Chapter 6: 态射的局部性质（Morphisms of Schemes: Local Properties）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 6.1 | 开浸入与闭浸入 | `02-概形理论/20-概形的嵌入与浸入.md` | 开子概形、闭子概形 |
| 6.2 | 仿射态射 | `02-概形理论/04-相对概形理论.md` §2 | 原像仿射 |
| 6.3 | 有限性条件 | `02-概形理论/10-Noether概形与有限性.md` §2 | 有限型、有限态射 |
| 6.4 | 正规与光滑 | `02-概形理论/13-光滑概形与正则概形.md` | 正则局部环、光滑性 |

---

## 五、Part III: 态射

### Chapter 7: 有用的态射类（Useful Classes of Morphisms）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 7.1 | 开浸入与闭浸入 | `02-概形理论/20-概形的嵌入与浸入.md` | 浸入判定 |
| 7.2 | 仿射态射详述 | `02-概形理论/04-相对概形理论.md` | 相对Spec |
| 7.3 | 射影态射 | `02-概形理论/08-射影概形.md` §2 | 射影概形、 ample层 |
| 7.4 | 有限态射 | `02-概形理论/10-Noether概形与有限性.md` | 仿射+有限模 |
| 7.5 | 平坦态射 | `02-概形理论/06-平坦性与平滑性.md` §1 | 平坦性等价条件 |
| 7.6 | 形式光滑与光滑 | `02-概形理论/13-光滑概形与正则概形.md` §2 | Jacobian判别法 |

**关键洞察**：FOAG对平坦性的处理非常详细，与FormalMath `02-概形理论/06-平坦性与平滑性.md` 对应。

---

### Chapter 8: 纤维积与基变换（Fibered Products of Schemes）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 8.1 | 纤维积的存在性 | `02-概形理论/03-纤维积与基变化.md` §2 | 构造证明 |
| 8.2 | 纤维积的性质 | `02-概形理论/03-纤维积与基变化.md` §3 | 与基变换交换 |
| 8.3 | 几何纤维 | `02-概形理论/19-概形的纤维与纤维积.md` | 纤维的几何直观 |
| 8.4 | 直观与应用 | `02-概形理论/03-纤维积与基变化-思维表征.md` | 几何解释 |

---

### Chapter 9: 分离与真态射（Separated and Proper Morphisms）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 9.1 | 分离态射 | `02-概形理论/04-相对概形理论.md` §3 | 对角线闭嵌入 |
| 9.2 | 真态射 | `02-概形理论/11-完备概形与紧性.md` | 泛闭+分离+有限型 |
| 9.3 | 射影态射是真态射 | `02-概形理论/11-完备概形与紧性.md` §2 | 射影→真 |
| 9.4 | 赋值判别法 | `02-概形理论/11-完备概形与紧性.md` §3 | 曲线判别法 |

---

### Chapter 10: （非）光滑态射与（非）分离态射

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 10.1 | 非分离概形例子 | `02-概形理论/02-概形定义与构造.md` §5 | 带双原点的直线 |
| 10.2 | 非光滑概形 | `02-概形理论/27-概形的奇点理论.md` | 奇点类型 |
| 10.3 | 更多例子 | `02-概形理论/02-概形定义与构造-思维表征.md` | 反例集合 |

---

## 六、Part IV: 几何性质

### Chapter 11: 维数与光滑性（Dimension and Smoothness）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 11.1 | 维数理论 | `02-概形理论/16-概形的维数理论.md` | Krull维数、余维数 |
| 11.2 | 光滑性判据 | `02-概形理论/13-光滑概形与正则概形.md` §2 | Jacobian判据 |
| 11.3 | 光滑→局部自由微分 | `02-概形理论/12-微分形式与对偶层.md` §1 | Kähler微分 |
| 11.4 | Bertini定理 | `02-概形理论/13-光滑概形与正则概形.md` §3 | 一般超平面截口 |

---

### Chapter 12: 正规化与双有理几何（Normalization and Birational Geometry）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 12.1 | 正规概形 | `02-概形理论/09-正规概形与约化概形.md` §1 | 整闭包 |
| 12.2 | 正规化构造 | `02-概形理论/18-概形的正规化与约化.md` | 泛性质 |
| 12.3 | 双有理等价 | `02-概形理论/26-概形的双有理几何.md` §1 | 双有理态射 |
| 12.4 |  blowing up | `02-概形理论/26-概形的双有理几何.md` §2 | 奇点消解 |

---

### Chapter 13: 除子与线丛（Divisors and Line Bundles）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 13.1 | Weil除子 | `02-概形理论/07-除子与线丛.md` §1 | 素除子、类群 |
| 13.2 | Cartier除子 | `02-概形理论/07-除子与线丛.md` §2 | 可逆层、线丛 |
| 13.3 | 除子与可逆层的关系 | `02-概形理论/07-除子与线丛.md` §3 | Picard群 |
| 13.4 | 射影空间中的除子 | `02-概形理论/08-射影概形.md` §3 | 超平面丛 |
| 13.5 | 丰富线丛 | `02-概形理论/07-除子与线丛.md` §4 | ample、very ample |

**Mathlib4对应**：

- `Mathlib.AlgebraicGeometry.Divisor`
- `Mathlib.AlgebraicGeometry.LineBundle`

---

### Chapter 14: 层上同调导论（Introduction to Sheaf Cohomology）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 14.1 | 上同调动机 | `03-上同调理论/01-层上同调基础-思维表征.md` | 为什么需要上同调 |
| 14.2 | 导出函子定义 | `03-上同调理论/01-层上同调基础.md` §4 | 内射分解、右导出 |
| 14.3 | Cech上同调 | `03-上同调理论/17-Cech上同调与层上同调.md` | 开覆盖、Cech复形 |
| 14.4 | 仿射概形的上同调 | `03-上同调理论/13-上同调的有限性与消失性.md` §1 | Serre消失定理 |

---

## 七、Part V: 上同调与对偶

### Chapter 15: 上同调的深入性质（More on Cohomology）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 15.1 | 推前与上同调 | `03-上同调理论/10-上同调与基变化.md` | 高阶直像 |
| 15.2 | 基变化映射 | `03-上同调理论/10-上同调与基变化.md` §2 | 平坦基变化 |
| 15.3 | 上同调与平坦性 | `03-上同调理论/18-上同调与张量积.md` | Tor函子 |
| 15.5 | 形式函数定理 | `03-上同调理论/14-上同调与局部化.md` | 完备化与上同调 |

---

### Chapter 16: 凝聚层上同调（Cohomology of Coherent Sheaves）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 16.1 | 凝聚层定义 | `02-概形理论/05-拟凝聚层与凝聚层.md` §2 | 有限生成、有限关系 |
| 16.2 | 射影概形的上同调 | `03-上同调理论/25-上同调与凝聚层上同调.md` §1 | Serre消失 |
| 16.3 | 上同调的有限性 | `03-上同调理论/13-上同调的有限性与消失性.md` §2 | 真推前有限性 |
| 16.4 | Euler示性数 | `03-上同调理论/25-上同调与凝聚层上同调.md` §3 | Hilbert多项式 |

**🎯 关键发现**：FOAG第16章与FormalMath `03-上同调理论/25-上同调与凝聚层上同调.md` **高度对应**，这正是Harvard Math 232br的核心内容！

---

### Chapter 17: 对偶理论（Duality Theory）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 17.1 | Serre对偶 | `03-上同调理论/21-上同调与Serre对偶.md` | 曲线、曲面情形 |
| 17.2 | Ext与深度 | `03-上同调理论/19-上同调与Ext函子.md` | 局部对偶 |
| 17.3 | Grothendieck对偶 | `03-上同调理论/22-上同调与Grothendieck对偶.md` | 对偶复形、迹映射 |
| 17.4 | 应用 | `03-上同调理论/22-上同调与Grothendieck对偶.md` §4 | 具体计算 |

**🎯🎯 核心对应**：FOAG第17章与FormalMath `03-上同调理论/21-上同调与Serre对偶.md` 和 `22-上同调与Grothendieck对偶.md` **逐节对应**。

---

### Chapter 18: 曲线（Curves）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 18.1 | 曲线基本性质 | `02-概形理论/`（曲线相关） | 亏格、典则除子 |
| 18.2 | Riemann-Roch定理 | `03-上同调理论/21-上同调与Serre对偶.md` §3 | 曲线版本 |
| 18.3 | 曲线的模空间 | `02-概形理论/25-概形的平坦族与形变理论.md` | 形变理论 |
| 18.4 | Hurwitz定理 | `02-概形理论/24-概形的Galois理论.md` | 分歧覆盖 |

---

### Chapter 19: 曲面初步（Introduction to the Geometry of Surfaces）

| FOAG章节 | 主题 | FormalMath对应文档 | 关键概念 |
|----------|------|-------------------|----------|
| 19.1 | 曲面的交理论 | `02-概形理论/26-概形的双有理几何.md` §3 | 相交数 |
| 19.2 | Riemann-Roch曲面版 | `03-上同调理论/21-上同调与Serre对偶.md` §4 | Noether公式 |
| 19.3 | 直纹面 | `02-概形理论/30-概形的射影束与向量丛.md` | P^1-丛 |
| 19.4 | Castelnuovo准则 | `02-概形理论/26-概形的双有理几何.md` | 例外曲线 |

---

## 八、Part VI: 进一步专题

### Chapter 20: 高级专题（Advanced Topics）

| FOAG章节 | 主题 | FormalMath对应文档 | 学习建议 |
|----------|------|-------------------|----------|
| 20.1 | 群概形 | `02-概形理论/23-概形的群作用与商概形.md` | 群对象 |
| 20.2 | 形式概形 | `02-概形理论/15-概形的局部化与完整化.md` | adic完备化 |
| 20.3 | 代数空间 | `格洛腾迪克/05-代数几何现代化/` | Artin叠 |
| 20.4 | 代数叠 | `格洛腾迪克/05-代数几何现代化/` | Deligne-Mumford叠 |
| 20.5 | 导出范畴与上同调 | `03-上同调理论/06-导出版上同调.md` | 三角范畴 |

---

## 九、Mathlib4形式化对应

### 9.1 概形基础（Schemes）

| FOAG章节 | Mathlib4路径 | 状态 |
|----------|-------------|------|
| Ch. 3-4 | `Mathlib.AlgebraicGeometry.Scheme` | ✅ 完整 |
| Ch. 4.5 | `Mathlib.AlgebraicGeometry.ProjectiveSpectrum` | ✅ 完整 |
| Ch. 5 | `Mathlib.AlgebraicGeometry.Properties` | ✅ 基本完整 |
| Ch. 6 | `Mathlib.AlgebraicGeometry.Morphisms` | ✅ 发展中 |
| Ch. 7 | `Mathlib.AlgebraicGeometry.Flat` | ✅ 进行中 |
| Ch. 13 | `Mathlib.AlgebraicGeometry.Divisor` | ✅ 进行中 |

### 9.2 上同调（Cohomology）

| FOAG章节 | Mathlib4路径 | 状态 |
|----------|-------------|------|
| Ch. 14 | `Mathlib.AlgebraicGeometry.SheafCohomology` | 🔄 发展中 |
| Ch. 16 | `Mathlib.AlgebraicGeometry.CohomologyOfCoherent` | 🔄 计划中 |
| Ch. 17 | `Mathlib.AlgebraicGeometry.Duality` | 🔄 计划中 |

### 9.3 使用Mathlib4学习FOAG

```lean
-- 示例：在Lean4中探索仿射概形
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Spec

-- 定义一个仿射概形
noncomputable example : AffineScheme := Spec (ℤ : CommRing)

-- 查看Spec的拓扑性质
#check Spec ℤ
-- 查看结构层
#check (Spec ℤ).sheaf
```

**学习建议**：

- 在阅读FOAG对应章节时，查看Mathlib4的API文档
- 使用 `#check` 和 `#print` 探索形式化定义
- 在 `docs/09-形式化证明/` 中查找更多示例

---

## 十、FOAG学习路径建议

### 10.1 标准学习路径

```
阶段1：预备（2-3周）
├── FOAG Part 0: 预述
├── FormalMath: docs/13-代数几何/01-代数几何基础.md
└── 目标：理解为什么需要概形

阶段2：范畴与层（3-4周）
├── FOAG Ch. 1: 范畴论
│   └── 格洛腾迪克/01-范畴论与函子理论/
├── FOAG Ch. 2: 层与拓扑空间
│   └── 03-上同调理论/01-层上同调基础.md
└── 目标：掌握抽象语言

阶段3：概形基础（4-5周）⭐核心
├── FOAG Ch. 3-4: 仿射概形与概形
│   └── 格洛腾迪克/02-概形理论/01-02/
├── FOAG Ch. 5: 概形性质
│   └── 格洛腾迪克/02-概形理论/09-10/
└── 目标：理解概形定义和基本例子

阶段4：态射理论（4-5周）⭐核心
├── FOAG Ch. 6-9: 态射的各种类型
│   └── 格洛腾迪克/02-概形理论/03-08/
├── FOAG Ch. 11: 维数与光滑性
│   └── 格洛腾迪克/02-概形理论/12-13/
└── 目标：掌握态射的分类和性质

阶段5：几何深入（3-4周）
├── FOAG Ch. 12: 正规化
│   └── 格洛腾迪克/02-概形理论/18/
├── FOAG Ch. 13: 除子与线丛
│   └── 格洛腾迪克/02-概形理论/07/
└── 目标：理解经典几何概念在概形中的推广

阶段6：上同调（4-6周）⭐⭐核心
├── FOAG Ch. 14-15: 上同调基础
│   └── 格洛腾迪克/03-上同调理论/01-06/
├── FOAG Ch. 16: 凝聚层上同调 ⭐关键
│   └── 格洛腾迪克/03-上同调理论/25-上同调与凝聚层上同调.md
├── FOAG Ch. 17: 对偶理论 ⭐关键
│   └── 格洛腾迪克/03-上同调理论/21-22/
└── 目标：掌握现代代数几何的核心工具

阶段7：应用（3-4周）
├── FOAG Ch. 18-19: 曲线与曲面
│   └── 格洛腾迪克/02-概形理论/ + 03-上同调理论/
└── 目标：看到上同调的实际威力
```

### 10.2 与Harvard Math 232ar/br的对比学习

| 学习阶段 | FOAG对应 | Harvard对应 | FormalMath路径 |
|----------|---------|-------------|---------------|
| 概形基础 | Ch. 3-5 | Math 232ar前半 | 02-概形理论/01-02/ |
| 态射理论 | Ch. 6-9 | Math 232ar后半 | 02-概形理论/03-08/ |
| 上同调基础 | Ch. 14-15 | Math 232br前半 | 03-上同调理论/01-06/ |
| 凝聚层上同调 | Ch. 16 | Math 232br核心 | **03-上同调理论/25-上同调与凝聚层上同调.md** |
| 对偶理论 | Ch. 17 | Math 232br核心 | **03-上同调理论/22-上同调与Grothendieck对偶.md** |

### 10.3 练习建议

FOAG的练习按难度分为：

- ★：基础验证，建议全部完成
- ★★：需要思考，建议完成80%
- ★★★：挑战性，建议尝试至少50%

**FormalMath配套练习**：

- 每章完成后，查阅 `docs/工作示例/` 中的对应计算
- 使用 `docs/00-评估系统/` 的自测题目
- 参考 `数学家理念体系/格洛腾迪克/02-数学内容深度分析/` 的思维表征验证理解

---

## 附录

### A. FOAG版本历史

| 版本日期 | 重要更新 | FormalMath跟进 |
|----------|---------|---------------|
| Jul 31, 2024 | 重大修订版 | 已复核 |
| **Oct 21, 2025** | **当前最新版** | ✅ 已对齐 |

### B. 相关资源链接

- FOAG官网：http://math.stanford.edu/~vakil/216blog/
- Vakil主页：http://math.stanford.edu/~vakil/
- Stanford Math 216：以官网公布为准

### C. 版本记录

| 日期 | 版本 | 更新内容 |
|------|------|----------|
| 2026-04-03 | v1.0 | 初始创建，基于FOAG Oct 2025版本，完整章节映射 |

---

**文档状态**：v1.0（2026年4月）
**维护建议**：FOAG每季度更新，需定期复核映射准确性
**下次复核**：2026年7月（FOAG下一版本发布后）
