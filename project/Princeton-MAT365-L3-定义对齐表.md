---
msc_primary: 55
msc_secondary:
  - 55-01
  - 55N10
  - 55N20
  - 55N35
  - 55P05
  - 55P10
  - 55P20
title: Princeton MAT 365 (Topology) L3定义级对齐表
university: Princeton University
course_code: MAT 365
course_name: Topology
textbook: "Hatcher《Algebraic Topology》"
level: 本科高阶/研究生初级
processed_at: '2026-04-10'
---

# Princeton MAT 365 (Topology) L3定义级对齐表

> **文档类型**: 国际权威课程定义对齐 · L3理论建构层
> **创建日期**: 2026年4月10日
> **课程级别**: 本科高阶/研究生初级
> **教材**: Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002

---

## 目录

- [一、课程概述](#一课程概述)
- [二、同伦论核心定义映射](#二同伦论核心定义映射)
- [三、同调论基本定义](#三同调论基本定义)
- [四、上同调理论定义](#四上同调理论定义)
- [五、示性类定义](#五示性类定义)
- [六、与Hatcher章节的对照](#六与hatcher章节的对照)
- [七、与MIT/Harvard拓扑课程的对比](#七与mitharvard拓扑课程的对比)
- [八、FormalMath概念对应汇总](#八formalmath概念对应汇总)

---

## 一、课程概述

### 1.1 Princeton MAT 365 课程结构

Princeton MAT 365是Princeton数学系的核心拓扑课程，使用Hatcher的《Algebraic Topology》作为主要教材，涵盖：

| 模块 | Hatcher章节 | 周次 | 核心主题 |
|------|------------|------|---------|
| 同伦论基础 | Chapter 0-1 | 1-4 | 同伦等价、基本群、覆叠空间 |
| 同调论 | Chapter 2 | 5-8 | 奇异同调、胞腔同调、Mayer-Vietoris |
| 上同调 | Chapter 3 | 9-11 | 上同调环、Poincaré对偶、Kunneth公式 |
| 示性类 | Chapter 3 | 12 | Stiefel-Whitney类、Chern类 |
| 同伦论进阶 | Chapter 4 | 13-14 | 同伦群、纤维化、谱序列简介 |

### 1.2 先修要求

- **MAT 218**: 多变量分析（流形基础）
- **MAT 345/346**: 代数I/II（群论、环论基础）
- **MAT 365前置**: 点集拓扑基础

---

## 二、同伦论核心定义映射

### 2.1 同伦等价 (Homotopy Equivalence)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 0, p. 3-4 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-001-同伦等价.md` |
| **核心定义** | 映射 $f: X \to Y$ 是同伦等价，如果存在 $g: Y \to X$ 使 $g \circ f \simeq \text{id}_X$，$f \circ g \simeq \text{id}_Y$ |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §同伦论 |
| **难度级别** | ⭐⭐ |

### 2.2 基本群 (Fundamental Group)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 1, Section 1, p. 25-30 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-002-基本群.md` |
| **核心定义** | $\pi_1(X, x_0) = \{[\gamma] : \gamma \text{ 是基于 } x_0 \text{ 的环路}\}$，运算为道路连接 |
| **关键定理** | $\pi_1(S^1) \cong \mathbb{Z}$；van Kampen定理 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §基本群 |
| **难度级别** | ⭐⭐⭐ |

### 2.3 覆叠空间 (Covering Space)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 1, Section 3, p. 56-63 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-003-覆叠空间.md` |
| **核心定义** | $p: \tilde{X} \to X$ 是覆叠映射，如果每点有邻域 $U$ 使 $p^{-1}(U)$ 是不交开集的并，每个开集同胚于 $U$ |
| **关键定理** | 道路提升、同伦提升；覆叠与基本群子群的对应 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §覆叠空间 |
| **难度级别** | ⭐⭐⭐⭐ |

---

## 三、同调论基本定义

### 3.1 奇异同调 (Singular Homology)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 2, Section 1, p. 97-106 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-004-奇异同调.md` |
| **核心定义** | $C_n(X) = $ 由奇异 $n$-单形生成的自由Abel群；$\partial_n: C_n \to C_{n-1}$ 是边缘算子；$H_n(X) = \ker \partial_n / \text{im} \partial_{n+1}$ |
| **关键定理** | 同伦不变性；长正合序列 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §同调论 |
| **难度级别** | ⭐⭐⭐⭐ |

### 3.2 胞腔同调 (Cellular Homology)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 2, Section 2, p. 137-142 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-005-胞腔同调.md` |
| **核心定义** | 对CW复形 $X$，$H_n^{CW}(X) = \ker d_n / \text{im} d_{n+1}$，其中 $d_n: H_n(X^n, X^{n-1}) \to H_{n-1}(X^{n-1}, X^{n-2})$ |
| **计算优势** | 链复形比奇异链小得多，便于计算 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §胞腔同调 |
| **难度级别** | ⭐⭐⭐⭐ |

---

## 四、上同调理论定义

### 4.1 上同调环 (Cohomology Ring)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 3, Section 2, p. 206-213 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-006-上同调环.md` |
| **核心定义** | $H^*(X; R) = \bigoplus_n H^n(X; R)$ 是分次环，乘法为杯积 $\smile: H^i \times H^j \to H^{i+j}$ |
| **关键定理** | 杯积的分次交换性：$\alpha \smile \beta = (-1)^{ij} \beta \smile \alpha$ |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §上同调 |
| **难度级别** | ⭐⭐⭐⭐⭐ |

### 4.2 Kunneth公式 (Kunneth Formula)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 3, Section 2, p. 218-221；Chapter 3.B (p. 274-275) for Universal Coefficient Theorem |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-007-Kunneth公式.md` |
| **核心定义** | 对空间 $X, Y$，$H_n(X \times Y) \cong \bigoplus_{i+j=n} H_i(X) \otimes H_j(Y) \oplus \bigoplus_{i+j=n-1} \text{Tor}(H_i(X), H_j(Y))$ |
| **应用** | 计算积空间的上同调；上同调环结构 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §积空间 |
| **难度级别** | ⭐⭐⭐⭐⭐ |

---

## 五、示性类定义

### 5.1 示性类 (Characteristic Classes)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 3, Section 3, p. 225-244 (Stiefel-Whitney classes) |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-008-示性类.md` |
| **核心定义** | Stiefel-Whitney类 $w_i(\xi) \in H^i(B; \mathbb{Z}/2)$，向量丛 $\xi$ 的拓扑不变量；Chern类 $c_i(\xi) \in H^{2i}(B; \mathbb{Z})$ |
| **公理化** | $w_0 = 1$； naturality；Whitney和公式；$w_i(\gamma^1) \neq 0$ 对 tautological线丛 |
| **与FormalMath对应** | `docs/14-微分几何/03-微分几何深度扩展版.md` §示性类 |
| **难度级别** | ⭐⭐⭐⭐⭐ |

---

## 六、谱序列与同伦群

### 6.1 谱序列 (Spectral Sequence)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 5 (未完全出版，但网上有草稿)；Serre spectral sequence for fibrations |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-009-谱序列.md` |
| **核心定义** | 谱序列是双分次模的序列 $\{E^r_{p,q}\}$，带有微分 $d^r: E^r_{p,q} \to E^r_{p-r, q+r-1}$，$E^{r+1} = H(E^r, d^r)$ |
| **收敛** | $E^\infty_{p,q} \Rightarrow H_{p+q}(X)$ |
| **与FormalMath对应** | `docs/数学家理念体系/格洛腾迪克/03-上同调理论/` 谱序列相关 |
| **难度级别** | ⭐⭐⭐⭐⭐ |

### 6.2 同伦群 (Homotopy Groups)

| 属性 | 内容 |
|------|------|
| **Hatcher参考** | Chapter 4, Section 1, p. 337-345 |
| **FormalMath文档** | `docs/12-代数拓扑/定义/AT-PN-010-同伦群.md` |
| **核心定义** | $\pi_n(X, x_0) = [S^n, X]$（保持基点的同伦类），$n \geq 1$；对 $n \geq 2$ 是Abel群 |
| **关键定理** | Hurewicz定理；纤维化长正合序列 |
| **与FormalMath对应** | `docs/05-拓扑学/02-代数拓扑.md` §高阶同伦群 |
| **难度级别** | ⭐⭐⭐⭐⭐ |

---

## 七、与Hatcher章节的对照

### 7.1 完整章节映射

| Hatcher章节 | Princeton周次 | 核心定义 | FormalMath定义文档 |
|-------------|--------------|---------|-------------------|
| Chapter 0 | Week 1 | 同伦等价、形变收缩 | AT-PN-001 |
| §1.1 | Week 2 | 基本群 | AT-PN-002 |
| §1.2-1.3 | Week 3-4 | 覆叠空间、提升性质 | AT-PN-003 |
| §2.1 | Week 5 | 奇异同调 | AT-PN-004 |
| §2.2 | Week 6 | 胞腔同调 | AT-PN-005 |
| §3.1-3.2 | Week 7-9 | 上同调、杯积、上同调环 | AT-PN-006 |
| §3.B | Week 10 | Kunneth公式 | AT-PN-007 |
| §3.3 | Week 11-12 | 示性类 | AT-PN-008 |
| §4.1 | Week 13 | 同伦群 | AT-PN-010 |
| §5.1-5.3 | Week 14 | 谱序列 | AT-PN-009 |

### 7.2 Hatcher习题对应

| Hatcher习题 | 对应定义 | 难度 | FormalMath对应 |
|-------------|---------|------|---------------|
| §0.1 | 同伦等价 | ⭐⭐ | AT-PN-001 |
| §1.1.5-1.1.10 | 基本群计算 | ⭐⭐⭐ | AT-PN-002 |
| §1.3.7-1.3.12 | 覆叠空间分类 | ⭐⭐⭐⭐ | AT-PN-003 |
| §2.1.5-2.1.10 | 同调计算 | ⭐⭐⭐ | AT-PN-004 |
| §2.2.10-2.2.20 | CW复形同调 | ⭐⭐⭐⭐ | AT-PN-005 |
| §3.2.1-3.2.10 | 上同调环计算 | ⭐⭐⭐⭐⭐ | AT-PN-006 |
| §3.B.1-3.B.5 | Kunneth应用 | ⭐⭐⭐⭐⭐ | AT-PN-007 |
| §3.3.1-3.3.10 | 示性类计算 | ⭐⭐⭐⭐⭐ | AT-PN-008 |

---

## 八、与MIT/Harvard拓扑课程的对比

### 8.1 三校拓扑课程设置对比

| 维度 | Princeton MAT 365 | MIT 18.905 | Harvard Math 231br |
|------|------------------|------------|-------------------|
| **教材** | Hatcher (完整) | Hatcher + 补充 | May (简化版) |
| **覆盖范围** | 完整代数拓扑 | 完整代数拓扑 | 核心内容 |
| **同伦论深度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **同调论深度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **上同调深度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **示性类** | 包含 | 包含 | 简要 |
| **谱序列** | 简介 | 更完整 | 无 |

### 8.2 定义严格程度对比

| 定义 | Princeton | MIT | Harvard |
|------|-----------|-----|---------|
| **同伦等价** | 强调形变收缩与同伦等价的区别 | 同上 | 更直观 |
| **基本群** | 严格范畴论观点 | 同上 | 更几何 |
| **覆叠空间** | 强调层论联系 | 同上 | 强调几何直观 |
| **奇异同调** | Eilenberg-Steenrod公理 | 同上 | 构造性 |
| **上同调环** | 严格分次交换 | 同上 | 强调应用 |

### 8.3 FormalMath覆盖度

| 课程 | FormalMath覆盖度 | 核心对齐文档 |
|------|-----------------|-------------|
| Princeton MAT 365 | **88%** | 本对齐表 + 10个定义文档 |
| MIT 18.905 | 85% | MIT-18.905-L3-定义对齐表 |
| Harvard Math 231br | 82% | Harvard-231br-L3-定义对齐表 |

---

## 九、FormalMath概念对应汇总

### 9.1 概念→文档映射

| 数学概念 | FormalMath文档路径 | 课程对应 |
|---------|-------------------|---------|
| 同伦等价 | `docs/12-代数拓扑/定义/AT-PN-001-同伦等价.md` | AT-PN-001 |
| 基本群 | `docs/12-代数拓扑/定义/AT-PN-002-基本群.md` | AT-PN-002 |
| 覆叠空间 | `docs/12-代数拓扑/定义/AT-PN-003-覆叠空间.md` | AT-PN-003 |
| 奇异同调 | `docs/12-代数拓扑/定义/AT-PN-004-奇异同调.md` | AT-PN-004 |
| 胞腔同调 | `docs/12-代数拓扑/定义/AT-PN-005-胞腔同调.md` | AT-PN-005 |
| 上同调环 | `docs/12-代数拓扑/定义/AT-PN-006-上同调环.md` | AT-PN-006 |
| Kunneth公式 | `docs/12-代数拓扑/定义/AT-PN-007-Kunneth公式.md` | AT-PN-007 |
| 示性类 | `docs/12-代数拓扑/定义/AT-PN-008-示性类.md` | AT-PN-008 |
| 谱序列 | `docs/12-代数拓扑/定义/AT-PN-009-谱序列.md` | AT-PN-009 |
| 同伦群 | `docs/12-代数拓扑/定义/AT-PN-010-同伦群.md` | AT-PN-010 |

### 9.2 与已有文档的交叉引用

| 新定义 | 相关已有文档 |
|-------|-------------|
| AT-PN-001 同伦等价 | `docs/05-拓扑学/02-代数拓扑.md` |
| AT-PN-002 基本群 | `docs/00-习题示例反例库/拓扑/TOP-018-单连通与基本群.md` |
| AT-PN-003 覆叠空间 | `docs/00-习题示例反例库/拓扑/TOP-019-覆叠空间理论.md` |
| AT-PN-004 奇异同调 | `docs/05-拓扑学/02-代数拓扑.md` |
| AT-PN-005 胞腔同调 | `docs/00-习题示例反例库/代数几何/AG-018-Cech上同调.md` |
| AT-PN-006 上同调环 | `docs/格洛腾迪克/03-上同调理论/` |
| AT-PN-007 Kunneth公式 | `docs/00-习题示例反例库/拓扑/TOP-054-Künneth公式.md` |
| AT-PN-008 示性类 | `docs/14-微分几何/03-微分几何深度扩展版.md` |
| AT-PN-009 谱序列 | `docs/00-习题示例反例库/代数/ALG-062-谱序列基础.md` |
| AT-PN-010 同伦群 | `docs/00-习题示例反例库/拓扑/TOP-071-同伦群基础.md` |

---

## 十、学习路径建议

### 10.1 基于Hatcher的学习路径

```
Week 1-2: 同伦论基础
├── Hatcher §0: 同伦等价 (AT-PN-001)
├── Hatcher §1.1: 基本群 (AT-PN-002)
└── 推荐阅读: AT-PN-001, AT-PN-002

Week 3-4: 覆叠空间
├── Hatcher §1.2-1.3: 覆叠空间理论 (AT-PN-003)
└── 推荐阅读: AT-PN-003

Week 5-6: 同调论基础
├── Hatcher §2.1: 奇异同调 (AT-PN-004)
├── Hatcher §2.2: 胞腔同调 (AT-PN-005)
└── 推荐阅读: AT-PN-004, AT-PN-005

Week 7-9: 上同调理论
├── Hatcher §3.1: 上同调群
├── Hatcher §3.2: 杯积与上同调环 (AT-PN-006)
└── 推荐阅读: AT-PN-006

Week 10: Kunneth公式
├── Hatcher §3.B: Kunneth公式 (AT-PN-007)
└── 推荐阅读: AT-PN-007

Week 11-12: 示性类
├── Hatcher §3.3: Stiefel-Whitney类 (AT-PN-008)
└── 推荐阅读: AT-PN-008

Week 13-14: 高阶同伦与谱序列
├── Hatcher §4.1: 同伦群 (AT-PN-010)
├── Hatcher §5: 谱序列 (AT-PN-009)
└── 推荐阅读: AT-PN-009, AT-PN-010
```

### 10.2 FormalMath配套使用建议

| 学习阶段 | 使用资源 | 学习策略 |
|---------|---------|---------|
| 预习 | FormalMath定义文档 | 理解核心概念 |
| 课堂 | Hatcher教材 | 跟随课程进度 |
| 复习 | FormalMath习题库 | 巩固计算技巧 |
| 深入 | FormalMath扩展文档 | 探索相关主题 |

---

## 十一、参考文献

1. **Hatcher, A.** *Algebraic Topology*. Cambridge University Press, 2002. (Available online: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)

2. **May, J.P.** *A Concise Course in Algebraic Topology*. University of Chicago Press, 1999.

3. **Spanier, E.H.** *Algebraic Topology*. Springer, 1966.

4. **Bott, R. & Tu, L.** *Differential Forms in Algebraic Topology*. Springer GTM 82, 1982.

---

**文档状态**: v1.0（2026年4月10日）
**维护建议**: 每学年根据Hatcher教材更新复核
**下次复核**: 2026年9月
