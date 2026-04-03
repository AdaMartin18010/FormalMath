---
msc_primary: "00A99"
msc_secondary: "97A99"
---

# MIT数学课程先修依赖关系图

> **说明**: 本图展示MIT数学课程的依赖关系，以及FormalMath资源如何支持这些依赖。

---

## 📊 课程依赖关系总图

```mermaid
flowchart TB
    subgraph Stage0["🌱 预备知识"]
        HS[高中数学<br/>代数/几何/微积分]
    end

    subgraph Stage1["📚 Stage 1: 入门级"]
        18090[18.090<br/>集合论与逻辑]
        18700[18.700<br/>线性代数I]
        18701[18.701<br/>线性代数II]
        18702[18.702<br/>抽象线性代数]
        18703[18.703<br/>计算线性代数]
        18100[18.100<br/>实分析]
    end

    subgraph Stage2["🔬 Stage 2: 高级"]
        18704[18.704<br/>群论]
        18715[18.715<br/>环论]
        18721[18.721<br/>代数几何<br/>⚠️2025-26不开设]
        18782[18.782<br/>数论]
    end

    subgraph Stage3["🎓 Stage 3: 研究生级"]
        18705[18.705<br/>交换代数]
        18725[18.725<br/>代数几何I]
        18726[18.726<br/>代数几何II]
        18745[18.745<br/>李群]
        18755[18.755<br/>表示论]
        18783[18.783<br/>数论高级]
    end

    HS --> 18090
    HS --> 18700

    18090 --> 18100
    18700 --> 18701
    18701 --> 18702
    18701 --> 18703
    18700 --> 18704

    18100 --> 18704
    18704 --> 18715
    18704 --> 18782
    18100 --> 18782

    18715 --> 18705
    18704 --> 18745
    18700 --> 18745
    18100 --> 18745

    18705 -.->|同时修| 18725
    18725 --> 18726
    18704 --> 18755
    18745 -.->|同时修| 18755

    18705 --> 18783
    18782 --> 18783

    18715 -.->|替代路径| 18725
    18705 -.->|准备| 18726
```

---

## 🔄 FormalMath支持映射图

```mermaid
flowchart LR
    subgraph FormalMath["📚 FormalMath资源库"]
        subgraph Foundation["基础数学"]
            SetTheory[集合论<br/>docs/01-基础数学/集合论/]
            ZFC[ZFC公理<br/>docs/01-基础数学/ZFC公理体系/]
            Logic[逻辑学<br/>docs/07-逻辑学/]
        end

        subgraph Algebra["代数结构"]
            Linear[线性代数<br/>docs/02-代数结构/线性代数/]
            Group[群论<br/>docs/02-代数结构/群论/]
            Ring[环论<br/>docs/02-代数结构/环论/]
            Module[模论<br/>docs/02-代数结构/模论/]
            CommAlg[交换代数<br/>docs/02-代数结构/交换代数/]
            Lie[Lie代数<br/>docs/02-代数结构/李代数/]
            Rep[表示论<br/>docs/02-代数结构/表示论/]
        end

        subgraph Analysis["分析学"]
            Real[实分析<br/>docs/03-分析学/实分析/]
            Complex[复分析<br/>docs/03-分析学/复分析/]
            Func[泛函分析<br/>docs/03-分析学/泛函分析/]
        end

        subgraph NumberTheory["数论"]
            Elementary[初等数论<br/>docs/06-数论/初等数论/]
            AlgNT[代数数论<br/>docs/06-数论/代数数论/]
            AnalNT[解析数论<br/>docs/06-数论/解析数论/]
        end

        subgraph AlgebraicGeometry["代数几何"]
            AG[代数几何基础<br/>docs/13-代数几何/]
            Homological[同调代数<br/>docs/15-同调代数/]
        end

        subgraph Grothendieck["格洛腾迪克体系"]
            Cat[范畴论<br/>数学家理念体系/格洛腾迪克/范畴论与函子理论/]
            Schemes[概形理论<br/>数学家理念体系/格洛腾迪克/概形理论/]
            Cohomology[上同调理论<br/>数学家理念体系/格洛腾迪克/上同调理论/]
            Topos[Topos理论<br/>数学家理念体系/格洛腾迪克/Topos理论/]
        end
    end

    subgraph MIT["🎓 MIT课程"]
        18090m[18.090<br/>集合论与逻辑]
        18700m[18.700-703<br/>线性代数序列]
        18100m[18.100<br/>实分析]
        18704m[18.704<br/>群论]
        18715m[18.715<br/>环论]
        18782m[18.782<br/>数论]
        18705m[18.705<br/>交换代数]
        18725m[18.725<br/>代数几何I]
        18726m[18.726<br/>代数几何II]
        18745m[18.745<br/>李群]
        18755m[18.755<br/>表示论]
        18783m[18.783<br/>数论高级]
    end

    SetTheory --> 18090m
    ZFC --> 18090m
    Logic --> 18090m

    Linear --> 18700m

    Real --> 18100m

    Group --> 18704m

    Ring --> 18715m
    Module --> 18715m

    Elementary --> 18782m
    AlgNT --> 18782m

    CommAlg --> 18705m
    Module --> 18705m

    AG --> 18725m
    CommAlg --> 18725m

    Schemes --> 18725m
    Schemes --> 18726m
    Cohomology --> 18726m
    Homological --> 18726m

    Lie --> 18745m
    Rep --> 18745m

    Rep --> 18755m
    Group --> 18755m

    AlgNT --> 18783m
    AnalNT --> 18783m
    AG --> 18783m
```

---

## 📈 课程序列推荐路径

### 标准路径 (4年制)

```mermaid
timeline
    title MIT数学课程标准学习路径

    section 大一秋季
        18.090 : 集合论与逻辑
        18.700 : 线性代数I

    section 大一春季
        18.701 : 线性代数II
        18.100 : 实分析

    section 大二秋季
        18.702 : 抽象线性代数
        18.703 : 计算线性代数

    section 大二春季
        18.704 : 群论
        选修 : 其他课程

    section 大三秋季
        18.715 : 环论
        18.782 : 数论

    section 大三春季
        18.705 : 交换代数
        选修 : 其他课程

    section 大四秋季
        18.725 : 代数几何I
        18.745 : 李群

    section 大四春季
        18.726 : 代数几何II
        18.755 : 表示论
        18.783 : 数论高级
```

### 加速路径 (有扎实基础的学生)

```mermaid
timeline
    title MIT数学课程加速学习路径

    section 大一秋季
        18.090 : 集合论与逻辑(快速)
        18.700 : 线性代数I
        18.100 : 实分析(同时修)

    section 大一春季
        18.701-702 : 线性代数II-III
        18.704 : 群论

    section 大二秋季
        18.715 : 环论
        18.705 : 交换代数(同时修)

    section 大二春季
        18.725 : 代数几何I
        18.782 : 数论

    section 大三
        18.726 : 代数几何II
        18.745 : 李群
        18.755 : 表示论
        18.783 : 数论高级
        研究生课 : 进阶专题
```

---

## 🎯 课程聚类图

```mermaid
flowchart TB
    subgraph PureMath["纯数学核心"]
        subgraph AlgebraCluster["代数方向"]
            AG[代数几何<br/>18.725/726]
            CA[交换代数<br/>18.705]
            RT[表示论<br/>18.755]
            LG[李群<br/>18.745]
        end

        subgraph AnalysisCluster["分析方向"]
            RA[实分析<br/>18.100]
            CA2[复分析<br/>18.112]
            FA[泛函分析<br/>18.102]
        end

        subgraph NumberCluster["数论方向"]
            NT1[数论<br/>18.782]
            NT2[数论高级<br/>18.783]
        end
    end

    subgraph Foundation2["基础支撑"]
        ST[集合论<br/>18.090]
        LA[线性代数<br/>18.700-703]
        GT[群论<br/>18.704]
        RT2[环论<br/>18.715]
    end

    ST --> LA
    ST --> RA
    LA --> GT
    LA --> LG

    GT --> RT2
    GT --> RT
    RT2 --> CA

    RA --> FA
    CA --> AG

    GT --> NT1
    CA --> NT2
    RT2 --> NT1
    FA --> NT2

    LG <--> RT
    AG <--> NT2
```

---

## 📚 FormalMath内容依赖图

```mermaid
flowchart TB
    subgraph ZFC["ZFC公理系统"]
        A1[外延公理]
        A2[配对公理]
        A3[并集公理]
        A4[幂集公理]
        A5[无穷公理]
        A6[分离公理]
        A7[替换公理]
        A8[正则公理]
        A9[选择公理]
    end

    subgraph Numbers["数系构造"]
        N[自然数<br/>Peano算术]
        Z[整数<br/>等价类构造]
        Q[有理数<br/>分式域]
        R[实数<br/>Dedekind分割/Cauchy列]
        C[复数<br/>代数闭包]
    end

    subgraph AlgebraicStructures["代数结构"]
        Group[群<br/>二元运算]
        Ring[环<br/>双运算结构]
        Module[模<br/>环上的向量空间]
        Field[域<br/>可逆环]
        Vector[向量空间<br/>域上的模]
    end

    subgraph AdvancedAlgebra["高等代数"]
        Comm[交换代数<br/>局部化/维数]
        Lie[Lie代数<br/>括号运算]
        Rep[表示论<br/>群到GL的映射]
        Hom[同调代数<br/>链复形/导出函子]
    end

    subgraph Geometry["几何与拓扑"]
        Top[拓扑<br/>开集系统]
        Manifold[流形<br/>局部欧几里得]
        AG[代数几何<br/>概形/层]
        Diff[微分几何<br/>切丛/联络]
    end

    subgraph Analysis2["分析学"]
        Measure[测度论<br/>σ-代数]
        Lebesgue[Lebesgue积分<br/>完备化]
        Func2[泛函分析<br/>Banach/Hilbert空间]
        PDE[偏微分方程<br/>Sobolev空间]
    end

    A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 --> N
    N --> Z
    Z --> Q
    Q --> R
    R --> C

    N --> Group
    Z --> Ring
    Q --> Field
    R --> Vector

    Group --> Lie
    Ring --> Comm
    Module --> Hom
    Field --> Comm
    Vector --> Func2

    Comm --> AG
    Hom --> AG
    Top --> Manifold
    Manifold --> Diff
    AG --> Diff

    R --> Measure
    Measure --> Lebesgue
    Lebesgue --> Func2
    Func2 --> PDE
```

---

## 🔍 课程与FormalMath详细映射

### 18.090 → FormalMath资源

```mermaid
flowchart LR
    18090[18.090<br/>集合论与逻辑]

    subgraph FormalMathSetTheory["FormalMath 集合论"]
        ST1[01-集合论基础<br/>5小时]
        ST2[02-数系与运算<br/>3小时]
        ST3[03-函数与映射<br/>3小时]
        ST4[04-关系与等价<br/>3小时]
        ST5[05-基数与序数<br/>5小时]
    end

    subgraph FormalMathLogic["FormalMath 逻辑学"]
        L1[命题逻辑<br/>3小时]
        L2[一阶逻辑<br/>4小时]
        L3[证明理论<br/>4小时]
    end

    subgraph FormalMathZFC["FormalMath ZFC"]
        ZFC1[ZFC公理详解<br/>6小时]
        ZFC2[自然数构造<br/>2小时]
        ZFC3[实数构造<br/>4小时]
    end

    18090 --> ST1
    18090 --> ST2
    18090 --> ST3
    18090 --> ST4
    18090 --> ST5
    18090 --> L1
    18090 --> L2
    18090 --> L3
    18090 --> ZFC1
    18090 --> ZFC2
    18090 --> ZFC3
```

### 18.725/726 → FormalMath资源

```mermaid
flowchart LR
    18725[18.725<br/>代数几何I]
    18726[18.726<br/>代数几何II]

    subgraph AGResources["FormalMath 代数几何"]
        AG1[代数几何基础<br/>docs/13-代数几何/]
        AG2[代数几何增强版]
        AG3[代数几何深度扩展]
    end

    subgraph GrothendieckResources["格洛腾迪克体系"]
        G1[范畴论与函子理论<br/>27篇]
        G2[概形理论<br/>32篇]
        G3[上同调理论<br/>30篇]
        G4[Topos理论<br/>22篇]
        G5[代数几何现代化<br/>16篇]
    end

    subgraph HomologicalResources["同调代数"]
        H1[同调代数基础<br/>docs/15-同调代数/]
        H2[同调代数增强版]
        H3[同调代数深度扩展]
    end

    18725 --> AG1
    18725 --> AG2
    18725 --> G1
    18725 --> G2

    18726 --> AG3
    18726 --> G2
    18726 --> G3
    18726 --> G4
    18726 --> G5
    18726 --> H1
    18726 --> H2
    18726 --> H3
```

---

## 📋 学习路径检查清单

### 进入Stage 1前

- [ ] 掌握高中数学全部内容
- [ ] 了解基本的集合运算（并、交、补）
- [ ] 理解函数的基本概念

### 进入Stage 2前

- [ ] ✅ 完成18.090: 能写形式化证明
- [ ] ✅ 完成18.700/701: 掌握有限维向量空间理论
- [ ] ✅ 完成18.100: 理解ε-δ语言
- [ ] 能阅读数学文献中的证明

### 进入Stage 3前

- [ ] ✅ 完成18.704: 掌握群论基本定理
- [ ] ✅ 完成18.715: 理解理想理论和模论基础
- [ ] ✅ 完成18.705 (或同时修): 熟悉局部化和诺特环
- [ ] 能独立阅读Hartshorne/Atiyah-Macdonald级别的教材

---

*最后更新: 2026年4月*
