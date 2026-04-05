---
title: nLab高阶概念映射表
msc_primary: 00A99
processed_at: '2026-04-05'
---
# nLab高阶概念映射表

**文档编号**: FM-ALIGN-NLAB-MAP-2026-04  
**创建日期**: 2026年4月4日  
**版本**: 1.0

---

## 使用说明

本映射表提供nLab与FormalMath之间的概念对应关系，支持多维度查询：
- 按主题分类
- 按难度级别
- 按形式化状态
- 按依赖关系

---

## 一、按主题分类映射

### 1. 基础范畴论 (Basic Category Theory)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 1.1 | category | Category | 范畴 | 18A05 | L1 | ✅ |
| 1.2 | functor | Functor | 函子 | 18A22 | L1 | ✅ |
| 1.3 | natural transformation | NaturalTransformation | 自然变换 | 18A23 | L1 | ✅ |
| 1.4 | isomorphism | Isomorphism | 同构 | 18A05 | L1 | ✅ |
| 1.5 | monomorphism | Monomorphism | 单态射 | 18A20 | L1 | ✅ |
| 1.6 | epimorphism | Epimorphism | 满态射 | 18A20 | L1 | ✅ |
| 1.7 | terminal object | TerminalObject | 终对象 | 18A30 | L1 | ✅ |
| 1.8 | initial object | InitialObject | 始对象 | 18A30 | L1 | ✅ |
| 1.9 | product | Product | 积 | 18A30 | L2 | ✅ |
| 1.10 | coproduct | Coproduct | 余积 | 18A30 | L2 | ✅ |
| 1.11 | equalizer | Equalizer | 等化子 | 18A30 | L2 | ✅ |
| 1.12 | coequalizer | Coequalizer | 余等化子 | 18A30 | L2 | ✅ |
| 1.13 | limit | Limit | 极限 | 18A30 | L2 | ✅ |
| 1.14 | colimit | Colimit | 余极限 | 18A30 | L2 | ✅ |
| 1.15 | adjunction | Adjunction | 伴随 | 18A40 | L2 | ✅ |
| 1.16 | unit | Unit | 单位 | 18A40 | L2 | ✅ |
| 1.17 | counit | Counit | 余单位 | 18A40 | L2 | ✅ |
| 1.18 | representable functor | RepresentableFunctor | 可表示函子 | 18F20 | L2 | ✅ |
| 1.19 | Yoneda lemma | YonedaLemma | 米田引理 | 18F20 | L2 | ✅ |
| 1.20 | Yoneda embedding | YonedaEmbedding | 米田嵌入 | 18F20 | L2 | ✅ |

### 2. 充实范畴论 (Enriched Category Theory)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 2.1 | enriched category | EnrichedCategory | 充实范畴 | 18D20 | L2 | ⚠️ |
| 2.2 | enriched functor | EnrichedFunctor | 充实函子 | 18D20 | L2 | ⚠️ |
| 2.3 | monoidal category | MonoidalCategory | 单范畴 | 18D10 | L2 | ✅ |
| 2.4 | strict monoidal category | StrictMonoidalCategory | 严格单范畴 | 18D10 | L2 | ⚠️ |
| 2.5 | braided monoidal category | BraidedMonoidalCategory | 辫单范畴 | 18D10 | L3 | ⚠️ |
| 2.6 | symmetric monoidal category | SymmetricMonoidalCategory | 对称单范畴 | 18D10 | L3 | ⚠️ |
| 2.7 | closed monoidal category | ClosedMonoidalCategory | 闭单范畴 | 18D15 | L3 | ⚠️ |
| 2.8 | compact closed category | CompactClosedCategory | 紧闭合范畴 | 18D15 | L3 | ❌ |
| 2.9 | *-autonomous category | StarAutonomousCategory | *-自反范畴 | 18D15 | L4 | ❌ |
| 2.10 | traced monoidal category | TracedMonoidalCategory | 迹单范畴 | 18D10 | L4 | ❌ |

### 3. 高阶范畴论 (Higher Category Theory)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 3.1 | 2-category | TwoCategory | 2-范畴 | 18N10 | L3 | ⚠️ |
| 3.2 | bicategory | Bicategory | 双范畴 | 18N10 | L3 | ⚠️ |
| 3.3 | 2-functor | TwoFunctor | 2-函子 | 18N10 | L3 | ⚠️ |
| 3.4 | pseudofunctor | Pseudofunctor | 伪函子 | 18N10 | L3 | ❌ |
| 3.5 | lax functor | LaxFunctor | 松弛函子 | 18N10 | L4 | ❌ |
| 3.6 | modification | Modification | 修正 | 18N10 | L3 | ❌ |
| 3.7 | tricategory | Tricategory | 三范畴 | 18N10 | L4 | ❌ |
| 3.8 | Gray-category | GrayCategory | Gray-范畴 | 18N10 | L4 | ❌ |
| 3.9 | (∞,1)-category | InfinityOneCategory | (∞,1)-范畴 | 18N60 | L4 | ⚠️ |
| 3.10 | quasi-category | QuasiCategory | 拟范畴 | 18N60 | L4 | ❌ |
| 3.11 | Kan complex | KanComplex | Kan复形 | 18N50 | L4 | ⚠️ |
| 3.12 | complete Segal space | CompleteSegalSpace | 完全Segal空间 | 18N60 | L4 | ❌ |
| 3.13 | simplicially enriched category | SimplicialCategory | 单纯范畴 | 18N50 | L4 | ❌ |
| 3.14 | model category | ModelCategory | 模型范畴 | 18N40 | L4 | ⚠️ |
| 3.15 | derivator | Derivator | 导出子 | 18G80 | L4 | ❌ |

### 4. 无穷群胚与同伦 (Infinity-Groupoids and Homotopy)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 4.1 | ∞-groupoid | InfinityGroupoid | 无穷群胚 | 18N50 | L4 | ⚠️ |
| 4.2 | fundamental ∞-groupoid | FundamentalInfinityGroupoid | 基本无穷群胚 | 18N50 | L4 | ⚠️ |
| 4.3 | homotopy hypothesis | HomotopyHypothesis | 同伦假设 | 18N50 | L4 | ⚠️ |
| 4.4 | delooping | Delooping | 去圈 | 18N50 | L4 | ❌ |
| 4.5 | looping | Looping | 圈化 | 18N50 | L4 | ❌ |
| 4.6 | suspension | Suspension | 悬挂 | 55P40 | L4 | ⚠️ |
| 4.7 | stabilization | Stabilization | 稳定化 | 55P42 | L4 | ❌ |
| 4.8 | periodic table | PeriodicTable | 周期表 | 18N50 | L4 | ❌ |

### 5. 同伦类型论 (Homotopy Type Theory)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 5.1 | homotopy type theory | HomotopyTypeTheory | 同伦类型论 | 03B38 | L4 | ✅ |
| 5.2 | dependent type | DependentType | 依赖类型 | 03B15 | L2 | ✅ |
| 5.3 | identity type | IdentityType | 恒等类型 | 03B38 | L3 | ✅ |
| 5.4 | path type | PathType | 路径类型 | 03B38 | L3 | ✅ |
| 5.5 | higher inductive type | HigherInductiveType | 高阶归纳类型 | 03B38 | L4 | ✅ |
| 5.6 | univalence axiom | UnivalenceAxiom | 单值公理 | 03B38 | L4 | ✅ |
| 5.7 | function extensionality | FunctionExtensionality | 函数外延性 | 03B38 | L3 | ✅ |
| 5.8 | type of types | TypeOfTypes | 类型之类型 | 03B38 | L4 | ⚠️ |
| 5.9 | h-level | HLevel | h-层级 | 03B38 | L3 | ⚠️ |
| 5.10 | truncation | Truncation | 截断 | 03B38 | L3 | ⚠️ |
| 5.11 | cubical type theory | CubicalTypeTheory | 立方类型论 | 03B38 | L4 | ❌ |
| 5.12 | cohesive homotopy type theory | CohesiveHoTT | 凝聚同伦类型论 | 03B38 | L4 | ❌ |

### 6. Topos理论 (Topos Theory)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 6.1 | topos | Topos | 拓扑斯 | 18B25 | L3 | ⚠️ |
| 6.2 | elementary topos | ElementaryTopos | 初等拓扑斯 | 18B25 | L3 | ⚠️ |
| 6.3 | Grothendieck topos | GrothendieckTopos | Grothendieck拓扑斯 | 18F10 | L3 | ⚠️ |
| 6.4 | sheaf | Sheaf | 层 | 14F05 | L3 | ✅ |
| 6.5 | presheaf | Presheaf | 预层 | 18F20 | L3 | ✅ |
| 6.6 | site | Site | 景 | 18F10 | L3 | ⚠️ |
| 6.7 | coverage | Coverage | 覆盖 | 18F10 | L3 | ❌ |
| 6.8 | sieve | Sieve | 筛 | 18F10 | L3 | ❌ |
| 6.9 | sheafification | Sheafification | 层化 | 18F10 | L3 | ⚠️ |
| 6.10 | subobject classifier | SubobjectClassifier | 子对象分类器 | 18B25 | L3 | ❌ |
| 6.11 | natural numbers object | NaturalNumbersObject | 自然数对象 | 18B25 | L3 | ⚠️ |
| 6.12 | power object | PowerObject | 幂对象 | 18B25 | L3 | ❌ |
| 6.13 | internal logic | InternalLogic | 内部逻辑 | 03G30 | L3 | ⚠️ |
| 6.14 | Mitchell-Bénabou language | MitchellBenabouLanguage | Mitchell-Bénabou语言 | 03G30 | L4 | ❌ |
| 6.15 | Kripke-Joyal semantics | KripkeJoyalSemantics | Kripke-Joyal语义 | 03G30 | L4 | ❌ |

### 7. 几何态射 (Geometric Morphisms)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 7.1 | geometric morphism | GeometricMorphism | 几何态射 | 18F10 | L3 | ❌ |
| 7.2 | direct image | DirectImage | 正像 | 18F10 | L3 | ❌ |
| 7.3 | inverse image | InverseImage | 逆像 | 18F10 | L3 | ❌ |
| 7.4 | essential geometric morphism | EssentialGeometricMorphism | 本质几何态射 | 18F10 | L4 | ❌ |
| 7.5 | locally connected morphism | LocallyConnectedMorphism | 局部连通态射 | 18F10 | L4 | ❌ |
| 7.6 | connected morphism | ConnectedMorphism | 连通态射 | 18F10 | L4 | ❌ |
| 7.7 | local geometric morphism | LocalGeometricMorphism | 局部几何态射 | 18F10 | L4 | ❌ |
| 7.8 | open geometric morphism | OpenGeometricMorphism | 开几何态射 | 18F10 | L4 | ❌ |
| 7.9 | proper geometric morphism | ProperGeometricMorphism | 真几何态射 | 18F10 | L4 | ❌ |
| 7.10 | surjective geometric morphism | SurjectiveGeometricMorphism | 满几何态射 | 18F10 | L4 | ❌ |
| 7.11 | geometric embedding | GeometricEmbedding | 几何嵌入 | 18F10 | L4 | ❌ |

### 8. (∞,1)-Topos理论

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 8.1 | (∞,1)-topos | InfinityTopos | (∞,1)-拓扑斯 | 18N60 | L4 | ❌ |
| 8.2 | elementary (∞,1)-topos | ElementaryInfinityTopos | 初等(∞,1)-拓扑斯 | 18N60 | L4 | ❌ |
| 8.3 | (∞,1)-sheaf | InfinitySheaf | (∞,1)-层 | 18N60 | L4 | ❌ |
| 8.4 | (∞,1)-site | InfinitySite | (∞,1)-景 | 18N60 | L4 | ❌ |
| 8.5 | (∞,1)-presheaf | InfinityPresheaf | (∞,1)-预层 | 18N60 | L4 | ❌ |
| 8.6 | topological localization | TopologicalLocalization | 拓扑局部化 | 18N60 | L4 | ❌ |
| 8.7 | hypercompletion | Hypercompletion | 超完备化 | 18N60 | L4 | ❌ |
| 8.8 | object classifier | ObjectClassifier | 对象分类器 | 18N60 | L4 | ❌ |
| 8.9 | n-truncated object | NTruncatedObject | n-截断对象 | 18N60 | L4 | ❌ |
| 8.10 | n-connected object | NConnectedObject | n-连通对象 | 18N60 | L4 | ❌ |
| 8.11 | cohesive (∞,1)-topos | CohesiveInfinityTopos | 凝聚(∞,1)-拓扑斯 | 18N60 | L4 | ❌ |
| 8.12 | local (∞,1)-topos | LocalInfinityTopos | 局部(∞,1)-拓扑斯 | 18N60 | L4 | ❌ |
| 8.13 | structured (∞,1)-topos | StructuredInfinityTopos | 结构化(∞,1)-拓扑斯 | 18N60 | L4 | ❌ |

### 9. 高阶代数 (Higher Algebra)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 9.1 | monoidal (∞,1)-category | MonoidalInfinityCategory | 单(∞,1)-范畴 | 18N70 | L4 | ❌ |
| 9.2 | symmetric monoidal (∞,1)-category | SymmetricMonoidalInfinityCategory | 对称单(∞,1)-范畴 | 18N70 | L4 | ❌ |
| 9.3 | algebra object | AlgebraObject | 代数对象 | 18C15 | L3 | ⚠️ |
| 9.4 | module object | ModuleObject | 模对象 | 18C15 | L3 | ⚠️ |
| 9.5 | operad | Operad | Operad | 18M60 | L4 | ⚠️ |
| 9.6 | (∞,1)-operad | InfinityOperad | (∞,1)-Operad | 18N70 | L4 | ❌ |
| 9.7 | algebra over an operad | AlgebraOverOperad | Operad上的代数 | 18M60 | L4 | ❌ |
| 9.8 | commutative algebra object | CommutativeAlgebraObject | 交换代数对象 | 18C15 | L4 | ⚠️ |
| 9.9 | spectrum | Spectrum | 谱 | 55P42 | L4 | ⚠️ |
| 9.10 | ring spectrum | RingSpectrum | 环谱 | 55P43 | L4 | ❌ |
| 9.11 | A-∞ ring | AInfinityRing | A-无穷环 | 55P43 | L4 | ❌ |
| 9.12 | E-∞ ring | EInfinityRing | E-无穷环 | 55P43 | L4 | ❌ |
| 9.13 | module spectrum | ModuleSpectrum | 模谱 | 55P43 | L4 | ❌ |
| 9.14 | L-∞ algebra | LInfinityAlgebra | L-无穷代数 | 18M70 | L4 | ❌ |
| 9.15 | brave new algebra | BraveNewAlgebra | 勇敢新代数 | 55P43 | L4 | ❌ |

### 10. 导出范畴与同调代数 (Derived Categories and Homological Algebra)

| 序号 | nLab概念 | FormalMath概念 | 中文名 | MSC | 难度 | 状态 |
|-----|---------|--------------|-------|-----|-----|------|
| 10.1 | derived category | DerivedCategory | 导出范畴 | 18G80 | L3 | ✅ |
| 10.2 | chain complex | ChainComplex | 链复形 | 18G35 | L2 | ✅ |
| 10.3 | cochain complex | CochainComplex | 上链复形 | 18G35 | L2 | ✅ |
| 10.4 | quasi-isomorphism | QuasiIsomorphism | 拟同构 | 18G35 | L3 | ✅ |
| 10.5 | homotopy category of chain complexes | HomotopyCategoryOfChainComplexes | 链复形同伦范畴 | 18G35 | L3 | ⚠️ |
| 10.6 | derived functor | DerivedFunctor | 导出函子 | 18G10 | L3 | ✅ |
| 10.7 | total derived functor | TotalDerivedFunctor | 全导出函子 | 18G10 | L4 | ⚠️ |
| 10.8 | spectral sequence | SpectralSequence | 谱序列 | 18T15 | L4 | ⚠️ |
| 10.9 | triangulated category | TriangulatedCategory | 三角范畴 | 18G80 | L4 | ✅ |
| 10.10 | t-structure | TStructure | t-结构 | 18G80 | L4 | ❌ |
| 10.11 | stable (∞,1)-category | StableInfinityCategory | 稳定(∞,1)-范畴 | 18N70 | L4 | ❌ |
| 10.12 | dg-category | DGCATEGORY | 微分分次范畴 | 18G35 | L4 | ❌ |
| 10.13 | A-∞ category | AInfinityCategory | A-无穷范畴 | 18G70 | L4 | ❌ |

---

## 二、按难度级别映射

### L1 - 基础 (Foundational)

| 概念 | nLab链接 | FormalMath文档 |
|-----|---------|--------------|
| Category | nlab:category | docs/02-代数结构/02-核心理论/范畴论/ |
| Functor | nlab:functor | docs/02-代数结构/02-核心理论/范畴论/ |
| Natural Transformation | nlab:natural+transformation | docs/02-代数结构/02-核心理论/范畴论/ |
| Limit | nlab:limit | docs/02-代数结构/02-核心理论/范畴论/ |
| Colimit | nlab:colimit | docs/02-代数结构/02-核心理论/范畴论/ |

### L2 - 核心 (Core)

| 概念 | nLab链接 | FormalMath文档 |
|-----|---------|--------------|
| Adjunction | nlab:adjoint+functor | docs/02-代数结构/02-核心理论/范畴论/ |
| Yoneda Lemma | nlab:Yoneda+lemma | docs/00-核心概念理解三问/11-核心定理多表征/05-米田引理-五种表征.md |
| Monoidal Category | nlab:monoidal+category | docs/02-代数结构/02-核心理论/范畴论/ |
| Abelian Category | nlab:abelian+category | docs/02-代数结构/02-核心理论/模论/ |
| Derived Category | nlab:derived+category | docs/00-知识层次体系/L3-理论建构层/01-代数方向/02-同调代数理论.md |

### L3 - 高级 (Advanced)

| 概念 | nLab链接 | FormalMath文档 |
|-----|---------|--------------|
| Topos | nlab:topos | docs/00-概念关联图谱/跨分支/05-逻辑几何Topos理论.md |
| Sheaf | nlab:sheaf | docs/13-代数几何/04-层与上同调-深度扩展版.md |
| 2-Category | nlab:2-category | docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md |
| Homotopy Type Theory | nlab:homotopy+type+theory | docs/11-高级数学/15-同伦类型论.md |
| Univalence Axiom | nlab:univalence | docs/11-高级数学/15-同伦类型论.md |

### L4 - 前沿 (Frontier)

| 概念 | nLab链接 | FormalMath文档 |
|-----|---------|--------------|
| (∞,1)-Category | nlab:quasi-category | 待创建 |
| Quasi-category | nlab:quasi-category | 待创建 |
| (∞,1)-Topos | nlab:(infinity,1)-topos | 待创建 |
| Higher Algebra | nlab:higher+algebra | 待创建 |
| E-∞ Ring | nlab:E-infinity+ring | 待创建 |

---

## 三、概念依赖关系图

```mermaid
graph TB
    subgraph L1[基础层 L1]
        CAT[Category 范畴]
        FUN[Functor 函子]
        NT[Natural Transformation 自然变换]
    end
    
    subgraph L2[核心层 L2]
        LIM[Limit 极限]
        ADJ[Adjunction 伴随]
        YON[Yoneda Lemma 米田引理]
        MON[Monoidal Category 单范畴]
    end
    
    subgraph L3[高级层 L3]
        TOP[Topos 拓扑斯]
        SHE[Sheaf 层]
        TWO[2-Category 2-范畴]
        BIC[Bicategory 双范畴]
        HOTT[Homotopy Type Theory 同伦类型论]
        DER[Derived Category 导出范畴]
    end
    
    subgraph L4[前沿层 L4]
        INF[(∞,1)-Category 无穷范畴]
        QCAT[Quasi-category 拟范畴]
        ITOP[(∞,1)-Topos 无穷拓扑斯]
        HIAL[Higher Algebra 高阶代数]
        EINF[E-∞ Ring E-无穷环]
    end
    
    CAT --> FUN --> NT --> ADJ
    CAT --> LIM --> YON
    CAT --> MON
    
    ADJ --> TOP
    LIM --> SHE --> TOP
    CAT --> TWO --> BIC --> INF
    
    NT --> HOTT
    MON --> HIAL
    
    INF --> QCAT --> ITOP
    HIAL --> EINF
    HOTT --> ITOP
```

---

## 四、形式化实现状态

### Lean 4实现状态

| 模块 | 路径 | 状态 | 覆盖率 |
|-----|-----|-----|-------|
| Category | Mathlib/CategoryTheory/Category | ✅ | 95% |
| Functor | Mathlib/CategoryTheory/Functor | ✅ | 90% |
| Limits | Mathlib/CategoryTheory/Limits | ✅ | 85% |
| Adjunction | Mathlib/CategoryTheory/Adjunction | ✅ | 80% |
| Monoidal | Mathlib/CategoryTheory/Monoidal | ⚠️ | 60% |
| Abelian | Mathlib/CategoryTheory/Abelian | ✅ | 75% |
| Topos | - | ❌ | 0% |
| HoTT | - | ⚠️ | 30% |
| Higher Category | - | ❌ | 0% |

### 建议新增Lean代码

```lean
-- 拟范畴基础定义（与nLab对齐）
structure QuasiCategory where
  underlying : SSet
  inner_horn_filling : ∀ (n : ℕ) (k : Fin n), 
    0 < k.val → k.val < n → 
    ∀ (f : Λ[n,k] → underlying), 
    ∃ (g : Δ[n] → underlying), 
    g ∘ hornInclusion n k = f

-- (∞,1)-范畴的同伦范畴
instance homotopy_category (C : QuasiCategory) : Category where
  Obj := C.underlying.obj 0
  Hom := λ X Y => homotopy_classes_of_morphisms C X Y
  id := λ X => identity_morphism C X
  comp := λ f g => compose_homotopy_classes C g f

-- Topos结构
elementary_topos_axioms (C : Category) : Prop := 
  has_finite_limits C ∧ 
  has_subobject_classifier C ∧ 
  cartesian_closed C

-- 几何态射
structure GeometricMorphism (E F : Category) where
  inverse_image : F ⥤ E
  direct_image : E ⥤ F
  adjunction : inverse_image ⊣ direct_image
  lex : preserves_finite_limits inverse_image
```

---

## 五、术语对照速查表

### 中文-英文-nLab术语对照

| 中文 | 英文 | nLab术语 | MSC |
|-----|-----|---------|-----|
| 范畴 | category | category | 18A05 |
| 函子 | functor | functor | 18A22 |
| 自然变换 | natural transformation | natural transformation | 18A23 |
| 极限 | limit | limit | 18A30 |
| 伴随 | adjunction | adjoint functor | 18A40 |
| 米田引理 | Yoneda lemma | Yoneda lemma | 18F20 |
| 2-范畴 | 2-category | 2-category | 18N10 |
| 双范畴 | bicategory | bicategory | 18N10 |
| 拟范畴 | quasi-category | quasi-category | 18N60 |
| 无穷范畴 | infinity category | (infinity,1)-category | 18N60 |
| 无穷群胚 | infinity groupoid | infinity-groupoid | 18N50 |
| 同伦类型论 | homotopy type theory | homotopy type theory | 03B38 |
| 单值公理 | univalence axiom | univalence | 03B38 |
| 拓扑斯 | topos | topos | 18B25 |
| 层 | sheaf | sheaf | 14F05 |
| 景 | site | site | 18F10 |
| 几何态射 | geometric morphism | geometric morphism | 18F10 |
| 子对象分类器 | subobject classifier | subobject classifier | 18B25 |
| 内部逻辑 | internal logic | internal logic | 03G30 |
| 单(∞,1)-范畴 | monoidal infinity category | monoidal (infinity,1)-category | 18N70 |
| Operad | operad | operad | 18M60 |
| E-无穷环 | E-infinity ring | E-infinity ring | 55P43 |
| 导出范畴 | derived category | derived category | 18G80 |
| 模型范畴 | model category | model category | 18N40 |
| 稳定(∞,1)-范畴 | stable infinity category | stable (infinity,1)-category | 18N70 |

---

## 六、更新日志

| 日期 | 版本 | 更新内容 |
|-----|-----|---------|
| 2026-04-04 | 1.0 | 初始版本，完成核心概念映射 |

---

**文档状态**: 完成  
**下次更新**: 2026年7月  
**维护团队**: FormalMath核心团队
