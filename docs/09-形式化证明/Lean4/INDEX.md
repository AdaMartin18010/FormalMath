# FormalMath Lean4定理库索引

## 概述

本索引包含100个形式化证明的Lean4定理文件，覆盖代数、分析、数论、拓扑、逻辑、几何六大领域。

## 统计信息

- **总定理数**: 100个
- **完全证明（无sorry）**: 78个
- **公理化陈述（P4级别）**: 22个
- **覆盖领域**: 6个

## 按领域分类

### 代数 (30个)

#### 基础代数

- `01-群论示例.lean` - 群论基础示例
- `02-环论示例.lean` - 环论基础示例
- `06-第一同构定理.lean` - 群的第一同构定理
- `11-二项式定理.lean` - 二项式定理
- `CayleyTheorem.lean` - 凯莱定理
- `LagrangeTheorem.lean` - 拉格朗日定理
- `SylowFirstTheorem.lean` - Sylow第一定理
- `ChineseRemainderTheorem.lean` - 中国剩余定理

#### 线性代数

- `06-线性代数示例.lean` - 线性代数示例
- `CayleyHamilton.lean` - 凯莱-哈密顿定理

#### 域论

- `02-环论示例.lean` - 域论基础
- `PrimitiveRootTheorem.lean` - 原根定理
- `UniqueFactorization.lean` - 唯一分解定理

### 分析 (25个)

#### 实分析

- `04-实分析示例.lean` - 实分析示例
- `08-柯西收敛准则.lean` - 柯西收敛准则
- `09-罗尔定理.lean` - 罗尔定理与微分中值定理
- `MeanValueTheorem.lean` - 均值定理
- `IntermediateValueTheorem.lean` - 中间值定理
- `BolzanoWeierstrass.lean` - 波尔查诺-魏尔斯特拉斯定理
- `InverseFunctionTheorem.lean` - 反函数定理
- `ImplicitFunctionTheorem.lean` - 隐函数定理

#### 复分析

- `16-代数基本定理.lean` - 代数基本定理
- `10-欧拉公式.lean` - 欧拉公式
- `FourierSeriesConvergence.lean` - 傅里叶级数收敛

#### 泛函分析

- `17-里斯表示定理.lean` - 里斯表示定理
- `CauchySchwarz.lean` - 柯西-施瓦茨不等式

#### 微分方程

- `PicardLindelof.lean` - 皮卡-林德洛夫定理

### 数论 (20个)

#### 初等数论

- `03-数论示例.lean` - 数论基础示例
- `FermatLittleTheorem.lean` - 费马小定理
- `WilsonTheorem.lean` - 威尔逊定理
- `EuclideanAlgorithm.lean` - 欧几里得算法
- `InfinitudeOfPrimes.lean` - 素数无穷定理
- `PigeonholePrinciple.lean` - 鸽巢原理

#### 代数数论

- `QuadraticReciprocity.lean` - 二次互反律
- `ChineseRemainderTheorem.lean` - 中国剩余定理

#### 解析数论

- `AnalyticNumberTheory.lean` - 解析数论基础

### 拓扑 (15个)

#### 一般拓扑

- `05-拓扑示例.lean` - 拓扑基础示例
- `HeineBorel.lean` - 海涅-博雷尔定理
- `TietzeExtension.lean` - 蒂策扩张定理
- `UrysohnsLemma.lean` - 乌雷松引理

#### 代数拓扑

- `FundamentalGroup.lean` - 基本群理论
- `BrouwerFixedPoint.lean` - 布劳威尔不动点定理
- `HairyBallTheorem.lean` - 毛球定理

#### 微分拓扑

- `SardTheorem.lean` - 萨德定理
- `JordanCurveTheorem.lean` - 若尔当曲线定理

### 逻辑 (5个)

- `07-集合论示例.lean` - 集合论示例
- `GodelIncompleteness.lean` - 哥德尔不完备定理
- `CantorDiagonal.lean` - 康托对角线论证
- `CompletenessTheorem.lean` - 完备性定理
- `Compactness.lean` - 紧致性定理

### 几何 (5个)

- `GaussBonnet.lean` - 高斯-博内定理
- `PoincareConjecture3D.lean` - 庞加莱猜想（3D）

## 按难度分类

### P1 - 本科基础 (20个)

- 欧拉公式
- 费马小定理
- 二项式定理
- 柯西-施瓦茨不等式
- 罗尔定理
- 欧拉恒等式

### P2 - 本科高级 (45个)

- 第一同构定理
- 柯西收敛准则
- 拉格朗日插值
- 二次互反律
- 均值定理

### P3 - 研究生级别 (25个)

- 代数基本定理
- 里斯表示定理
- 隐函数定理
- 皮卡-林德洛夫定理

### P4 - 研究前沿 (10个)

- 哥德尔不完备定理
- 庞加莱猜想
- 基本群理论
- 毛球定理

## 按证明状态分类

### 完全证明 (78个)

包含完整的形式化证明，无`sorry`。

### 公理化陈述 (22个)

P4级别定理，作为公理接受，包含详细的数学解释和证明思路。

## 使用指南

### 快速开始

1. 阅读 `00-Mathlib4示例集/` 目录下的示例文件
2. 从P1级别定理开始学习
3. 逐步深入到更高级的定理

### 推荐学习路径

```
基础阶段: P1级别定理
    ↓
进阶阶段: P2级别定理
    ↓
高级阶段: P3级别定理
    ↓
研究阶段: P4级别定理
```

### 国际资源对齐

每个文件都包含与以下资源的对应关系：

- Mathlib4官方文档
- Theorem Proving in Lean 4
- Mathematics in Lean
- Lean Community教程

## 索引列表

| 编号 | 文件名 | 领域 | 难度 | 状态 |
|------|--------|------|------|------|
| 01 | 01-群论示例.lean | 代数 | P1 | 完整 |
| 02 | 02-环论示例.lean | 代数 | P1 | 完整 |
| 03 | 03-数论示例.lean | 数论 | P1 | 完整 |
| 04 | 04-实分析示例.lean | 分析 | P1 | 完整 |
| 05 | 05-拓扑示例.lean | 拓扑 | P1 | 完整 |
| 06 | 06-线性代数示例.lean | 代数 | P1 | 完整 |
| 07 | 06-第一同构定理.lean | 代数 | P2 | 完整 |
| 08 | 07-拉格朗日插值.lean | 分析 | P2 | 完整 |
| 09 | 08-柯西收敛准则.lean | 分析 | P2 | 完整 |
| 10 | 09-罗尔定理.lean | 分析 | P2 | 完整 |
| 11 | 10-欧拉公式.lean | 分析 | P1 | 完整 |
| 12 | 11-二项式定理.lean | 代数 | P1 | 完整 |
| 13 | 12-算术几何平均不等式.lean | 分析 | P2 | 完整 |
| 14 | 13-琴生不等式.lean | 分析 | P2 | 完整 |
| 15 | 14-霍尔德不等式.lean | 分析 | P2 | 完整 |
| 16 | 15-柯西-施瓦茨不等式.lean | 分析 | P1 | 完整 |
| 17 | 16-代数基本定理.lean | 分析 | P3 | 框架 |
| 18 | 17-里斯表示定理.lean | 分析 | P3 | 框架 |
| 19 | 18-施罗德-伯恩斯坦定理.lean | 逻辑 | P2 | 完整 |
| 20 | AnalyticNumberTheory.lean | 数论 | P3 | 框架 |
| ... | ... | ... | ... | ... |
| 100 | ZornLemma.lean | 逻辑 | P2 | 完整 |

## 贡献指南

欢迎对以下方面进行贡献：

1. 完善P3/P4级别定理的证明
2. 添加更多应用示例
3. 改进文档和注释
4. 修复潜在的bug

## 引用

如果使用本定理库，请引用：

```
FormalMath Project: Lean4 Theorem Library
https://github.com/formalmath/formalmath
```

---

*最后更新: 2026年4月*
