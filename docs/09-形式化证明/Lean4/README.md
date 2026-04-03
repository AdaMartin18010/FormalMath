---
msc_primary: "68V20"
msc_secondary: ["03B35", "03B70"]
---

# FormalMath - Mathlib4对齐形式化证明库

## 概述

本目录包含FormalMath项目与Mathlib4对齐的核心定理形式化证明。
所有代码使用Lean 4编写，与Mathlib 4.19.0版本对齐。

## 15个核心定理

| # | 定理名称 | Mathlib4对应 | 文件名 | 领域 | 状态 |
|---|----------|--------------|--------|------|------|
| 1 | 拉格朗日定理 | `Subgroup.index_mul_card` | `LagrangeTheorem.lean` | 代数结构 | ✅ 完成 |
| 2 | 第一同构定理 | `MonoidHom.quotientKerEquivRange` | `FirstIsomorphismTheorem.lean` | 代数结构 | ✅ 完成 |
| 3 | 唯一分解定理 | `UniqueFactorizationMonoid` | `UniqueFactorization.lean` | 代数结构 | ✅ 完成 |
| 4 | Cayley定理 | `Cayley.embedding` | `CayleyTheorem.lean` | 代数结构 | ✅ 完成 |
| 5 | Sylow第一定理 | `Sylow.exists_subgroup_card_pow_prime` | `SylowFirstTheorem.lean` | 代数结构 | ✅ 完成 |
| 6 | 中值定理 | `exists_hasDerivAt_eq_slope` | `MeanValueTheorem.lean` | 分析学 | ✅ 完成 |
| 7 | Bolzano-Weierstrass定理 | `BolzanoWeierstrass.tendsto_subseq` | `BolzanoWeierstrass.lean` | 分析学 | ✅ 完成 |
| 8 | 介值定理 | `intermediate_value_Icc` | `IntermediateValueTheorem.lean` | 分析学 | ✅ 完成 |
| 9 | Heine-Borel定理 | `isCompact_iff_isClosed_bounded` | `HeineBorel.lean` | 分析学 | ✅ 完成 |
| 10 | 费马小定理 | `ZMod.pow_card` | `FermatLittleTheorem.lean` | 数论 | ✅ 完成 |
| 11 | 欧几里得算法 | `Nat.gcd_comm`, `EuclideanDomain` | `EuclideanAlgorithm.lean` | 数论 | ✅ 完成 |
| 12 | 素数无穷多 | `Nat.infinite_setOf_prime` | `InfinitudeOfPrimes.lean` | 数论 | ✅ 完成 |
| 13 | 康托尔定理 | `Cardinal.cantor` | `CantorDiagonal.lean` | 集合论 | ✅ 完成 |
| 14 | 鸽巢原理 | `Fintype.exists_ne_map_eq_of_card_lt` | `PigeonholePrinciple.lean` | 组合数学 | ✅ 完成 |
| 15 | 无穷鸽巢原理 | `infinite_pigeonhole` | `InfinitePigeonhole.lean` | 集合论 | ✅ 完成 |

## 优先级分类

### P0级（基础代数）

- `LagrangeTheorem.lean` - 群论基础
- `FirstIsomorphismTheorem.lean` - 同态基本定理
- `UniqueFactorization.lean` - 环论基础
- `CayleyTheorem.lean` - 群的置换表示
- `SylowFirstTheorem.lean` - 有限群分类基础

### P1级（分析与拓扑）

- `MeanValueTheorem.lean` - 微积分核心
- `BolzanoWeierstrass.lean` - 实分析基础
- `IntermediateValueTheorem.lean` - 连续性核心
- `HeineBorel.lean` - 紧致性理论
- `BrouwerFixedPoint.lean` - 拓扑学应用
- `Compactness.lean` - 拓扑基础

### P2级（数论与逻辑）

- `FermatLittleTheorem.lean` - 初等数论
- `EuclideanAlgorithm.lean` - 算法数论
- `InfinitudeOfPrimes.lean` - 素数理论
- `CantorDiagonal.lean` - 集合论
- `PigeonholePrinciple.lean` - 组合数学
- `InfinitePigeonhole.lean` - 无穷组合
- `FundamentalTheoremAlgebra.lean` - 代数与分析
- `GodelIncompleteness.lean` - 数理逻辑

## 使用指南

### 环境要求

```bash
# Lean 4 版本要求
lean --version  # 需要 ≥ 4.19.0

# 安装依赖
lake update mathlib
```

### 编译代码

```bash
# 在Lean4目录下
lake build

# 检查所有文件
lean *.lean
```

### 导入模块

```lean
import docs.形式化证明.Lean4.LagrangeTheorem
import docs.形式化证明.Lean4.FirstIsomorphismTheorem
```

## 代码结构

每个定理文件包含：

1. **Mathlib4对应说明** - 定理的Mathlib4位置和对应关系
2. **数学背景** - 定理的数学意义和历史
3. **形式化定义** - 核心概念的形式化
4. **主定理证明** - 完整的Lean4证明
5. **应用示例** - 定理的具体应用

```
theorem_file.lean
├── 导入语句 (import)
├── 命名空间定义 (namespace)
├── 核心概念 (definitions)
├── 辅助引理 (lemmas)
├── 主定理证明 (main theorem)
└── 应用示例 (examples)
```

## 与Mathlib4的对齐策略

### 1. 直接引用

对于Mathlib4中已完整实现的定理，直接引用：

```lean
theorem my_theorem : ... := by
  exact Mathlib4.theorem_name
```

### 2. 补充证明

对于Mathlib4中有定义但缺少特定视角的证明，补充证明：

```lean
theorem alternative_proof : ... := by
  -- 不同的证明方法
```

### 3. 教学版本

为教学目的提供更详细的证明版本：

```lean
theorem detailed_proof : ... := by
  -- 分步详细注释
```

## 定理依赖关系

```
基础层:
├── PigeonholePrinciple.lean
├── InfinitePigeonhole.lean
└── EuclideanAlgorithm.lean

代数层:
├── LagrangeTheorem.lean
│   └── (使用) PigeonholePrinciple
├── FirstIsomorphismTheorem.lean
│   └── (使用) LagrangeTheorem
├── CayleyTheorem.lean
│   └── (使用) LagrangeTheorem
└── SylowFirstTheorem.lean
    └── (使用) LagrangeTheorem

分析层:
├── MeanValueTheorem.lean
├── BolzanoWeierstrass.lean
├── IntermediateValueTheorem.lean
└── HeineBorel.lean
    └── (使用) BolzanoWeierstrass

数论层:
├── FermatLittleTheorem.lean
│   └── (使用) LagrangeTheorem
├── InfinitudeOfPrimes.lean
└── UniqueFactorization.lean
    └── (使用) EuclideanAlgorithm

集合论层:
├── CantorDiagonal.lean
└── (与所有层关联)
```

## 扩展计划

### 近期（2026年Q2）

- [x] 补充更多群论定理（Cayley定理、Sylow定理）
- [x] 完善环论内容（欧几里得算法、素数无穷多）
- [x] 添加分析学基础（Bolzano-Weierstrass、介值定理）
- [ ] 添加线性代数基础（秩-零化度定理、谱定理）

### 中期（2026年Q3-Q4）

- [ ] 建立更完整的分析学分支（一致连续性、Riemann积分）
- [ ] 完善拓扑学内容（连通性、道路连通性）
- [ ] 添加测度论基础
- [ ] 添加复分析基础（Cauchy积分公式）

### 长期（2027年）

- [ ] 代数几何初步（Hilbert零点定理）
- [ ] 同调代数（长正合序列、导出函子）
- [ ] 范畴论应用（伴随函子、极限）
- [ ] 泛函分析基础（Hahn-Banach定理）

## 贡献指南

### 添加新定理

1. 在对应优先级目录下创建`.lean`文件
2. 按照模板填写Mathlib4对应信息
3. 提供完整的Lean4证明
4. 添加数学背景和应用示例
5. 更新本README

### 代码规范

- 使用4空格缩进
- 遵循Mathlib4命名约定
- 添加详细的注释说明
- 包含完整的导入语句
- 每个定理包含Mathlib4对应关系注释

## 参考文献

### Mathlib4资源

- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

### 数学参考

- Dummit, D. S., & Foote, R. M. *Abstract Algebra*
- Munkres, J. *Topology*
- Rudin, W. *Principles of Mathematical Analysis*
- Hardy, G. H., & Wright, E. M. *An Introduction to the Theory of Numbers*
- Boolos, G., et al. *Computability and Logic*

## 维护信息

- **最后更新**: 2026年4月3日
- **Mathlib4版本**: 4.19.0
- **Lean版本**: 4.19.0
- **维护者**: FormalMath项目团队
- **定理数量**: 15个核心定理

## 许可证

本目录下的代码遵循与Mathlib4相同的许可证（Apache 2.0）。

---

**FormalMath项目**: 建立与Mathlib4紧密对齐的形式化数学知识体系
