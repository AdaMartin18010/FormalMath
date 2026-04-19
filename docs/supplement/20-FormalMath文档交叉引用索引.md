---
title: "FormalMath文档交叉引用索引"
msc_primary: "00"
---

# FormalMath 文档交叉引用索引

---

## 1. 索引说明

本文档提供FormalMath项目所有文档之间的交叉引用关系，帮助读者：
- 快速定位相关概念
- 理解知识依赖关系
- 规划学习路径

---

## 2. 按分支索引

### 2.1 基础数学 (01-基础数学)

| 文档 | 相关文档 | 关系类型 |
|-----|---------|---------|
| 00-集合论基础 | 数理逻辑、分析学 | 前置知识 |
| 数理逻辑基础 | 哥德尔不完备定理 | 扩展应用 |
| 数学归纳法 | 数论、组合数学 | 核心工具 |
| 数论习题精解 | 代数学基础、素数定理 | 练习深化 |

### 2.2 代数结构 (02-代数结构)

| 文档 | 相关文档 | 关系类型 |
|-----|---------|---------|
| 群论基础 | 群论习题精讲、拓扑学 | 理论基础 |
| 环论与域论 | 代数数论、代数几何 | 进阶应用 |
| 线性代数 | MIT 18.06、CS 229 | 课程对齐 |
| Sylow定理 | 群论习题精讲 | 应用实例 |

### 2.3 分析学 (03-分析学)

| 文档 | 相关文档 | 关系类型 |
|-----|---------|---------|
| 实数系统 | 实分析核心习题集 | 基础-应用 |
| 极限理论 | 微积分、级数理论 | 核心理论 |
| 实分析习题集 | 测度论、Lp空间 | 进阶铺垫 |
| 复分析 | Math 106、留数定理 | 课程对齐 |

### 2.4 几何拓扑 (04-几何拓扑)

| 文档 | 相关文档 | 关系类型 |
|-----|---------|---------|
| 拓扑学基础 | 代数拓扑习题精解 | 理论-应用 |
| 微分形式 | Stokes定理 | 核心工具 |
| 代数拓扑 | Jordan曲线定理 | 前沿研究 |
| 微分几何 | 数学物理、广义相对论 | 物理应用 |

### 2.5 形式化证明 (09-形式化证明)

| 定理 | 前置知识 | 应用方向 |
|-----|---------|---------|
| 中值定理 | 连续性、微分 | 分析学基础 |
| Sylow定理 | 群论基础 | 有限群分类 |
| 素数定理 | 解析数论 | 密码学 |
| Jordan曲线 | 代数拓扑 | 计算几何 |
| Gödel不完备 | 数理逻辑 | 元数学 |

---

## 3. 按主题索引

### 3.1 收敛性主题

```
数列收敛
├── 定义: docs/03-分析学/序列与级数基础
├── 性质: docs/03-分析学/极限理论
├── 习题: docs/03-分析学/supplement/实分析核心习题集
├── 决策树: docs/supplement/09-数学问题求解决策树大全
└── 反例: docs/supplement/02-数学经典反例大全

函数项级数
├── 一致收敛: docs/03-分析学/函数序列与均匀收敛
├── 对比矩阵: docs/supplement/03-数学概念多维对比矩阵
└── 应用: docs/03-分析学/Fourier分析
```

### 3.2 代数结构主题

```
群论
├── 基础: docs/02-代数结构/群论基础
├── 习题: docs/02-代数结构/supplement/群论习题精讲
├── Sylow定理: docs/02-代数结构/Sylow定理
├── 应用: docs/02-代数结构/Cayley定理
└── Lean4: docs/09-形式化证明/Lean4/SylowFirstTheorem.lean

线性代数
├── 基础: docs/02-代数结构/线性代数基础
├── MIT对齐: docs/supplement/05-MIT-18.01-18.06微积分与微分方程系列精讲
├── Stanford对齐: docs/supplement/10-Stanford-CS229-EE364A-Math106系列精讲
└── 应用: docs/supplement/18-数学在金融生物CS中的应用
```

### 3.3 拓扑学主题

```
紧致性
├── 定义: docs/04-几何拓扑/拓扑学基础
├── 对比矩阵: docs/supplement/03-数学概念多维对比矩阵
├── 定理: docs/09-形式化证明/Lean4/HeineBorel.lean
└── 反例: docs/supplement/02-数学经典反例大全

代数拓扑
├── 基础: docs/04-几何拓扑/supplement/06-代数拓扑习题精解
├── 应用: docs/09-形式化证明/Lean4/BrouwerFixedPoint.lean
└── 前沿: docs/09-形式化证明/Lean4/HairyBallTheorem.lean
```

---

## 4. 国际课程对齐索引

### 4.1 MIT系列

| MIT课程 | FormalMath文档 | 对齐深度 |
|--------|---------------|---------|
| 18.01 | docs/03-分析学/微积分基础 | 完全对齐 |
| 18.02 | docs/03-分析学/多变量微积分 | 完全对齐 |
| 18.03 | docs/05-ODE/常微分方程基础 | 完全对齐 |
| 18.06 | docs/02-代数结构/线性代数 | 完全对齐 |
| 18.100A | docs/supplement/05-MIT-18.01-18.06微积分与微分方程系列精讲 | 专题对齐 |

### 4.2 其他顶尖大学

| 大学 | 课程 | FormalMath文档 |
|-----|------|---------------|
| Harvard | Math 55 | docs/supplement/06-Harvard-Math55高等数学系列精讲 |
| Princeton | MAT 215/216 | docs/supplement/07-Princeton-MAT215-216-425分析代数系列精讲 |
| Stanford | CS229/EE364A | docs/supplement/10-Stanford-CS229-EE364A-Math106系列精讲 |
| ETH Zurich | Analysis I-III | docs/supplement/11-ETH-Zurich分析系列精讲 |
| Cambridge | Tripos | docs/supplement/14-Cambridge-Tripos数学系列精讲 |

---

## 5. 习题与实例索引

### 5.1 按难度分级

**基础级** (适合大一):
- docs/01-基础数学/supplement/数学归纳法与证明技巧
- docs/03-分析学/supplement/数学分析解题策略
- docs/02-代数结构/supplement/群论习题精讲

**进阶级** (适合大二/三):
- docs/03-分析学/supplement/实分析核心习题集
- docs/04-几何拓扑/supplement/代数拓扑习题精解
- docs/06-概率统计/supplement/概率论习题精解

**高级** (适合研究生):
- docs/09-形式化证明/Lean4/各定理证明
- docs/supplement/15-数论与动力系统高级反例
- docs/supplement/12-PDE与代数几何高级反例

### 5.2 按应用场景

**理论研究**:
- 反例大全系列
- 形式化证明
- 高级专题

**工程应用**:
- Stanford系列
- 数学应用文档
- 数值计算

**竞赛准备**:
- 数学竞赛解题策略
- 习题精解系列

---

## 6. Lean4定理索引

### 6.1 已形式化定理

| 定理 | 文档位置 | 依赖 |
|-----|---------|-----|
| IntermediateValueTheorem | Lean4/IntermediateValueTheorem.lean | 连续性 |
| MeanValueTheorem | Lean4/MeanValueTheorem.lean | 微分 |
| FundamentalTheoremOfAlgebra | Lean4/FundamentalTheoremOfAlgebra.lean | 复分析 |
| SylowFirstTheorem | Lean4/SylowFirstTheorem.lean | 群论 |
| CentralLimitTheorem | Lean4/CentralLimitTheorem.lean | 概率论 |

### 6.2 框架占位定理

| 定理 | 文档位置 | 待完善 |
|-----|---------|-------|
| StokesTheorem | Lean4/StokesTheorem.lean | 微分形式边界积分 |
| JordanCurveTheorem | Lean4/JordanCurveTheorem.lean | 平面拓扑 |
| GodelIncompleteness | Lean4/GodelIncompleteness.lean | 元数学 |
| PrimeNumberTheorem | Lean4/PrimeNumberTheorem.lean | 解析数论 |

---

## 7. 快速参考表

### 7.1 概念查找

| 想查什么 | 去哪里找 |
|---------|---------|
| 定义 | docs/XX-分支名/概念名 |
| 定理证明 | docs/09-形式化证明/Lean4/定理名.lean |
| 习题 | docs/XX-分支名/supplement/习题精解 |
| 反例 | docs/supplement/02-数学经典反例大全 |
| 应用实例 | docs/supplement/18-数学在金融生物CS中的应用 |
| 课程对齐 | docs/supplement/XX-大学系列精讲 |
| 解题策略 | docs/supplement/09-数学问题求解决策树大全 |
| 概念对比 | docs/supplement/03-数学概念多维对比矩阵 |

### 7.2 学习路径

**纯数学路径**:
```
基础数学 → 代数结构 → 分析学 → 几何拓扑 → 形式化证明/高级专题
```

**应用数学路径**:
```
基础数学 → 分析学 → ODE/PDE → 数值计算 → 应用领域
```

**计算机科学路径**:
```
基础数学 → 线性代数 → 概率统计 → 优化 → 机器学习/算法
```

---

*本文档为FormalMath项目交叉引用索引*  
*最后更新: Round 18*
