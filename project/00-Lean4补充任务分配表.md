---
title: "银层文档 Lean4 代码补充任务分配表"
msc_primary: 00A99
date: "2026-04-18"
status: "queued"
---

# Lean4 代码补充任务分配表

> **触发条件**: 银层攻坚全部完成后启动
> **目标**: 为所有银层文档嵌入可编译的 Lean4 代码框架

---

## MIT 18.06 线性代数（8篇缺Lean4）

| 章节 | 文档 | 待补充Lean4内容 | 优先级 | 预计工时 |
|------|------|----------------|--------|---------|
| Ch.1 | 线性方程组的几何 | `LinearSystem` 定义、解存在性判定 | P1 | 2h |
| Ch.2 | 矩阵消元法 | `RowOperation`、RREF算法 | P1 | 2h |
| Ch.3 | 矩阵运算与逆矩阵 | `Matrix.mul`、逆矩阵存在判定 | P1 | 2h |
| Ch.4 | LU分解 | `LUDecomposition`、三角矩阵 | P2 | 3h |
| Ch.5 | 向量空间与子空间 | `VectorSpace` typeclass、`Subspace` | P1 | 2h |
| Ch.6 | 列空间与零空间 | `colSpace`、`nullSpace`、`rank` | P1 | 2h |
| Ch.7 | 求解线性方程组 | `solveLinearSystem`、通解参数化 | P2 | 3h |
| Ch.8 | 线性无关基与维数 | `LinearIndependent`、`Basis`、`finrank` | P1 | 3h |
| Ch.9 | 四大基本子空间 | 四大子空间定义与正交关系 | P2 | 3h |
| Ch.10 | 正交性与投影 | `innerProduct`、`projectionMatrix` | P2 | 3h |
| Ch.11 | 最小二乘与Gram-Schmidt | `leastSquares`、`gramSchmidt` | P2 | 3h |
| Ch.12 | 行列式 | `Matrix.det` 性质验证 | P1 | 4h |
| Ch.13 | 特征值与特征向量 | `eigenvalues`、`eigenvectors` | P1 | 4h |
| Ch.14 | 对角化与对称矩阵 | `diagonalizable`、`SpectralTheorem` | P1 | 4h |
| Ch.15 | SVD与线性变换 | `SVD`、`pseudoInverse` | P2 | 4h |

---

## MIT 18.100A 实分析（2篇缺Lean4）

| 定理 | 文档 | 待补充Lean4内容 | 优先级 | 预计工时 |
|------|------|----------------|--------|---------|
| 比较判别法 | 比较判别法.md | `ComparisonTest` 级数收敛判定 | P2 | 2h |
| 比值/根值判别法 | 比值根值判别法.md | `RatioTest`、`RootTest` | P2 | 2h |

---

## MIT 18.701 抽象代数（0篇缺Lean4）

✅ 全部已嵌入 Lean4 代码

---

## Harvard 232br 代数几何（待评估）

| 章节 | 状态 | 备注 |
|------|------|------|
| Chapter II | 部分有 `sorry` 占位 | 需逐步补全 |
| Chapter III | 部分有 `sorry` 占位 | 需逐步补全 |
| Chapter IV-V | 待生产 | 生产时同步嵌入 |

---

## Stanford FOAG（待评估）

| 章节 | 状态 | 备注 |
|------|------|------|
| Part VI | 待生产 | 生产时同步嵌入 |

---

## 执行策略

1. **高优先级先行**: MIT 18.06 Ch.1–3, 5–6, 12–14（核心基础内容）
2. **Mathlib4 复用**: 优先使用 Mathlib4 已有定义，减少重复劳动
3. **框架先行**: 先完成定义和定理陈述，`sorry` 占位，后续补证明
4. **审校联动**: Lean4 代码完成一轮后，由形式化专家审校

---

**预计总工时**: 约 40–50 小时（单人不间断）
**建议执行方式**: 启动 2–3 个并行 Agent，每 Agent 负责 5 篇
