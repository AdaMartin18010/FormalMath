---
title: 计算数学
msc_primary: 00A99
msc_secondary:
- 00A99
- 00A99
- 00A99
processed_at: '2026-04-05'
---
# 计算数学 / Computational Mathematics

**最后更新**: 2026年4月4日

---

## 📋 分支概述

计算数学是研究数值方法和算法的数学分支，致力于开发求解连续和离散数学问题的有效计算技术。核心内容包括数值线性代数、微分方程数值解、优化算法、逼近理论等。计算数学是现代科学与工程计算的基石，为天气预报、流体力学、金融建模等领域提供计算工具。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 数值线性代数、有限元方法、谱方法 | 65Fxx, 65Nxx | Golub & Van Loan |
| [02-核心定理](./02-核心定理.md) | Lax等价定理、收敛性分析 | 65J10, 65M12 | Trefethen |
| [03-实战问题](./03-实战问题.md) | 10个数值计算问题 | 65xx | Quarteroni |

---

## 🎯 理论架构

```

计算数学
├── 数值线性代数
│   ├── 直接法（LU、Cholesky、QR分解）
│   ├── 迭代法（Jacobi、Gauss-Seidel、CG）
│   ├── 特征值计算
│   └── 稀疏矩阵技术
├── 插值与逼近
│   ├── 多项式插值
│   ├── 样条函数
│   ├── 最小二乘逼近
│   └── FFT与谱方法
├── 微分方程数值解
│   ├── 常微分方程（Euler、Runge-Kutta）
│   ├── 有限差分法
│   ├── 有限元方法
│   └── 谱方法
├── 优化算法
│   ├── 无约束优化
│   ├── 约束优化
│   ├── 凸优化
│   └── 随机优化
└── 高性能计算
    ├── 并行算法
    ├── 快速算法
    └── 不确定性量化

```

---

## 📚 核心人物

- **John von Neumann (1903-1957)**: 现代计算机和数值分析奠基人
- **Cornelius Lanczos (1893-1974)**: Lanczos算法、变分原理
- **Magnus Hestenes & Eduard Stiefel**: 共轭梯度法（1952）
- **James H. Wilkinson (1919-1986)**: 舍入误差分析、向后误差分析
- **Lloyd N. Trefethen (1955-)**: 谱方法、伪谱、数值分析现代观点
- **Gene H. Golub (1932-2007)**: 矩阵计算、SVD、科学计算

---

## 🔗 与其他分支的联系

- **线性代数**: 矩阵计算的理论基础
- **分析学**: 收敛性、稳定性、误差估计
- **微分方程**: 离散化方法和数值积分
- **逼近论**: 函数逼近、插值理论
- **优化理论**: 数值优化算法
- **计算机科学**: 算法设计、并行计算、浮点运算

---

## 📖 学习路径建议

1. **先修知识**: 线性代数、微积分、微分方程、基础编程
2. **第一阶段**: 数值线性代数（直接法和迭代法）
3. **第二阶段**: 插值逼近和数值积分
4. **第三阶段**: 微分方程数值解（ODE和PDE）
5. **第四阶段**: 高级专题（谱方法、高维问题、不确定性量化）

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Gene H. Golub & Charles F. Van Loan** - *Matrix Computations* (4th Edition, 2013)
- **Lloyd N. Trefethen & David Bau III** - *Numerical Linear Algebra* (1997)
- **Alfio Quarteroni, Riccardo Sacco & Fausto Saleri** - *Numerical Mathematics* (2nd Edition, 2007)
- **Nicholas J. Higham** - *Accuracy and Stability of Numerical Algorithms* (2nd Edition, 2002)
- **Jan S. Hesthaven** - *Numerical Methods for Conservation Laws* (2018)

---

*最后更新：2026年4月*
