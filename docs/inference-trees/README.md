---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 几何拓扑推理树索引
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 几何拓扑推理树索引

本目录包含几何与拓扑学核心定理的推理树集合，采用 Markdown + Mermaid 语法编写。

## 目录结构

### 一、拓扑学推理树 (4个)

| 文件名 | 主题 | 核心内容 |
|--------|------|----------|
| [topology-compactness-equivalence.md](./topology-compactness-equivalence.md) | 紧致性等价条件 | 开覆盖、FIP、序列紧致、Heine-Borel、Tychonoff |
| [topology-connectedness-chain.md](./topology-connectedness-chain.md) | 连通性性质链 | 道路连通、连通、局部连通、单连通的层次关系 |
| [topology-separation-axioms.md](./topology-separation-axioms.md) | 分离公理层次 | T₀到T₆的严格蕴含链及Urysohn/Tietze定理 |
| [topology-tychonoff-theorem.md](./topology-tychonoff-theorem.md) | Tychonoff定理 | 乘积空间紧致性的多种证明及与选择公理关系 |

### 二、代数拓扑推理树 (5个)

| 文件名 | 主题 | 核心内容 |
|--------|------|----------|
| [alg-top-fundamental-group-strategy.md](./alg-top-fundamental-group-strategy.md) | 基本群计算策略 | 典型空间基本群、覆叠空间、形变收缩计算法 |
| [alg-top-seifert-van-kampen.md](./alg-top-seifert-van-kampen.md) | Seifert-van Kampen定理 | 基本群计算核心定理的完整推导 |
| [alg-top-homology-long-exact.md](./alg-top-homology-long-exact.md) | 同调群长正合列 | 空间对同调的长正合列构造 |
| [alg-top-mayer-vietoris.md](./alg-top-mayer-vietoris.md) | Mayer-Vietoris序列 | 同调计算核心工具及应用 |
| [alg-top-universal-coefficient.md](./alg-top-universal-coefficient.md) | 万有系数定理 | 整系数与任意系数同调的关系 |

### 三、微分几何推理树 (5个)

| 文件名 | 主题 | 核心内容 |
|--------|------|----------|
| [diff-geo-manifold-hierarchy.md](./diff-geo-manifold-hierarchy.md) | 流形定义层次 | 拓扑流形到光滑流形的严格构造 |
| [diff-geo-tensor-analysis.md](./diff-geo-tensor-analysis.md) | 张量分析推导 | 张量代数、协变导数、曲率张量 |
| [diff-geo-curvature-tensor.md](./diff-geo-curvature-tensor.md) | 曲率张量性质 | Riemann曲率、Ricci、Weyl张量的代数与微分恒等式 |
| [diff-geo-gauss-bonnet.md](./diff-geo-gauss-bonnet.md) | Gauss-Bonnet定理 | 经典与高维形式、Chern证明、拓扑意义 |
| [diff-geo-geodesic-equation.md](./diff-geo-geodesic-equation.md) | 测地线方程推导 | 变分法、自平行、Jacobi场 |

### 四、代数几何推理树 (3个)

| 文件名 | 主题 | 核心内容 |
|--------|------|----------|
| [alg-geo-scheme-hierarchy.md](./alg-geo-scheme-hierarchy.md) | 概形构造层次 | 从代数集到概形的Grothendieck构造 |
| [alg-geo-sheaf-cohomology.md](./alg-geo-sheaf-cohomology.md) | 层上同调推导 | 导出函子上同调、Serre定理、对偶 |
| [alg-geo-riemann-roch.md](./alg-geo-riemann-roch.md) | Riemann-Roch定理概述 | 经典到高维：HRR、GRR、历史发展 |

## 知识依赖关系

```

拓扑学基础
    ↓
代数拓扑（基本群、同调）
    ↓
微分几何（流形、张量、曲率）
    ↓
代数几何（概形、层、Riemann-Roch）

```

## 使用指南

1. **阅读顺序**: 建议按拓扑学 → 代数拓扑 → 微分几何 → 代数几何的顺序
2. **推理树解读**: 
   - 实线箭头表示定义或蕴含关系
   - 虚线箭头表示等价或条件依赖
   - 颜色深浅表示抽象层次
3. **公式查看**: 所有文件支持标准Markdown渲染，公式使用LaTeX语法

## 参考资源

- **拓扑学**: Munkres《Topology》, Hatcher《Algebraic Topology》
- **微分几何**: do Carmo《Riemannian Geometry》, Lee《Smooth Manifolds》
- **代数几何**: Hartshorne《Algebraic Geometry》, Vakil《The Rising Sea》

---

*生成时间: 2026年4月*
*总计: 17个推理树文件*
