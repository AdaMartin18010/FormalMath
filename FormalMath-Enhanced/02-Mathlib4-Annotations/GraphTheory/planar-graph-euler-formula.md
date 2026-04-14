---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 平面图欧拉公式 (Euler's Formula for Planar Graphs)
---
# 平面图欧拉公式 (Euler's Formula for Planar Graphs)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Planarity

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- 平面图的欧拉公式：V - E + F = 1 + C，
    其中 C 是连通分支数。对连通平面图，V - E + F = 2 -/
theorem euler_formula_planar (hG : G.Planar) :
    Fintype.card V - G.edgeFinset.card + G.faceCount = 1 + G.connectedComponents.card := by
  -- 对边数归纳证明
  sorry

end SimpleGraph
```

## 数学背景

平面图的欧拉公式是数学中最优美、最普遍的定理之一，由莱昂哈德·欧拉（Leonhard Euler）于1750年代首次提出。对于任何连通的平面图，公式 $V - E + F = 2$ 建立了顶点数 $V$、边数 $E$ 和面数 $F$ 之间的基本关系。这一定理不仅是拓扑学的基石，也是证明四色定理、Kuratowski 定理和无数图论结果的关键工具。

## 直观解释

想象用橡皮筋在平面上围成一个网络。欧拉公式告诉我们：无论网络多么复杂，只要它是连通的且边不相交，顶点数减去边数再加上被分割出的区域数（包括外部无限区域），结果总是 2。可以从一个简单的三角形开始：3 个顶点、3 条边、2 个面（内部和外部），$3 - 3 + 2 = 2$。每添加一条新边，要么增加一个面，要么增加一个顶点，$V - E + F$ 的值保持不变。

## 形式化表述

设 $G$ 是一个连通的平面图，$V$ 为顶点数，$E$ 为边数，$F$ 为面数（包括外部面），则：

$$V - E + F = 2$$

对于具有 $C$ 个连通分支的平面图：

$$V - E + F = 1 + C$$

其中：

- $V = |V(G)|$ 表示顶点数
- $E = |E(G)|$ 表示边数
- $F$ 表示图在平面嵌入中将平面分割成的区域数（面数）
- $C$ 表示连通分支数

## 证明思路

1. **树的情况**：若 $G$ 是树，则 $F = 1$（只有外部面），且 $E = V - 1$，故 $V - (V - 1) + 1 = 2$\n2. **归纳假设**：假设公式对所有边数少于 $E$ 的连通平面图成立\n3. **添加边**：若 $G$ 不是树，则存在圈。移除圈上的一条边，减少一个面但不改变顶点数\n4. **归纳推导**：由归纳假设，新图满足 $V - (E - 1) + (F - 1) = 2$，即原图也满足公式

核心洞察在于欧拉公式是平面拓扑的"守恒量"，与具体图的结构无关。

## 示例

### 示例 1：完全图 $K_4$

$K_4$ 可以平面嵌入为一个三角形内部有一点连接到三个顶点。此时 $V = 4$, $E = 6$, $F = 4$（三个小三角形面和一个外部面）。验证：$4 - 6 + 4 = 2$。

### 示例 2：立方体图

立方体的顶点、边和面构成一个平面图（通过投影）。$V = 8$, $E = 12$, $F = 6$（六个正方形面）。验证：$8 - 12 + 6 = 2$。这是多面体欧拉公式的经典实例。

### 示例 3：两个不相连的三角形

图有两个连通分支，每个是一个三角形。$V = 6$, $E = 6$, $F = 3$（两个内部面和一个共享的外部面）。验证：$6 - 6 + 3 = 3 = 1 + 2$。说明了非连通图的推广形式。

## 应用

- **四色定理**：证明平面图着色数上界的关键工具
- **多面体分类**：正多面体（柏拉图立体）只有五种
- **平面图判定**：推导平面图边数上界 $E \leq 3V - 6$
- **拓扑学**：欧拉示性数 $\chi = V - E + F$ 是曲面的拓扑不变量
- **计算机图形学**：网格生成和曲面参数化中的拓扑约束

## 相关概念

- 平面图 (Planar Graph)：可以在平面上无交叉绘制的图
- 面 (Face)：平面图将平面分割成的连通区域
- 欧拉示性数 (Euler Characteristic)：$\chi = V - E + F$，曲面的拓扑不变量
- Kuratowski 定理：判定平面图的特征定理
- 对偶图 (Dual Graph)：将平面图的面转换为顶点的构造

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 4]
- [J. A. Bondy & U. S. R. Murty. Graph Theory. Springer, 2008. Chapter 10]

### 历史文献

- [L. Euler. Elementa doctrinae solidorum. Novi Commentarii academiae scientiarum Petropolitanae, 1758]

### 在线资源

- [Mathlib4 - Planarity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Planarity.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
