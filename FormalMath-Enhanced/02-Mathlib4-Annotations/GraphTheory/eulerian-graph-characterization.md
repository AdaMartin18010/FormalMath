---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 欧拉图的判定 (Eulerian Graph Characterization)
---
# 欧拉图的判定 (Eulerian Graph Characterization)

## Mathlib4 引用

```lean
import Mathlib.Combinatorics.SimpleGraph.Trails

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- 连通图 G 是欧拉图当且仅当每个顶点的度都是偶数 -/
theorem eulerian_iff_all_deg_even (hG : G.Connected) :
    G.IsEulerian ↔ ∀ v : V, Even (G.degree v) := by
  -- 证明基于构造性方法，利用 Hierholzer 算法的思想
  sorry

/-- 连通图 G 存在欧拉迹当且仅当恰好有两个奇度顶点 -/
theorem eulerian_trail_iff_two_odd (hG : G.Connected) :
    (∃ p : G.Walk, p.IsEulerianTrail) ↔
    {v : V | Odd (G.degree v)}.ncard = 2 := by
  -- 两个奇度顶点即为欧拉迹的端点
  sorry

end SimpleGraph
```

## 数学背景

欧拉图理论起源于18世纪著名的哥尼斯堡七桥问题，由莱昂哈德·欧拉（Leonhard Euler）于1736年解决，这也被公认为图论诞生的标志。欧拉证明了一个图存在经过每条边恰好一次的闭合路径的充分必要条件：图是连通的且每个顶点的度都是偶数。对于存在经过每条边恰好一次的开放路径的情况，条件变为图是连通的且恰好有两个奇度顶点。

## 直观解释

想象一个公园的游览路线，游客希望走过每一座桥恰好一次并最终回到起点。欧拉定理告诉我们：只有当从每座桥出发和返回的次数是偶数时（即每个区域的桥数是偶数），这才可能实现。如果某个区域连接了奇数座桥，那么游客要么从那里开始，要么在那里结束——不可能既从那里进入又从那里离开。如果有两个区域连接了奇数座桥，那么可以将一个作为起点、另一个作为终点。

## 形式化表述

设 $G$ 是一个连通图：

1. $G$ 是**欧拉图**（存在欧拉回路）当且仅当每个顶点的度都是偶数：
   $$\forall v \in V(G), \quad \deg(v) \equiv 0 \pmod{2}$$

2. $G$ 存在**欧拉迹**（不闭合）当且仅当恰好有两个顶点的度是奇数：
   $$|\{v \in V(G) : \deg(v) \equiv 1 \pmod{2}\}| = 2$$

其中：

- $\deg(v)$ 表示顶点 $v$ 的度
- 欧拉回路是指经过每条边恰好一次并回到起点的闭合路径
- 欧拉迹是指经过每条边恰好一次的开放路径

## 证明思路

1. **必要性**：在欧拉回路中，每次进入一个顶点必然伴随着一次离开，因此所有顶点的度必须是偶数\n2. **充分性构造**：从任意顶点出发，沿着未走过的边前进。由于所有度为偶数，这个过程只能在一个已经访问过的顶点结束，形成一个圈\n3. **圈的合并**：若还有未走过的边，由于连通性，必存在某个已访问顶点还有未走边，从该点继续构造新圈并合并\n4. **Hierholzer 算法**：上述构造过程可以系统化实现，是寻找欧拉回路的经典算法

核心洞察在于偶度条件保证了"有进必有出"的局部对称性。

## 示例

### 示例 1：正方形加对角线

考虑一个正方形的四个顶点，加上两条对角线。每个顶点的度为 3（连接两条边和一条对角线），是奇数。因此该图不存在欧拉回路，但存在欧拉迹（从任意顶点开始，到对角顶点结束）。

### 示例 2：完全图 $K_5$

$K_5$ 有 5 个顶点，每个顶点的度为 4（偶数）。根据欧拉定理，$K_5$ 是欧拉图，存在经过每条边恰好一次的回路。

### 示例 3：哥尼斯堡七桥问题

哥尼斯堡的四个陆地区域由七座桥连接，对应的图中四个顶点的度分别为 3, 3, 3, 5，全是奇数。因此既不存在欧拉回路，也不存在欧拉迹，证明了居民不可能走过每座桥恰好一次。

## 应用

- **路径规划**：邮递员问题、街道清扫路线优化
- **电路板检测**：探针遍历电路板所有连接的最优路径
- **DNA 测序**：基因组拼接中读取片段的遍历与组装
- **网络协议**：数据包遍历网络中所有链路的状态检测

## 相关概念

- 欧拉回路 (Eulerian Circuit)：经过每条边恰好一次的闭合路径
- 欧拉迹 (Eulerian Trail)：经过每条边恰好一次的开放路径
- 欧拉图 (Eulerian Graph)：存在欧拉回路的图
- 半欧拉图 (Semi-Eulerian Graph)：存在欧拉迹但不存在欧拉回路的图
- Hierholzer 算法：构造欧拉回路的线性时间算法

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 1]
- [D. B. West. Introduction to Graph Theory. Pearson, 2nd edition, 2001. Section 1.2]

### 历史文献

- [L. Euler. Solutio problematis ad geometriam situs pertinentis. Commentarii academiae scientiarum Petropolitanae, 1736]

### 在线资源

- [Mathlib4 - Trails](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Trails.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
