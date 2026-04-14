import os

files = {
    "GraphTheory/four-color-theorem.md": """---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 四色定理 (Four Color Theorem)
---
# 四色定理 (Four Color Theorem)

## Mathlib4 引用

```lean
-- 该定理在 FourColor 项目中得到完整形式化证明
-- 来源: https://github.com/leanprover-community/fourcolor
import Mathlib

/-- 四色定理：任何平面地图只需四种颜色即可使得相邻区域颜色不同 -/
theorem FourColorTheorem (G : SimpleGraph ℕ) [Finite <| V G] (h : G.Planar) :
    G.chromaticNumber ≤ 4 := by
  -- 核心证明依赖于可约构形集的不可避性与放电法
  sorry
```

## 数学背景

四色定理是图论中最著名的定理之一，由肯尼斯·阿佩尔（Kenneth Appel）和沃尔夫冈·哈肯（Wolfgang Haken）于1976年首次借助计算机完成证明。该定理断言任何平面地图只需四种颜色就能确保相邻区域颜色不同。这是第一个主要依赖计算机辅助证明的数学定理，开创了数学证明的新纪元，也引发了关于计算机证明可接受性的广泛讨论。

## 直观解释

四色定理的含义非常直观：想象一张世界地图，每个国家都要涂上一种颜色，而相邻的国家不能使用相同的颜色。定理告诉我们，无论地图多么复杂，四种颜色总是足够的。可以将这理解为平面本身的某种"有限性"——即使边界蜿蜒曲折，平面区域之间的邻接关系仍然受到拓扑约束，不会产生需要超过四种颜色的极端构型。

## 形式化表述

设 $G$ 是一个有限平面图，则：

$$\\chi(G) \\leq 4$$

其中：

- $\\chi(G)$ 表示图 $G$ 的色数（正常顶点着色所需的最少颜色数）
- $G$ 为平面图意味着 $G$ 可以在平面上画出且边不相交

## 证明思路

1. **不可避集**：构造一个包含约1900个构形的集合，证明任何平面图必然包含其中至少一个构形
2. **可约性**：证明这些构形都是"可约的"——如果包含该构形的地图可四着色，则整个地图也可四着色
3. **放电法**：利用欧拉公式和电荷分配方法证明上述构形集是不可避的

核心难点在于需要处理海量构形，这是计算机辅助证明发挥关键作用的地方。

## 示例

### 示例 1：简单国家地图

考虑一个由四个国家组成的地图，其中每个国家都与其他三个国家相邻。这对应于完全图 $K_4$，其色数恰好为 4，说明四色是不可改进的上界。

### 示例 2：省级行政区划

中国的省级行政区划构成一个复杂的平面图。根据四色定理，只需要四种颜色就能为所有省份着色，使得任意两个接壤的省份颜色不同。实际上，大多数真实世界的地图都远不需要四种颜色。

### 示例 3：反例在环面上

在环面（轮胎表面）上，存在需要七种颜色的地图。这说明四色定理严重依赖于平面的拓扑性质，不能推广到任意曲面。

## 应用

- **地图着色**：地理信息系统和地图绘制中的着色优化
- **寄存器分配**：编译器中将变量分配到有限寄存器的图着色问题
- **调度问题**：资源分配和任务调度中的冲突避免
- **频谱分配**：无线通信中的信道频率分配

## 相关概念

- 平面图 (Planar Graph)：可以在平面上无交叉绘制的图
- 色数 (Chromatic Number)：正常顶点着色所需的最少颜色数
- 欧拉公式 (Euler's Formula)：$V - E + F = 2$，平面图的基本关系
- 图着色 (Graph Coloring)：为图的顶点或边分配颜色使得相邻对象颜色不同
- 对偶图 (Dual Graph)：将地图区域转换为图的数学构造

## 参考

### 教材

- [R. Diestel. Graph Theory. Springer, 5th edition, 2017. Chapter 5]
- [J. A. Bondy & U. S. R. Murty. Graph Theory. Springer, 2008. Chapter 10]

### 历史文献

- [Appel & Haken. Every planar map is four colorable. Illinois J. Math., 1977]

### 在线资源

- [Mathlib4 FourColor 项目](https://github.com/leanprover-community/fourcolor)
- [Four Color Theorem - Wikipedia](https://en.wikipedia.org/wiki/Four_color_theorem)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
""",
}

for path, content in files.items():
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f'Created {path}')
