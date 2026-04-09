---
msc_primary: 18N60
msc_secondary: [18D05, 55U35]
title: nLab - ∞-范畴 (∞-category) 中文解读
nlab_url: https://ncatlab.org/nlab/show/infinity-category
processed_at: '2026-04-09'
---

# nLab - ∞-范畴 (∞-category) 中文解读

**原文链接**: https://ncatlab.org/nlab/show/infinity-category
**最后修订**: 2025年10月14日（第38版）
**nLab讨论区**: https://nforum.ncatlab.org/discussion/4625/
**解读版本**: v0.1（框架版）

---

## 一、核心概念

### 1.1 什么是∞-范畴？

**直观理解**:

∞-范畴是**范畴论的高阶推广**，其中：

- **普通范畴**: 有对象（0-态射）和态射（1-态射），态射之间只有相等或不相等
- **2-范畴**: 对象、1-态射、2-态射（态射之间的"态射"）
- **∞-范畴**: 有任意高阶的态射（n-态射 for all n ≥ 0），且高阶态射可逆（在适当意义下）

**关键特征**:

| 特征 | 说明 | 对比普通范畴 |
|------|------|--------------|
| 高阶态射 | 存在n-态射 for all n | 只有对象和1-态射 |
| 弱可逆性 | 高阶态射是可逆的（同伦意义） | 态射未必可逆 |
| 弱复合 | 复合满足结合律仅到同伦 | 严格结合律 |
| 组合数据 | 需要无穷多的 coherence 数据 | 有限数据 |

### 1.2 多种模型

∞-范畴有不同的数学实现方式（模型）：

```
∞-范畴 (概念)
│
├─ 拟范畴 (Quasi-categories) [Joyal, Lurie]
│   └─ 弱Kan复形：内Horn可填
│
├─ 拓扑范畴 (Topologically enriched categories)
│   └─ 态射空间为拓扑空间
│
├─ 单纯范畴 (Simplicial categories)
│   └─ 态射空间为单纯集
│
├─ Segal范畴
│   └─ Segal条件的弱化
│
└─ 完备Segal空间 [Rezk]
    └─ 单纯空间满足Segal条件和完备性
```

**模型范畴等价**: 上述模型在适当的意义下相互等价（Quillen等价）。

---

## 二、形式化定义（拟范畴模型）

### 2.1 预备知识

**单纯集 (Simplicial Set)**:

单纯集是函子 $X: \Delta^{\text{op}} \to \text{Set}$，其中 $\Delta$ 是有限序数范畴。

**Horn**:

对于 $n \geq 1$ 和 $0 \leq k \leq n$，$\Lambda^n_k \subset \Delta^n$ 是移除第 $k$ 个面和内部后的子复形。

### 2.2 拟范畴定义

**定义** ([Joyal](https://ncatlab.org/nlab/show/Andr%C3%A9+Joyal), [Lurie](https://ncatlab.org/nlab/show/Jacob+Lurie)):

单纯集 $X$ 称为**拟范畴**（或∞-范畴），如果对任意 $n \geq 2$ 和 $0 < k < n$，任意映射 $\Lambda^n_k \to X$ 都可延拓为 $\Delta^n \to X$。

```
Λ^n_k ───→ X
│         ↗
↓        /  (存在延拓)
Δ^n ────╯
```

**直观解释**:

- **内Horn可填** ($0 < k < n$) 意味着"高维态射的合成存在"
- 与外Horn的区别反映了∞-范畴中"高阶态射可逆"的特性

### 2.3 与普通范畴的关系

**定理**: 拟范畴 $X$ 是（普通）范畴的神经当且仅当每个内Horn有**唯一**填充。

这说明：

- 普通范畴 = 严格结合的∞-范畴
- ∞-范畴 = 弱结合的范畴

---

## 三、∞-范畴的基本概念

### 3.1 对象与态射

在拟范畴 $C$ 中：

| 概念 | 定义 | 直观 |
|------|------|------|
| **对象** | $C$ 的0-单形 | 点 |
| **1-态射** | $C$ 的1-单形 | 箭头 $f: x \to y$ |
| **2-态射** | 连接两个1-单形的2-单形 | 同伦/2-胞腔 |
| **n-态射** | n-单形 | 高阶同伦 |

### 3.2 同伦与等价

**同伦**:

两个1-态射 $f, g: x \to y$ **同伦**，如果存在2-单形连接它们。

**等价 (Equivalence)**:

1-态射 $f: x \to y$ 是**等价**，如果存在 $g: y \to x$ 使得 $g \circ f$ 同伦于 $\text{id}_x$，$f \circ g$ 同伦于 $\text{id}_y$。

**关键区别**: 在∞-范畴中，我们关心的是"同伦类"而非"严格相等"。

### 3.3 极限与余极限

**∞-极限** ([Lurie, HTT](https://ncatlab.org/nlab/show/Higher+Topos+Theory)):

与普通范畴的极限不同，∞-极限满足**泛性质到同伦唯一**（homotopy-unique）。

**例子**:

- 推出 (pushout) 在同伦论中对应同伦推出
- 纤维积在同伦论中对应同伦纤维积

---

## 四、与FormalMath的关联

### 4.1 当前覆盖情况

**相关文档**:

- `docs/02-代数结构/02-核心理论/范畴论/06-范畴论-深度扩展版.md`
- `docs/02-代数结构/02-核心理论/范畴论/07-高阶范畴论.md` (如有)

**现状评估**:

- ⏳ ∞-范畴概念尚未系统覆盖
- ⏳ 同伦类型论相关内容待补充
- ⏳ 与代数拓扑的联系待建立

### 4.2 建议补充内容

| 主题 | 优先级 | 关联分支 |
|------|--------|----------|
| ∞-范畴基础 | P1 | 范畴论、代数拓扑 |
| 同伦类型论 | P1 | 数理逻辑、形式化证明 |
| (∞,1)-Topos | P2 | 代数几何、Topos理论 |
| 导出代数几何 | P2 | 代数几何 |

### 4.3 与Stacks Project的关联

Stacks Project在以下章节涉及∞-范畴相关内容：

- **导出范畴 (Chapter 13)**: 可以视为(∞,1)-范畴的截断
- **代数拓扑**: 同伦论基础

**深化建议**: 在`docs/15-同调代数/导出范畴-深度扩展版.md`中添加∞-范畴视角的解读。

---

## 五、学习路径

### 5.1 前置知识

```
1. 普通范畴论
   └─ 函子、自然变换、极限

2. 同伦论基础
   └─ 同伦、同伦等价、同伦群

3. 单纯集
   └─ 单纯对象、几何实现

4. ∞-范畴
   └─ 拟范畴、模型结构
```

### 5.2 推荐教材

| 资源 | 作者 | 难度 | 备注 |
|------|------|------|------|
| Higher Topos Theory | Jacob Lurie | ⭐⭐⭐⭐⭐ | 权威参考书 |
| Higher Algebra | Jacob Lurie | ⭐⭐⭐⭐⭐ | 代数方向 |
| Kerodon | Jacob Lurie | ⭐⭐⭐⭐⭐ | 在线教材 |
| ∞-Category Theory | Cisinski | ⭐⭐⭐⭐ | 较新的处理方法 |
| 同伦类型论讲义 | 多作者 | ⭐⭐⭐⭐ | 逻辑视角 |

### 5.3 nLab相关条目

- [quasi-category](https://ncatlab.org/nlab/show/quasi-category)
- [higher category theory](https://ncatlab.org/nlab/show/higher+category+theory)
- [homotopy type theory](https://ncatlab.org/nlab/show/homotopy+type+theory)
- [derived algebraic geometry](https://ncatlab.org/nlab/show/derived+algebraic+geometry)

---

## 六、前沿应用

### 6.1 导出代数几何 (DAG)

**核心思想**: 用∞-范畴代替普通范畴进行代数几何。

**代表人物**: [Jacob Lurie](https://ncatlab.org/nlab/show/Jacob+Lurie), [Bertrand Toën](https://ncatlab.org/nlab/show/Bertrand+To%C3%ABn)

**应用**:

- 相交理论的完善
- 模空间理论的严格化
- 形变理论的推广

### 6.2 拓扑量子场论 (TQFT)

**核心思想**: 用∞-范畴描述高维协变 functorial field theory。

**相关**: [cobordism hypothesis](https://ncatlab.org/nlab/show/cobordism+hypothesis) (Baez-Dolan, Lurie)

### 6.3 形式化数学

**同伦类型论 (HoTT)**:

将∞-群胚（特殊的∞-范畴）作为类型的语义，实现数学的形式化。

**工具**: [Lean4](https://leanprover.github.io/) (有HoTT库), [Cubical Agda](https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html)

---

## 七、深化行动项

### 立即行动（Round 35-36）

- [ ] 在FormalMath创建∞-范畴概念条目
- [ ] 链接nLab和Lurie的HTT
- [ ] 建立与导出范畴的联系

### 中期计划（Round 37-40）

- [ ] 建设(∞,1)-范畴基础文档
- [ ] 添加同伦类型论入门
- [ ] 与代数几何现代发展模块对接

### 长期目标（Round 41+）

- [ ] 完成∞-范畴体系的初步建设
- [ ] 与Kerodon建立内容对应
- [ ] 探索Lean4形式化实现

---

**解读人**: AI Assistant
**审核状态**: 待高阶范畴论专家审核
**最后更新**: 2026年4月9日
**下次更新**: 随nLab更新
