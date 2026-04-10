---
msc_primary: 13F15
exercise_id: CEX-ALG-006
title: 非主理想整环的例子
difficulty: 3
type: CST
topic: 代数学
subtopic: 环论
source:
  original: true
processed_at: '2026-04-10'
---

# CEX-ALG-006: 非主理想整环的例子

**反例编号**: CEX-ALG-006  
**难度**: ⭐⭐⭐ (Level 3)  
**类型**: 构造型 (CST)  
**主题**: 理想理论

---

## 反例构造

**环**: $\mathbb{Z}[x]$（整数系数多项式环）

**理想**: $I = (2, x)$（由2和$x$生成的理想）

### 验证 $I$ 不是主理想

**假设**: $I = (f(x))$ 对某个 $f(x) \in \mathbb{Z}[x]$

**推导**:
1. 由于 $2 \in I$，有 $f(x) \mid 2$
2. 由于 $x \in I$，有 $f(x) \mid x$

**分析**:
- $f(x) \mid 2$ 意味着 $f(x) = \pm 1$ 或 $\pm 2$
- $f(x) \mid x$ 意味着 $f(x) = \pm 1$ 或 $\pm x$

**同时满足**: $f(x) = \pm 1$

**矛盾**: 
- 若 $I = (1) = \mathbb{Z}[x]$，则 $1 \in I$
- 但 $I = \{2p(x) + xq(x) : p, q \in \mathbb{Z}[x]\}$ 中，常数项必为偶数
- 所以 $1 \notin I$

**结论**: $I$ 不是主理想，故 $\mathbb{Z}[x]$ 不是主理想整环。

---

## 更简单的反例

**环**: $\mathbb{Z}[\sqrt{-5}]$

**理想**: $I = (2, 1 + \sqrt{-5})$

同样可以证明 $I$ 不是主理想。

---

## 相关定理

### 主理想整环的性质

> 在PID中，每个理想都是主理想。

**例子**:
- $\mathbb{Z}$ 是PID
- $\mathbb{Q}[x]$ 是PID
- $\mathbb{Z}[x]$ **不是** PID

### Hilbert基定理

> 若 $R$ 是Noetherian环，则 $R[x]$ 也是Noetherian环。

**应用**: $\mathbb{Z}[x]$ 是Noetherian环，但不是PID。

---

## 教学要点

| 概念 | 包含关系 |
|------|----------|
| PID $\subset$ UFD | 是 |
| UFD $\subset$ PID | 否（本反例） |
| $\mathbb{Z}[x]$ | UFD但不是PID |

---

**反例设计**: AI Assistant  
**最后更新**: 2026年4月10日
