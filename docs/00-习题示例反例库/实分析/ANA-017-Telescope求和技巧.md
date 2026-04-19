---
msc_primary: 40

  - 40A05
exercise_id: ANA-017
title: Telescope求和技巧
difficulty: 3
type: CALC
topic: 实分析
subtopic: 极限计算
source:
  course: MIT 18.100A Real Analysis
  chapter: "2.3"
  original: true
processed_at: '2026-04-09'
---

# ANA-017: Telescope求和技巧

**题号**: ANA-017
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 计算型 (CALC)
**来源**: MIT 18.100A Chapter 2.3
**主题**: 裂项相消法求极限

---

## 题目

利用Telescope（裂项相消）方法计算下列极限：

**(a)** 计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \frac{1}{k(k+1)}$

**(b)** 计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \frac{1}{k(k+1)(k+2)}$

**(c)** 计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \frac{k}{(k+1)!}$

---

## 解答

### (a) 基本Telescope

**解**:

**Step 1: 裂项**
$$\frac{1}{k(k+1)} = \frac{1}{k} - \frac{1}{k+1}$$

**Step 2: 求和**
$$\sum_{k=1}^{n} \frac{1}{k(k+1)} = \sum_{k=1}^{n} \left(\frac{1}{k} - \frac{1}{k+1}\right)$$

展开：
$$= \left(1 - \frac{1}{2}\right) + \left(\frac{1}{2} - \frac{1}{3}\right) + \left(\frac{1}{3} - \frac{1}{4}\right) + \cdots + \left(\frac{1}{n} - \frac{1}{n+1}\right)$$

中间项全部抵消：
$$= 1 - \frac{1}{n+1}$$

**Step 3: 求极限**
$$\lim_{n\to\infty} \sum_{k=1}^{n} \frac{1}{k(k+1)} = \lim_{n\to\infty} \left(1 - \frac{1}{n+1}\right) = 1 \quad \square$$

---

### (b) 高阶Telescope

**解**:

**Step 1: 裂项**

设 $\frac{1}{k(k+1)(k+2)} = \frac{A}{k} + \frac{B}{k+1} + \frac{C}{k+2}$

通分后比较分子：
$$1 = A(k+1)(k+2) + Bk(k+2) + Ck(k+1)$$

令 $k = 0$：$1 = 2A \Rightarrow A = \frac{1}{2}$

令 $k = -1$：$1 = -B \Rightarrow B = -1$

令 $k = -2$：$1 = 2C \Rightarrow C = \frac{1}{2}$

所以：
$$\frac{1}{k(k+1)(k+2)} = \frac{1}{2k} - \frac{1}{k+1} + \frac{1}{2(k+2)}$$

**Step 2: 重写为Telescope形式**

$$= \frac{1}{2}\left(\frac{1}{k} - \frac{1}{k+1}\right) - \frac{1}{2}\left(\frac{1}{k+1} - \frac{1}{k+2}\right)$$

**Step 3: 求和**

设 $b_k = \frac{1}{k} - \frac{1}{k+1}$，则原式 $= \frac{1}{2}(b_k - b_{k+1})$。

$$\sum_{k=1}^{n} \frac{1}{k(k+1)(k+2)} = \frac{1}{2}\sum_{k=1}^{n} (b_k - b_{k+1})$$

这是Telescope：
$$= \frac{1}{2}(b_1 - b_{n+1}) = \frac{1}{2}\left(\frac{1}{2} - \frac{1}{n+1} + \frac{1}{n+2}\right)$$

**Step 4: 求极限**
$$\lim_{n\to\infty} = \frac{1}{2} \cdot \frac{1}{2} = \frac{1}{4} \quad \square$$

---

### (c) 含阶乘的Telescope

**解**:

**Step 1: 裂项**

注意到 $\frac{k}{(k+1)!} = \frac{(k+1)-1}{(k+1)!} = \frac{1}{k!} - \frac{1}{(k+1)!}$

**Step 2: 求和**
$$\sum_{k=1}^{n} \frac{k}{(k+1)!} = \sum_{k=1}^{n} \left(\frac{1}{k!} - \frac{1}{(k+1)!}\right)$$

展开：
$$= \left(\frac{1}{1!} - \frac{1}{2!}\right) + \left(\frac{1}{2!} - \frac{1}{3!}\right) + \cdots + \left(\frac{1}{n!} - \frac{1}{(n+1)!}\right)$$

Telescope后：
$$= 1 - \frac{1}{(n+1)!}$$

**Step 3: 求极限**
$$\lim_{n\to\infty} \sum_{k=1}^{n} \frac{k}{(k+1)!} = \lim_{n\to\infty} \left(1 - \frac{1}{(n+1)!}\right) = 1 \quad \square$$

**注**: 这是 $e$ 的级数展开相关的结果。

---

## 证明技巧总结

| 技巧 | 应用位置 | 说明 |
|------|----------|------|
| 部分分式 | (a)(b) | 有理函数的裂项分解 |
| 阶乘裂项 | (c) | $(k+1)! = (k+1) \cdot k!$ 的利用 |
| 差分形式 | 全部 | 将通项写为 $a_k - a_{k+1}$ |
| 部分和简化 | 全部 | 利用抵消简化求和 |

### 关键洞察

1. **Telescope的核心**: 通项可写为差分形式 $f(k) - f(k+1)$
2. **部分分式分解**: 有理函数裂项的标准方法
3. **阶乘的裂项**: $\frac{1}{k!} - \frac{1}{(k+1)!} = \frac{k}{(k+1)!}$

---

## 常见错误

### 错误1: 裂项错误

❌ **错误做法**:
> $\frac{1}{k(k+1)} = \frac{1}{k} + \frac{1}{k+1}$（符号错误）

✅ **正确做法**:
> 验证：$\frac{1}{k} - \frac{1}{k+1} = \frac{k+1-k}{k(k+1)} = \frac{1}{k(k+1)}$ ✓

### 错误2: 遗漏边界项

❌ **错误做法**:
> Telescope后忘记保留首项或末项

✅ **正确做法**:
> 仔细检查：$\sum_{k=1}^{n}(a_k - a_{k+1}) = a_1 - a_{n+1}$

### 错误3: 系数处理不当

❌ **错误做法**:
> 在(b)中，裂项后直接求和而不整理成Telescope形式

✅ **正确做法**:
> 将裂项结果重新组合，形成清晰的Telescope结构

---

## 变式练习

### 变式1（难度⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \frac{1}{k(k+2)}$

**答案**: $\frac{3}{4}$

**提示**: $\frac{1}{k(k+2)} = \frac{1}{2}\left(\frac{1}{k} - \frac{1}{k+2}\right)$

### 变式2（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \arctan\frac{1}{k^2+k+1}$

**答案**: $\frac{\pi}{4}$

**提示**: 利用 $\arctan\frac{1}{k^2+k+1} = \arctan(k+1) - \arctan k$

### 变式3（难度⭐⭐⭐⭐）

计算 $\displaystyle\lim_{n\to\infty} \sum_{k=1}^{n} \frac{2k+1}{k^2(k+1)^2}$

**答案**: $1$

**提示**: $\frac{2k+1}{k^2(k+1)^2} = \frac{1}{k^2} - \frac{1}{(k+1)^2}$

---

## 相关概念

| 概念 | 关系 |
|------|------|
| 部分分式分解 | 有理函数裂项的标准技术 |
| 级数求和 | Telescope是求级数和的重要方法 |
| 差分方法 | 离散微积分的核心工具 |

**标签**: #Telescope求和 #裂项相消 #级数求和 #实分析 #MIT-18.100A
