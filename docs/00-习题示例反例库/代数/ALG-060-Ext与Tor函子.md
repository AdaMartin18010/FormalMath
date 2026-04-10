---
exercise_id: ALG-060
title: Ext与Tor函子的基本计算
difficulty: ⭐⭐⭐⭐
topics: [Ext函子, Tor函子, 导出函子, 投射分解]
created: 2026-04-10
---

## 题目

设 $R$ 是含幺环，$M, N$ 是 $R$-模。

(1) 用**投射分解**定义 $\operatorname{Tor}_n^R(M, N)$ 并计算 $\operatorname{Tor}_n^{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z})$；

(2) 用**内射分解**定义 $\operatorname{Ext}_R^n(M, N)$ 并计算 $\operatorname{Ext}_{\mathbb{Z}}^n(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z})$；

(3) 证明：$M$ 平坦当且仅当 $\operatorname{Tor}_1^R(M, -) = 0$。

## 详细解答

### (1) Tor函子定义与计算

**定义**：取 $M$ 的投射分解 $... \to P_1 \to P_0 \to M \to 0$。

张量积 $-\otimes N$ 得链复形：

$$... \to P_1 \otimes N \to P_0 \otimes N \to 0$$

则 $\operatorname{Tor}_n^R(M, N) = H_n(P_\bullet \otimes N)$。

特别地，$\operatorname{Tor}_0(M, N) = M \otimes N$。

**计算**：$M = \mathbb{Z}/m\mathbb{Z}$。

投射分解：$0 \to \mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \to 0$。

张量积 $-\otimes \mathbb{Z}/n\mathbb{Z}$：

$$0 \to \mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \to 0$$

即：$0 \to \mathbb{Z}/n\mathbb{Z} \xrightarrow{\times m} \mathbb{Z}/n\mathbb{Z} \to 0$。

- $\operatorname{Tor}_0 = \mathbb{Z}/n\mathbb{Z} / m(\mathbb{Z}/n\mathbb{Z}) = \mathbb{Z}/n\mathbb{Z} / m\mathbb{Z}/n\mathbb{Z} = \mathbb{Z}/\gcd(m,n)\mathbb{Z}$
- $\operatorname{Tor}_1 = \ker(\times m) = \{x \in \mathbb{Z}/n\mathbb{Z} : mx \equiv 0 \pmod n\} = (n/\gcd(m,n))\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$
- $\operatorname{Tor}_n = 0$ 对 $n \geq 2$

**结论**：$\operatorname{Tor}_0 \cong \operatorname{Tor}_1 \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$，其余为0。

### (2) Ext函子定义与计算

**定义**：取 $M$ 的投射分解 $P_\bullet \to M \to 0$。

应用 $\operatorname{Hom}(-, N)$ 得余链复形：

$$0 \to \operatorname{Hom}(P_0, N) \to \operatorname{Hom}(P_1, N) \to ...$$

则 $\operatorname{Ext}_R^n(M, N) = H^n(\operatorname{Hom}(P_\bullet, N))$。

或用内射分解：取 $N$ 的内射分解 $0 \to N \to I^\bullet$，应用 $\operatorname{Hom}(M, -)$。

**计算**：$M = \mathbb{Z}/m\mathbb{Z}$，$N = \mathbb{Z}$。

用投射分解：$0 \to \mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \to 0$。

应用 $\operatorname{Hom}(-, \mathbb{Z})$：

$$0 \to \operatorname{Hom}(\mathbb{Z}, \mathbb{Z}) \xrightarrow{(-\circ m)} \operatorname{Hom}(\mathbb{Z}, \mathbb{Z}) \to 0$$

即：$0 \to \mathbb{Z} \xrightarrow{\times m} \mathbb{Z} \to 0$。

- $\operatorname{Ext}^0 = \ker(\times m) = 0$（$m \neq 0$）
- $\operatorname{Ext}^1 = \mathbb{Z}/m\mathbb{Z}$
- $\operatorname{Ext}^n = 0$ 对 $n \geq 2$

### (3) 平坦性判据

**定理**：$M$ 平坦 $\Leftrightarrow$ $\operatorname{Tor}_1^R(M, N) = 0$ 对所有 $N$。

**证明**：

$(\Rightarrow)$ $M$ 平坦 $\Rightarrow$ $M \otimes -$ 正合。

对任意短正合列 $0 \to A \to B \to C \to 0$，$0 \to M \otimes A \to M \otimes B \to M \otimes C \to 0$ 正合。

由长正合列，$\operatorname{Tor}_1(M, C) \to M \otimes A \to M \otimes B$ 正合。

因中间映射单，$\operatorname{Tor}_1(M, C) \to M \otimes A$ 的像为0。

由正合性，$\operatorname{Tor}_1(M, C) = 0$。

$(\Leftarrow)$ 设 $\operatorname{Tor}_1(M, -) = 0$。

对任意短正合列 $0 \to A \to B \to C \to 0$，Tor长正合列给出：

$$0 = \operatorname{Tor}_1(M, C) \to M \otimes A \to M \otimes B \to M \otimes C \to 0$$

故 $M \otimes A \to M \otimes B$ 单，$M$ 平坦。

## 证明技巧

1. **具体分解**：用短正合列作为投射分解
2. **函子计算**：仔细追踪诱导映射
3. **长正合列应用**：Tor/Ext的长正合列是核心工具

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 左右混淆 | Tor从右张量还是从左 | Tor(M,N)可用任一模的投射分解 |
| Ext变体 | 混淆Ext^n(M,N)中哪边取分解 | 两边都行，结果同构 |
| 平坦判据 | 只验证 $\operatorname{Tor}_1(M,R)=0$ | 需要对所有模验证 |

## 变式练习

**变式1（难度⭐⭐⭐）**：计算 $\operatorname{Tor}_1^{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z}/n\mathbb{Z})$。

**变式2（难度⭐⭐⭐⭐）**：证明 $\operatorname{Ext}^1_R(M,N)$ 分类 $M$ 被 $N$ 的扩张。

**变式3（难度⭐⭐⭐⭐）**：用Ext刻划投射模和内射模。
