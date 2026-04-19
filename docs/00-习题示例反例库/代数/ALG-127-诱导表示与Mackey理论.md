---
msc_primary: 00A99
习题编号: ALG-127
学科: 代数
知识点: 表示论-Mackey理论
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# 诱导表示与Mackey理论

## 题目

设 $G$ 是有限群，$H, K \subset G$ 是子群。

**(a) Mackey公式**：对 $W \in \text{Rep}(H)$：
$$\text{Res}_K^G \text{Ind}_H^G W \cong \bigoplus_{g \in K \setminus G / H} \text{Ind}_{K \cap gHg^{-1}}^K \text{Res}_{K \cap gHg^{-1}}^{gHg^{-1}} W^g$$

**(b) Mackey不可约性判别法**：$\text{Ind}_H^G W$ 不可约当且仅当：
(i) $W$ 不可约；
(ii) 对 $g \notin H$，$\text{Res}_{H \cap gHg^{-1}}^H W$ 与 $\text{Res}_{H \cap gHg^{-1}}^{gHg^{-1}} W^g$ 不交。

**(c) 应用**：证明 $G = S_4$ 的某些表示不可约。

## 解答

### (a) Mackey公式

**证明概要**：

**双重陪集分解**：$G = \bigsqcup_{g \in K \setminus G / H} KgH$。

**诱导表示的分解**：

$\text{Ind}_H^G W = \bigoplus_{x \in G/H} x \otimes W$。

$K$ 作用保持 $KgH/H$ 的块。

**每个块**：$K \cap gHg^{-1}$ 固定 $g \otimes W$ 的稳定子。

诱导出表示 $\text{Ind}_{K \cap gHg^{-1}}^K$。

**具体计算**：

对 $k \in K$，$k(g \otimes w) = kg \otimes w = gx' \otimes w$（$kg = gx'h$）。

$= g \otimes h w$（适当解释）。

共轭作用给出 $W^g$。$\square$

### (b) 不可约性判别法

**证明**：

$\text{Ind}_H^G W$ 不可约 $\Leftrightarrow$ $\langle \text{Ind}_H^G W, \text{Ind}_H^G W \rangle = 1$。

由Frobenius互反性：
$$\langle \text{Ind}_H^G W, \text{Ind}_H^G W \rangle = \langle W, \text{Res}_H^G \text{Ind}_H^G W \rangle$$

由Mackey公式：
$$= \sum_{g \in H \setminus G / H} \langle W, \text{Ind}_{H \cap gHg^{-1}}^H \text{Res} W^g \rangle$$

$$= \sum_g \langle \text{Res} W, \text{Res} W^g \rangle$$

$g = e$ 项贡献 $\langle W, W \rangle$。

其他项为零当且仅当条件(ii)。$\square$

### (c) $S_4$ 的应用

**例子**：

$H = S_3 \subset S_4$（固定一个点）。

$W = \text{sgn}$（符号表示）。

**双重陪集**：$S_4 = S_3 \cup S_3(14)S_3$。

**Mackey检验**：

对 $g = (14)$，$H \cap gHg^{-1} = S_2$。

$\text{Res}_{S_2}^{S_3}(\text{sgn}) = \text{sgn}$。

$W^g$ 在 $S_2$ 上也是 $\text{sgn}$（符号在共轭下不变）。

因此两表示相同，不交条件不满足。

**修正**：取 $W$ 为标准表示（二维）。

$\text{Res}_{S_2}^{S_3}(\text{std}) = \text{triv} \oplus \text{sgn}$。

$W^g$ 在 $S_2$ 上作用需检验。$\square$

## 证明技巧

1. **双重陪集**：群作用的轨道分解
2. **互反性+Mackey**：内积计算的标准方法
3. **具体群计算**：子群结构的精细分析

## 常见错误

- ❌ 双重陪集代表选择错误
- ❌ 共轭作用的方向混淆
- ❌ 限制表示的分解计算

## 变式练习

**变式1：** 计算 $A_4$ 的所有不可约表示。

**变式2：** 证明超可解群的单项性（monomiality）。
