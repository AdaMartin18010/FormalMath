---
msc_primary: 18G15
msc_secondary:
- 13D07
title: Ext与Tor函子计算 - 工作示例
processed_at: '2026-04-08'
---
# Ext与Tor函子计算 - 工作示例

**类型**: 计算示例
**领域**: 同调代数
**难度**: L3
**前置知识**: 同调代数、投射分解、内射分解
**创建日期**: 2026年4月8日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | Ext和Tor函子的基本计算 |
| **领域** | 同调代数 / 导出函子 |
| **MSC** | 18G15（Ext和Tor） |
| **相关概念** | 导出函子、Ext、Tor、投射分解 |

---

## 题目

设 $R = \mathbb{Z}$，计算：

1. $\text{Tor}_1^{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z})$
2. $\text{Ext}_{\mathbb{Z}}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z})$

---

## 完整解答（工作示例）

### 基本定义

- **Tor**：左导出函子，$\text{Tor}_i^R(M, N) = L_i(M \otimes_R -)(N)$
- **Ext**：右导出函子，$\text{Ext}_R^i(M, N) = R^i\text{Hom}_R(M, -)(N)$

---

**解答 1**：$\text{Tor}_1^{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z})$

**步骤 1**：为 $\mathbb{Z}/m\mathbb{Z}$ 构造投射分解

$$0 \to \mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \to 0$$

这是短正合列，也是投射分解（$\mathbb{Z}$ 是自由模，故投射）。

**步骤 2**：与 $\mathbb{Z}/n\mathbb{Z}$ 做张量积

$$0 \to \mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \to 0$$

即：
$$0 \to \mathbb{Z}/n\mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \otimes \mathbb{Z}/n\mathbb{Z} \to 0$$

**步骤 3**：计算 Tor

$$\text{Tor}_1^{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) = \ker(\mathbb{Z}/n\mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z}/n\mathbb{Z})$$

$$= \{\bar{a} \in \mathbb{Z}/n\mathbb{Z} : ma \equiv 0 \pmod{n}\}$$

$$= \{\bar{a} : n \mid ma\} = \frac{n}{\gcd(m,n)}\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$$

**结论**：
$$\text{Tor}_1^{\mathbb{Z}}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$$

---

**解答 2**：$\text{Ext}_{\mathbb{Z}}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z})$

**步骤 1**：用同样的投射分解

$$0 \to \mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z} \to \mathbb{Z}/m\mathbb{Z} \to 0$$

**步骤 2**：应用 $\text{Hom}(-, \mathbb{Z})$

$$0 \to \text{Hom}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) \to \text{Hom}(\mathbb{Z}, \mathbb{Z}) \xrightarrow{\cdot m} \text{Hom}(\mathbb{Z}, \mathbb{Z}) \to \text{Ext}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) \to 0$$

**步骤 3**：计算各项

- $\text{Hom}(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) = 0$（$\mathbb{Z}$ 无挠）
- $\text{Hom}(\mathbb{Z}, \mathbb{Z}) \cong \mathbb{Z}$

序列变为：
$$0 \to 0 \to \mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z} \to \text{Ext}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) \to 0$$

**步骤 4**：计算 Ext

$$\text{Ext}_{\mathbb{Z}}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) = \text{coker}(\mathbb{Z} \xrightarrow{\cdot m} \mathbb{Z}) = \mathbb{Z}/m\mathbb{Z}$$

**结论**：
$$\text{Ext}_{\mathbb{Z}}^1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}) \cong \mathbb{Z}/m\mathbb{Z}$$

---

## 关键步骤说明

- **投射分解**：用投射模逼近给定模
- **张量积**：Tor 通过张量积的左导出函子定义
- **Hom函子**：Ext 通过 Hom 的右导出函子定义
- **长正合列**：导出函子产生长正合列

---

## 相关概念链接

- [正合列](../../../concept/核心概念/23-正合列.md)
- [同调代数](../../../docs/10-同调代数/01-同调代数基础/01-同调代数.md)
