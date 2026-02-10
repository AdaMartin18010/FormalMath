# 导出函子与 Ext 计算（Z-模） - 工作示例

**类型**: 计算示例
**领域**: 同调代数 / 导出函子
**难度**: L1
**前置知识**: 模、正合列、Hom、投射模/内射模（可选）
**创建日期**: 2026年2月10日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 用投射消解计算 Ext^1_Z(Z/nZ, Z) |
| **领域** | 同调代数 / 导出函子 |
| **MSC** | 18G10（导出函子）、18G20（Hom、Ext） |
| **相关概念** | [29-上同调与同调代数](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/29-上同调与同调代数.md)、[19-上同调与Ext函子](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/19-上同调与Ext函子.md)、[06-导出版上同调](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/06-导出版上同调.md) |

---

## 题目

**问题**：设 \(n \geq 2\) 为整数。求 \(\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z})\)。

本题展示从“右正合函子 \(\operatorname{Hom}_{\mathbb{Z}}(-,\mathbb{Z})\)”到“导出函子 \(\operatorname{Ext}^1\)”的一次完整计算。

---

## 完整解答（工作示例）

**步骤 1**：回忆定义。

- \(\operatorname{Ext}^i_A(M,N) = R^i \operatorname{Hom}_A(M,-)(N)\)（对 N 用内射消解），或等价地 \(R^i \operatorname{Hom}_A(-,N)(M)\)（对 M 用投射消解）。
- 这里用对第一个变量 M 的投射消解：\(\operatorname{Ext}^i_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}) = H^i(\operatorname{Hom}_{\mathbb{Z}}(P^\bullet, \mathbb{Z}))\)，其中 \(P^\bullet \to \mathbb{Z}/n\mathbb{Z} \to 0\) 为 \(\mathbb{Z}/n\mathbb{Z}\) 的投射消解。

**步骤 2**：取 \(\mathbb{Z}/n\mathbb{Z}\) 的投射消解。

- 正合列：\(0 \to \mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z} \xrightarrow{\pi} \mathbb{Z}/n\mathbb{Z} \to 0\)，其中 \(\pi\) 为商同态，\(\cdot n\) 为乘以 n。
- 取 \(P^0 = \mathbb{Z}\)，\(P^1 = \mathbb{Z}\)，\(d^0: P^1 \to P^0\) 为 \(\cdot n\)；则 \(P^\bullet: \cdots \to 0 \to \mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z} \to 0 \to \cdots\)（\(P^0\) 在 0 次，\(P^1\) 在 1 次）给出 \(\mathbb{Z}/n\mathbb{Z}\) 的投射消解（\(\operatorname{coker}(d^0) = \mathbb{Z}/n\mathbb{Z}\)）。

**步骤 3**：应用 \(\operatorname{Hom}_{\mathbb{Z}}(-, \mathbb{Z})\)。

- \(\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Z}, \mathbb{Z}) \cong \mathbb{Z}\)（同态由 \(1 \mapsto k\) 给出）。
- \(d^0 = \cdot n\) 诱导 \(\operatorname{Hom}(d^0, \mathbb{Z}): \operatorname{Hom}(P^0, \mathbb{Z}) \to \operatorname{Hom}(P^1, \mathbb{Z})\)，即 \(\operatorname{Hom}(\mathbb{Z}, \mathbb{Z}) \to \operatorname{Hom}(\mathbb{Z}, \mathbb{Z})\)：\(\varphi \mapsto \varphi \circ (\cdot n)\)。在生成元 1 上，\(1 \mapsto n\)，故该映射为 \(\mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z}\)。
- 复形 \(\operatorname{Hom}(P^\bullet, \mathbb{Z})\) 为：\(0 \to \mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z} \to 0 \to \cdots\)（\(\mathbb{Z}\) 在 0、1 次）。

**步骤 4**：取上同调。

- \(H^0 = \ker(\cdot n) / \operatorname{im}(0) = \ker(\cdot n) = 0\)（因 \(n \geq 2\)，\(\mathbb{Z}\) 中无 n  torsion）。
- \(H^1 = \ker(0) / \operatorname{im}(\cdot n) = \mathbb{Z} / n\mathbb{Z}\)。
- 故 \(\operatorname{Ext}^0_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}) = 0\)，\(\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}) = \mathbb{Z}/n\mathbb{Z}\)。

**步骤 5**：小结。

\[
\operatorname{Ext}^1_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}) = \mathbb{Z}/n\mathbb{Z}.
\]

（\(\operatorname{Ext}^0 = \operatorname{Hom}\)，\(\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}) = 0\)，与上面一致。）

---

## 关键步骤说明

- **思路**：对第一个变元取投射消解（\(0 \to \mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z} \to \mathbb{Z}/n\mathbb{Z} \to 0\)），再应用 \(\operatorname{Hom}(-, \mathbb{Z})\) 得上同调即 Ext。
- **技巧**：\(\mathbb{Z}\) 是自由模故投射；\(\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Z}, \mathbb{Z}) \cong \mathbb{Z}\)；\(\operatorname{Hom}((\cdot n), \operatorname{id})\) 对应乘法 n。
- **易错点**：消解的方向与 \(\operatorname{Hom}\) 的变元（对第一变元消解得 \(\operatorname{Hom}(P^\bullet, N)\)）；微分方向导致 \(H^1 = \mathbb{Z}/n\mathbb{Z}\)。

---

## 相关概念链接

- [29-上同调与同调代数](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/29-上同调与同调代数.md)
- [19-上同调与Ext函子](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/19-上同调与Ext函子.md)
- [06-导出版上同调](../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/06-导出版上同调.md)
