---
习题编号: ALG-113
学科: 代数
知识点: 交换代数-素谱
难度: ⭐⭐⭐
预计时间: 20分钟
---

# 素谱与Zariski拓扑

## 题目

设 $R$ 是交换环，**素谱** $\text{Spec}(R)$ 是所有素理想的集合。

对 $I \subset R$ 理想，定义 $V(I) = \{\mathfrak{p} \in \text{Spec}(R) : I \subset \mathfrak{p}\}$。

(a) 证明 $\{V(I)\}$ 构成闭集族，定义Zariski拓扑。

(b) 证明 $\text{Spec}(R)$ 是拟紧的（quasi-compact）。

(c) 设 $f: R \to S$ 是环同态，证明诱导映射 $f^*: \text{Spec}(S) \to \text{Spec}(R)$，$f^*(\mathfrak{q}) = f^{-1}(\mathfrak{q})$ 是连续的。

## 解答

### (a) Zariski拓扑

**证明：**

需验证 $\{V(I)\}$ 满足闭集公理。

- **$\emptyset = V(R)$**：$R$ 不包含于任何素理想。

- **$\text{Spec}(R) = V(0)$**：$0$ 包含于所有素理想。

- **$\bigcap_\alpha V(I_\alpha) = V(\sum_\alpha I_\alpha)$**：

$\mathfrak{p} \in \bigcap V(I_\alpha)$ $\Leftrightarrow$ $I_\alpha \subset \mathfrak{p}$ 对所有 $\alpha$

$\Leftrightarrow$ $\sum I_\alpha \subset \mathfrak{p}$ $\Leftrightarrow$ $\mathfrak{p} \in V(\sum I_\alpha)$。

- **$V(I) \cup V(J) = V(I \cap J)$**：

$\supset$：$I \cap J \subset \mathfrak{p}$ 推出 $I \subset \mathfrak{p}$ 或 $J \subset \mathfrak{p}$（素理想性质）。

$\subset$：显然。

因此构成拓扑。$\square$

### (b) 拟紧性

**证明：**

设 $\text{Spec}(R) = \bigcup_\alpha D(f_\alpha)$，其中 $D(f) = \text{Spec}(R) \setminus V(f)$。

等价于 $\bigcap_\alpha V(f_\alpha) = V((f_\alpha)) = \emptyset$。

即 $(f_\alpha) = R$。

因此 $1 = \sum_{i=1}^n a_i f_{\alpha_i}$（有限和）。

$\text{Spec}(R) = \bigcup_{i=1}^n D(f_{\alpha_i})$。

故拟紧。$\square$

### (c) 诱导映射的连续性

**证明：**

需证 $(f^*)^{-1}(V(I))$ 是闭集。

$$(f^*)^{-1}(V(I)) = \{\mathfrak{q} \in \text{Spec}(S) : f^{-1}(\mathfrak{q}) \in V(I)\}$$

$$= \{\mathfrak{q} : I \subset f^{-1}(\mathfrak{q})\} = \{\mathfrak{q} : f(I) \subset \mathfrak{q}\}$$

$$= V(f(I)S)$$

是闭集。$\square$

## 证明技巧

1. **闭集公理**：并和交的验证
2. **理想的生成**：拟紧性的代数表达
3. **原像计算**：连续性的自然验证

## 常见错误

- ❌ 忘记 $V(I) = V(\sqrt{I})$
- ❌ 拟紧性证明中未利用1的有限表示
- ❌ 诱导映射定义中忘记扩张理想

## 变式练习

**变式1：** 计算 $\text{Spec}(\mathbb{Z})$ 的拓扑。

**变式2：** 证明 $\text{Spec}(k[x,y])$ 的闭集是代数曲线和点的并。
