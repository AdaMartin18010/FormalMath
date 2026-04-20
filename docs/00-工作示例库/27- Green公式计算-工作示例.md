---
msc_primary: 00

  - 00A99
  - 26A42
  - 03B40
title: Green 公式计算 - 工作示例
processed_at: '2026-04-05'
---
# Green 公式计算 - 工作示例

**类型**: 计算示例 **领域**: 向量分析 **难度**: L1 **创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 用 Green 公式将线积分化为二重积分 |
| **领域** | 分析学 |
| **MSC** | 26B20 |

---

## 一、定义与理论背景

### 1.1 曲线积分

设 \(C\) 为平面上的分段光滑有向曲线，\(\mathbf{F} = (P, Q)\) 为向量场。**第二类曲线积分**定义为：

$$
\oint_C P\,dx + Q\,dy = \int_C \mathbf{F} \cdot d\mathbf{r}
$$

其中 \(d\mathbf{r} = (dx, dy)\)。方向约定：沿 \(C\) 行走时区域 \(D\) 始终在左侧，称为**正向**（逆时针）。

### 1.2 单连通区域

平面区域 \(D\) 称为**单连通**，若 \(D\) 内任意简单闭曲线所围区域完全包含于 \(D\)。直观上，单连通区域"没有洞"。

---

## 二、核心定理

### 定理 2.1（Green 公式）

设 \(D\) 为平面上的有界闭区域，其边界 \(\partial D\) 由有限条分段光滑简单闭曲线组成，取正向。若 \(P(x,y)\) 和 \(Q(x,y)\) 在包含 \(D\) 的某开集上具有连续偏导数，则：

$$
\oint_{\partial D} P\,dx + Q\,dy = \iint_D \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dA
$$

### 定理 2.2（面积公式）

取 \(P = -y/2, Q = x/2\)，则 \(\partial Q/\partial x - \partial P/\partial y = 1\)。因此区域 \(D\) 的面积为：

$$
\text{Area}(D) = \frac{1}{2} \oint_{\partial D} x\,dy - y\,dx
$$

### 定理 2.3（等价条件，平面向量场）

设 \(D\) 为单连通区域，\(P, Q\) 在 \(D\) 上连续可微。以下条件等价：
1. \(\oint_C P\,dx + Q\,dy = 0\) 对任意闭曲线 \(C\) 成立
2. 积分与路径无关
3. 存在势函数 \(\varphi\) 使得 \(d\varphi = P\,dx + Q\,dy\)
4. \(\partial P/\partial y = \partial Q/\partial x\) 在 \(D\) 上处处成立

---

## 三、推导过程

Green 公式是**Stokes 公式**的二维特例，也是**Newton-Leibniz 公式**在高维的推广。

**证明概要**：先证矩形区域情形。设 \(D = [a,b] \times [c,d]\)。则：

$$
\iint_D \frac{\partial Q}{\partial x}\,dA = \int_c^d \left[\int_a^b \frac{\partial Q}{\partial x}\,dx\right] dy = \int_c^d [Q(b,y) - Q(a,y)]\,dy
$$

这恰等于 \(\oint_{\partial D} Q\,dy\) 中上下边的贡献。同理处理 \(P\) 项。对一般区域，用矩形网格逼近。

---

## 四、题目与完整解答

### 题目

用 Green 公式求 \(\oint_C x^2\,dx + xy\,dy\)，其中 \(C\) 为单位圆逆时针。

### 完整解答

**步骤 1：识别分量**

设 \(P(x,y) = x^2\)，\(Q(x,y) = xy\)。计算偏导数：

$$
\frac{\partial Q}{\partial x} = y, \quad \frac{\partial P}{\partial y} = 0
$$

**步骤 2：应用 Green 公式**

区域 \(D\) 为单位圆盘 \(\{(x,y) : x^2 + y^2 \leq 1\}\)。由 Green 公式：

$$
\oint_C x^2\,dx + xy\,dy = \iint_D \left(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dA = \iint_D y\,dA
$$

**步骤 3：计算二重积分**

被积函数 \(y\) 关于 \(y\) 是奇函数，而区域 \(D\) 关于 \(x\) 轴对称。因此：

$$
\iint_D y\,dA = 0
$$

也可用极坐标验证：\(y = r\sin\theta\)，\(dA = r\,dr\,d\theta\)

$$
\iint_D y\,dA = \int_0^{2\pi} \int_0^1 r\sin\theta \cdot r\,dr\,d\theta = \left(\int_0^1 r^2\,dr\right)\left(\int_0^{2\pi} \sin\theta\,d\theta\right) = \frac{1}{3} \cdot 0 = 0
$$

**答案**：\(\oint_C x^2\,dx + xy\,dy = 0\)。

---

## 五、应用与拓展

### 5.1 平面静电学

静电场 \(\mathbf{E}\) 满足 \(\oint_C \mathbf{E} \cdot d\mathbf{r} = 0\)（保守场）。由 Green 公式等价于 \(\nabla \times \mathbf{E} = 0\)（二维旋度为零）。

### 5.2 流体力学

对二维不可压缩流体的速度场 \(\mathbf{v} = (u, v)\)，环量 \(\oint_C \mathbf{v} \cdot d\mathbf{r}\) 由 Green 公式化为涡量 \(\omega = \partial v/\partial x - \partial u/\partial y\) 在区域上的积分。

### 5.3 复分析中的 Cauchy 定理

对复函数 \(f(z) = u + iv\)，Cauchy-Riemann 条件 \(\partial u/\partial x = \partial v/\partial y\)，\(\partial u/\partial y = -\partial v/\partial x\) 正是使 Green 公式中实部和虚部同时为零的条件。

---

**文档状态**: ✅ 完成 **最后更新**: 2026年4月20日
