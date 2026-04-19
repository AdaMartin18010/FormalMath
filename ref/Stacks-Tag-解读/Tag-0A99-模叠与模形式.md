---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0A99 - 模叠与模形式

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0A99 |
| **英文名称** | Moduli Stacks and Modular Forms |
| **所属章节** | Moduli of Curves |
| **主题分类** | 代数几何 - 模空间理论 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 模叠概述

**模叠**（Moduli Stack）是代数几何中参数化几何对象（如曲线、向量丛等）的叠（Stack）。与模概形不同，模叠可以正确处理对象具有非平凡自同构的情形。

### 2.2 关键定义

**定义 2.2.1**（叠 - Stack）
在范畴 $S$（通常是概形范畴）上，一个**叠** $\mathcal{M}$ 是一个纤维范畴，满足：

- **下降条件**：对于覆盖 $\{U_i \to U\}$，对象和态射可以粘合

等价于：$
\mathcal{M}$ 是从概形到群胚（groupoids）的层。

**定义 2.2.2**（代数叠）
一个**代数叠**（Algebraic Stack）是叠 $\mathcal{M}$，满足：
- 对角线 $\Delta: \mathcal{M} \to \mathcal{M} \times \mathcal{M}$ 是分离、拟紧的
- 存在**光滑覆盖** $U \to \mathcal{M}$，其中 $U$ 是概形

**定义 2.2.3**（Deligne-Mumford叠）
一个**Deligne-Mumford叠**是代数叠，存在**étale覆盖** $U \to \mathcal{M}$。

等价地：对角线是无挠的（unramified）。

### 2.3 模叠的例子

**定义 2.3.1**（椭圆曲线模叠 $\mathcal{M}_{1,1}$）
**模叠 of 椭圆曲线**定义为：

$$\mathcal{M}_{1,1}(S) = \{(E \to S, e: S \to E) : E/S \text{ 光滑，纤维亏格1}\}$$

态射是Cartier除子的同构。

**定义 2.3.2**（稳定曲线模叠 $\overline{\mathcal{M}}_{g,n}$）
**Deligne-Mumford模叠** of 稳定 $n$-点标定亏格$g$曲线：

$$\overline{\mathcal{M}}_{g,n}(S) = \{(C \to S, s_1, \ldots, s_n) : C/S \text{ 稳定曲线}\}/\cong$$

稳定性：$\omega_C(\sum s_i)$ 是 $C/S$ 上的丰富层。

---

## 3. 主要结果与定理

### 3.1 模叠的基本性质

**定理 3.1.1**（Tag 0A99）
模叠 $\mathcal{M}_{1,1}$ 和 $\overline{\mathcal{M}}_{g,n}$ 具有以下性质：

**(a) Deligne-Mumford性质**
$\mathcal{M}_{1,1}$ 和 $\overline{\mathcal{M}}_{g,n}$（对于 $2g-2+n > 0$）是Deligne-Mumford叠。

**(b) 分离性**
它们是真（proper）的Deligne-Mumford叠。

**(c) 光滑性**
它们是在 $\text{Spec}(\mathbb{Z})$ 上的光滑叠。

**(d) 维数**
$$\dim \mathcal{M}_{1,1} = 1$$
$$\dim \overline{\mathcal{M}}_{g,n} = 3g-3+n$$

### 3.2 模形式

**定理 3.2.1**（模形式与模叠）
**模形式**可以解释为模叠上的线丛的截面：

**(a) 权$k$模形式**
$$M_k(\Gamma) = H^0(\mathcal{M}_\Gamma, \omega^{\otimes k})$$

其中 $\omega = \pi_*\Omega^1_{E/\mathcal{M}}$ 是Hodge线丛。

**(b) 尖点形式**
$$S_k(\Gamma) = H^0(\overline{\mathcal{M}}_\Gamma, \omega^{\otimes k}(-D))$$

其中 $D$ 是边界除子。

**定理 3.2.2**（Kodaira维数）
对于模叠 $\overline{\mathcal{M}}_g$：

- $g = 0, 1$：unirational（有理的）
- $g = 2, 3, 4, 5$：unirational
- $g \geq 22$：一般型（general type）
- $g = 23$：中间情形（geometry of genus unknown）

### 3.3 Picard群

**定理 3.3.1**（Harber, Mumford, Harris）
$$\text{Pic}(\overline{\mathcal{M}}_{g,n}) \otimes \mathbb{Q}$$

由以下生成：
- $\lambda$（Hodge类）
- $\psi_1, \ldots, \psi_n$（点标定类）
- $\delta_{irr}, \delta_{i,S}$（边界类）

关系由Mumford公式等给出。

---

## 4. 证明思路

### 4.1 Deligne-Mumford性质的证明

**步骤1**：自同构群
- 稳定曲线的自同构群是有限的
- 这保证了对角线是无挠的

**步骤2**：覆盖的构造
- 使用三典范嵌入（tricanonical embedding）
- 将曲线嵌入到射影空间
- Hilbert概形提供覆盖

**步骤3**：局部结构
- 在点 $[C]$ 处，局部结构由形变理论控制
- Kuranishi族：$H^1(C, T_C)$ 参数化局部形变

### 4.2 真性的证明

**步骤1**：Valuative准则
- 检查离散赋值环上的曲线可以完备化
- 这是**稳定约化定理**的内容

**步骤2**：分离性
- 使用稳定约化的唯一性

### 4.3 模形式的计算

**核心观察**：
模形式是**自守形式**的几何解释：

$$H^0(\mathcal{M}_{1,1}, \omega^k) \cong M_k(SL_2(\mathbb{Z}))$$

计算使用：
1. 上半平面的商实现
2. 或几何不变量理论

---

## 5. 应用与例子

### 5.1 椭圆曲线的模

**例子 5.1.1**（$j$-不变量）
粗糙模空间（coarse moduli space）：

$$M_{1,1} = \mathbb{A}^1_j$$

其中 $j(E) = 1728\frac{4a^3}{4a^3+27b^2}$ 对于 $E: y^2 = x^3 + ax + b$。

**例子 5.1.2**（模形式环）
$$
\bigoplus_{k \geq 0} M_k(SL_2(\mathbb{Z})) = \mathbb{C}[E_4, E_6]$$

其中 $E_4, E_6$ 是Eisenstein级数。

判别式 $\Delta = \frac{E_4^3 - E_6^2}{1728}$ 是权12的尖点形式。

### 5.2 计数几何

**应用 5.2.1**（Hurwitz数）
计算亏格$g$曲线到 $\mathbb{P}^1$ 的$d$次覆盖数：

$$H_{g,d} = \int_{\overline{\mathcal{M}}_{g,n}} \psi_1^{a_1} \cdots \psi_n^{a_n}$$

使用Witten猜想/Kontsevich定理计算。

**应用 5.2.2**（Gromov-Witten不变量）
对于靶空间 $X$，GW不变量：

$$\langle \tau_{a_1}(\gamma_1) \cdots \tau_{a_n}(\gamma_n) \rangle_{g,n,\beta}^X$$

可以通过模叠 $\overline{\mathcal{M}}_{g,n}(X, \beta)$ 定义。

### 5.3 弦论

**应用 5.3.1**（镜面对称）
Calabi-Yau 3-fold的镜像对称涉及模形式：

- A-模型：Gromov-Witten不变量
- B-模型：周期积分（与模形式相关）

**应用 5.3.2**（Borcherds的魔群月光）
魔群（Monster group）与模形式的深刻联系：

$$j(\tau) - 744 = q^{-1} + 196884q + 21493760q^2 + \cdots$$

系数与魔群的不可约表示维度相关。

### 5.4 拓扑模形式

**应用 5.4.1**（Hopkins的定理）
椭圆曲线模叠关联的拓扑模形式：

$$\pi_{2k}(\text{TMF}) \cong \{\text{弱模形式 of weight } k\}$$

这联系了代数拓扑与数论。

---

## 6. 与其他概念的关系

### 6.1 模空间的层次结构

```
    粗模空间 $M_{g,n}$
          │
          │ 添加自同构信息
          ▼
    Deligne-Mumford叠 $\overline{\mathcal{M}}_{g,n}$
          │
          │ 导出化
          ▼
    导出模叠 $R\overline{\mathcal{M}}_{g,n}$
          │
          │ 考虑所有复形
          ▼
    导出增强叠
```

### 6.2 与模形式的关系

| 几何对象 | 模形式解释 |
|---------|-----------|
| $\mathcal{M}_{1,1}$ | 权$k$模形式 = $\omega^k$ 的截面 |
| $E_4, E_6$ | Hodge线丛的陈类 |
| $\Delta$ | 边界除子的截面 |
| $j$ | 粗糙模空间的坐标 |

### 6.3 与弦论的关系

| 数学概念 | 物理解释 |
|---------|---------|
| $\overline{\mathcal{M}}_{g,n}$ | 弦的世界面模空间 |
| 模形式 | 配分函数 |
| Virasoro约束 | Witten猜想 |
| TMF | 椭圆上同调 |

---

## 7. 参考文献

### 7.1 奠基文献

1. **Deligne, P. & Mumford, D.** (1969). *The irreducibility of the space of curves of given genus*
   - Publ. Math. IHÉS 36
   - $\overline{\mathcal{M}}_{g,n}$ 的原始定义

2. **Mumford, D.** (1977). *Stability of projective varieties*
   - Lectures on curves on an algebraic surface
   - 模叠的几何不变量理论

3. **Deligne, P.** (1975). *Courbes elliptiques: formulaire d'après J. Tate*
   - 椭圆曲线的模形式

### 7.2 现代发展

4. **Harris, J. & Morrison, I.** (1998). *Moduli of Curves*
   - Springer GTM 187
   - 标准教科书

5. **Arbarello, E., Cornalba, M., Griffiths, P.** (2011). *Geometry of Algebraic Curves, Vol II*
   - 模叠的深层理论

6. **Farkas, G. & Morrison, I.** (2013). *Handbook of Moduli*
   - 现代综述

### 7.3 模形式

7. **Diamond, F. & Shurman, J.** (2005). *A First Course in Modular Forms*
   - Springer GTM 228
   - 模形式的全面介绍

8. **Zagier, D.** (2008). *Elliptic modular forms and their applications*
   - The 1-2-3 of Modular Forms

### 7.4 在线资源

9. **Stacks Project**: [Tag 0A99](https://stacks.math.columbia.edu/tag/0A99)
10. **Stacks Project**: [Chapter Moduli of Curves](https://stacks.math.columbia.edu/chapter/0E6C)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0A9A](#tag-0a9a) | 椭圆曲线模空间 | 具体例子 |
| [0A9B](#tag-0a9b) | 模形式的层 | 结构层 |
| [0E6C](#tag-0e6c) | 稳定曲线模叠 | 主要对象 |

### 8.2 模空间理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0E6D](#tag-0e6d) | 叠的基础 | 理论框架 |
| [0E6E](#tag-0e6e) | 代数叠 | 一般理论 |
| [0E6F](#tag-0e6f) | Deligne-Mumford叠 | 特殊类型 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0E6G](#tag-0e6g) | Hurwitz空间 | 应用 |
| [0E6H](#tag-0e6h) | Gromov-Witten理论 | 现代应用 |
| [0E6I](#tag-0e6i) | Picard群计算 | 具体不变量 |

---

## 附录：模形式公式

### Eisenstein级数

$$E_k(\tau) = 1 - \frac{2k}{B_k}\sum_{n=1}^\infty \sigma_{k-1}(n)q^n$$

其中 $q = e^{2\pi i \tau}$，$\sigma_{k-1}(n) = \sum_{d|n} d^{k-1}$，$B_k$ 是Bernoulli数。

### 维数公式

$$\dim M_k(SL_2(\mathbb{Z})) = \begin{cases} \lfloor k/12 \rfloor & k \equiv 2 \pmod{12} \\ \lfloor k/12 \rfloor + 1 & \text{否则} \end{cases}$$

（对于 $k \geq 0$ 偶数）

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
