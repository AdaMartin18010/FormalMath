# Sobolev空间 (Sobolev Spaces)

## 中心概念精确定义

**Sobolev空间**是含弱导数的函数空间，是现代偏微分方程理论和数值分析的核心框架。

> **弱导数**：设 $f, g \in L^1_{loc}(\Omega)$，称 $g$ 是 $f$ 的 $\alpha$ 阶弱导数，记作 $D^\alpha f = g$，如果：
> $$\int_\Omega f \cdot D^\alpha \phi\,dx = (-1)^{|\alpha|} \int_\Omega g \cdot \phi\,dx, \quad \forall \phi \in C_c^\infty(\Omega)$$

> **Sobolev空间** $W^{k,p}(\Omega)$：
> $$W^{k,p}(\Omega) = \{f \in L^p(\Omega) : D^\alpha f \in L^p(\Omega), \forall |\alpha| \leq k\}$$
> 范数：$\|f\|_{W^{k,p}} = \left(\sum_{|\alpha| \leq k} \|D^\alpha f\|_{L^p}^p\right)^{1/p}$

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Sobolev空间<br/>Sobolev Spaces W^{k,p}))
    弱导数
      定义
        分部积分公式
        测试函数
      性质
        唯一性
        线性性
        Leibniz法则
      例子
        |x|的导数
        阶梯函数
    Sobolev空间
      定义
        W^{k,p}
        H^k=W^{k,2}
      范数
        导数L^p范数
        等价范数
      完备性
        Banach空间
        Hilbert空间(H^k)
    逼近定理
      Meyers-Serrin
        W^{k,p}=H^{k,p}
        光滑稠密
      延拓定理
        有界Lipschitz域
        全空间延拓
      磨光
        J_εf→f
        标准技巧
    嵌入定理
      Sobolev嵌入
        W^{k,p}↪L^q
        临界指数
      紧嵌入
        Rellich-Kondrachov
        有界域
      Morrey定理
        W^{k,p}↪C^{m,α}
        超临界情形
    迹定理
      边界值
        γ:W^{1,p}→L^p(∂Ω)
        有界线性
      核空间
        W_0^{1,p}
        零边值
      应用
        边值问题
        变分形式
    PDE应用
      弱解
        Lax-Milgram
        存在唯一性
      正则性
        内部正则
        边界正则
      例子
        Laplace方程
        散度型方程
```

---

## 核心要素详解

### 1. 弱导数理论

**动机**：经典导数要求太强，许多物理问题的解不可微。

**例子**：$f(x) = |x|$ 在 $\mathbb{R}$ 上
- 经典导数：在 $x=0$ 不存在
- 弱导数：$g(x) = \text{sgn}(x)$（符号函数）

验证：对 $\phi \in C_c^\infty$：
$$\int_{-\infty}^{\infty} |x| \phi'(x)dx = -\int_{-\infty}^{\infty} \text{sgn}(x) \phi(x)dx$$

**与分布导数的关系**：弱导数存在且局部可积 $\Leftrightarrow$ 分布导数是正则分布。

### 2. Sobolev空间的基本结构

**$H^k$ 空间**：$W^{k,2}(\Omega) = H^k(\Omega)$ 是Hilbert空间，内积：
$$(f, g)_{H^k} = \sum_{|\alpha| \leq k} \int_\Omega D^\alpha f \cdot \overline{D^\alpha g}\,dx$$

**重要特例**：
- $W^{0,p} = L^p$
- $W^{1,p}$：一阶弱导数在 $L^p$ 中

**Sobolev范数的等价形式**：
- 全导数范数 vs 最高阶导数范数（Poincaré不等式保证等价性）

### 3. Meyers-Serrin 逼近定理

**定理（$H = W$）**：对 $1 \leq p < \infty$，$C^\infty(\Omega) \cap W^{k,p}(\Omega)$ 在 $W^{k,p}(\Omega)$ 中稠密。

即：$W^{k,p}$ 函数可以用光滑函数逼近。

**证明思路**：
1. 局部化（单位分解）
2. 平移磨光
3. 拼接

**注意**：$C_c^\infty(\Omega)$ 一般不在 $W^{k,p}(\Omega)$ 中稠密，其闭包是 $W_0^{k,p}(\Omega)$。

### 4. Sobolev嵌入定理

**Sobolev嵌入**：设 $\Omega \subset \mathbb{R}^n$ 是有界光滑域。

**临界指数**：$p^* = \frac{np}{n-kp}$（当 $kp < n$）

**嵌入结果**：

| 条件 | 嵌入 | 说明 |
|------|------|------|
| $kp < n$ | $W^{k,p} \hookrightarrow L^{p^*}$ | 连续嵌入 |
| $kp = n$ | $W^{k,p} \hookrightarrow L^q$，$\forall q < \infty$ | 临界情形 |
| $kp > n$ | $W^{k,p} \hookrightarrow C^{m,\alpha}$ | Morrey嵌入 |

**Gagliardo-Nirenberg-Sobolev不等式**（$kp < n$）：
$$\|f\|_{L^{p^*}} \leq C \|Df\|_{L^p}$$

### 5. Rellich-Kondrachov 紧嵌入

**紧嵌入定理**：设 $1 \leq p < \infty$，$\Omega$ 有界，则：
- $W^{1,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$，$1 \leq q < p^*$（$kp < n$ 情形）
- $W^{1,p}(\Omega) \hookrightarrow\hookrightarrow C(\bar{\Omega})$（$kp > n$ 情形）

**意义**：有界集在 $L^q$ 中是相对紧的，用于证明紧算子和特征值问题。

### 6. 迹定理与边界值

**迹算子**：存在有界线性算子 $\gamma: W^{1,p}(\Omega) \to L^p(\partial\Omega)$ 使得对 $f \in C^\infty(\bar{\Omega})$：
$$\gamma(f) = f|_{\partial\Omega}$$

**核空间**：$W_0^{1,p}(\Omega) = \{f \in W^{1,p} : \gamma(f) = 0\} = \overline{C_c^\infty}^{W^{1,p}}$

**Poincaré不等式**：对 $f \in W_0^{1,p}(\Omega)$，$\Omega$ 有界：
$$\|f\|_{L^p} \leq C \|\nabla f\|_{L^p}$$

**意义**：在 $W_0^{1,p}$ 中，$\|\nabla f\|_{L^p}$ 等价于全范数。

---

## 关键性质与定理

### 定理1：Poincaré不等式

**定理**：设 $\Omega$ 有界，$1 \leq p < \infty$，则存在 $C = C(\Omega, p)$：
$$\|f - f_\Omega\|_{L^p} \leq C \|\nabla f\|_{L^p}, \quad \forall f \in W^{1,p}(\Omega)$$

其中 $f_\Omega = \frac{1}{|\Omega|}\int_\Omega f$ 是平均值。

**推论**：在 $W_0^{1,p}$ 或平均值为零的函数上，$\|\nabla f\|_{L^p}$ 与全范数等价。

### 定理2：Sobolev不等式

**GNS不等式**（$1 \leq p < n$）：
$$\|f\|_{L^{p^*}} \leq C \|\nabla f\|_{L^p}, \quad p^* = \frac{np}{n-p}$$

**最优常数**（Aubin-Talenti）：对 $p=2$，最优常数由某些径向函数达到。

### 定理3：Lax-Milgram定理与弱解

**Lax-Milgram**：设 $a(\cdot, \cdot)$ 是Hilbert空间 $H$ 上的双线性形式，满足：
- **有界性**：$|a(u,v)| \leq C\|u\|\|v\|$
- **强制性**：$a(u,u) \geq c\|u\|^2$

则对任意 $f \in H^*$，存在唯一的 $u \in H$ 使得 $a(u,v) = \langle f, v \rangle$ 对所有 $v \in H$。

**应用**：椭圆方程 $-\Delta u + u = f$ 在 $H^1$ 中的弱解存在唯一。

### 定理4：内部正则性

**定理**：设 $u \in H^1(\Omega)$ 是 $Lu = f$ 的弱解，$L$ 是具光滑系数的椭圆算子。
- 若 $f \in H^k$，则 $u \in H^{k+2}_{loc}$（$k \geq 0$）
- 若 $f \in C^\infty$，则 $u \in C^\infty_{loc}$

**Bootstrap论证**：通过迭代提高正则性。

---

## 典型例子

### 例子1：一维Sobolev函数的特征

**定理**：$W^{1,1}(a,b)$ 恰好是绝对连续函数空间。

即：$f \in W^{1,1}$ $\Leftrightarrow$ $f$ 绝对连续，且 $f' \in L^1$。

### 例子2：角点奇异性

在扇形域 $\Omega = \{(r,\theta) : 0 < r < 1, 0 < \theta < \omega\}$ 上，函数：
$$u(r,\theta) = r^{\pi/\omega} \sin\frac{\pi\theta}{\omega}$$

满足 $\Delta u = 0$，在 $r=0$ 处：
- $\omega < \pi$（凸角）：$u$ 光滑
- $\omega > \pi$（凹角）：$u \in H^1$ 但不属于 $H^2$

### 例子3：变分问题中的极小元

**Dirichlet原理**：在 $W_0^{1,2}(\Omega)$ 上最小化：
$$J(u) = \int_\Omega |\nabla u|^2$$

约束 $u = g$ 在 $\partial\Omega$。

解满足Euler-Lagrange方程：$-\Delta u = 0$。

---

## 关联概念网络

### 相似概念

| 概念 | 关系 | 说明 |
|------|------|------|
| **Besov空间** | 细化 | 插值尺度更精细 |
| **Triebel-Lizorkin** | 细化 | Fourier分解定义 |
| **BV空间** | 边界情形 | 有界变差函数 |
| **BD空间** | 应用 | 有界变形（塑性力学） |

### 对偶概念

| 概念 | 对偶关系 | 说明 |
|------|----------|------|
| **$W^{k,p} \leftrightarrow W^{-k,q}$** | 对偶对 | $1/p+1/q=1$ |
| **$H^s \leftrightarrow H^{-s}$** | Hilbert对偶 | 分数阶Sobolev |

### 推广概念

```
Sobolev空间 W^{k,p} → Besov空间 B^{s}_{p,q}
      ↓
   Triebel-Lizorkin F^{s}_{p,q}
      ↓
   各向异性Sobolev
      ↓
   加权Sobolev
```

---

## 课程对齐

### MIT 18.155/18.156
- **Topic**: Sobolev spaces, elliptic PDEs
- **Text**: Evans, *Partial Differential Equations*, Ch. 5
- **Key topics**: Weak derivatives, embedding theorems, trace theorem, applications

### Princeton MAT 425
- **Topic**: Functional analysis of PDEs
- **Text**: Brezis, *Functional Analysis, Sobolev Spaces and PDEs*
- **Emphasis**: Lax-Milgram, regularity, compactness methods

---

## 总结

Sobolev空间是现代偏微分方程理论的基石，它通过弱导数的概念将微分运算推广到不可微函数上。嵌入定理揭示了Sobolev空间与连续函数空间、可积空间之间的包含关系，而紧嵌入定理为特征值问题和紧算子理论提供了关键工具。迹定理允许我们讨论Sobolev函数在边界上的值，这是处理边值问题的必要条件。结合Lax-Milgram定理，Sobolev空间为椭圆型偏微分方程的弱解理论提供了完整的框架。

---

*创建日期：2026年4月*  
*相关概念：[分布理论](分布理论.md)、[Lp空间](Lp空间.md)、[变分法](变分法.md)*
