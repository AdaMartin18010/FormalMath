# 偏导数 → 可微性 → 链式法则推理树

## 概述
本推理树展示多元微分学核心链条：从偏导数定义到多元函数可微性，最终建立链式法则的完整理论框架。

```mermaid
graph TD
    subgraph 偏导数定义
        A1[方向导数] --> A2[偏导数定义]
        A2 --> A3[∂f/∂x, ∂f/∂y]
        A3 --> A4[几何意义]
        A4 --> A5[偏导存在不一定连续]
    end
    
    subgraph 可微性
        A2 --> B1[多元可微定义]
        B1 --> B2[线性逼近]
        B2 --> B3[全微分df]
        B3 --> B4[可微⇒连续]
        B3 --> B5[可微⇒偏导存在]
    end
    
    subgraph 偏导连续条件
        A3 --> C1[偏导连续]
        C1 --> C2[偏导连续⇒可微]
        C2 --> C3[充分非必要条件]
    end
    
    subgraph 链式法则
        B1 --> D1[一元复合链式法则]
        B1 --> D2[多元复合链式法则]
        D2 --> D3[树形图法则]
        D3 --> D4[矩阵形式Jacobi]
    end
    
    subgraph 梯度与方向导数
        B3 --> E1[梯度定义∇f]
        E1 --> E2[方向导数公式]
        E2 --> E3[梯度是最大方向]
    end
    
    style B1 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style D2 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
```

## 推理步骤详解

### 第一步：偏导数定义

**定义**：设 $f: \mathbb{R}^n \to \mathbb{R}$，在点 $a$ 关于 $x_i$ 的偏导数：

$$\frac{\partial f}{\partial x_i}(a) = \lim_{h \to 0} \frac{f(a + he_i) - f(a)}{h}$$

其中 $e_i$ 是第 $i$ 个单位向量。

### 第二步：可微性定义

**定义**：$f$ 在 $a$ 点可微，若存在线性映射 $L: \mathbb{R}^n \to \mathbb{R}$：

$$f(a + h) - f(a) = L(h) + o(\|h\|), \quad h \to 0$$

**定理**：若 $f$ 可微，则偏导数存在且 $L(h) = \sum \frac{\partial f}{\partial x_i}(a) h_i$

### 第三步：链式法则

**定理**：设 $g: \mathbb{R}^m \to \mathbb{R}^n$ 在 $x$ 可微，$f: \mathbb{R}^n \to \mathbb{R}^p$ 在 $g(x)$ 可微，则 $f \circ g$ 可微且：

$$D(f \circ g)(x) = Df(g(x)) \cdot Dg(x)$$

Jacobi矩阵形式：$J_{f \circ g} = J_f \cdot J_g$

### 第四步：梯度与方向导数

**梯度**：$\nabla f = (\frac{\partial f}{\partial x_1}, ..., \frac{\partial f}{\partial x_n})$

**方向导数**：$D_u f = \nabla f \cdot u$

**性质**：$|\nabla f|$ 是最大方向导数，方向为梯度方向。
