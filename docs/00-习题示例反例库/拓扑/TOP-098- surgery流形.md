---
msc_primary: 00A99
习题编号: TOP-098
学科: 拓扑
知识点: 拓扑-surgery流形
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Surgery 流形结构

## 题目

**(a)** 证明 Browder-Novikov 手术理论的基本定理。

**(b)** 讨论同伦球面的分类（Kervaire-Milnor）。

**(c)** 证明高维 Poincaré 猜想的 surgery 证明。

## 解答

### (a) Browder-Novikov 定理

**设置**：$X^n$ 是单连通 Poincaré 复形（$n \geq 5$）。

**问题**：$X$ 是否同伦等价于光滑流形？

**定理（Browder-Novikov）**：$X$ 有光滑流形结构当且仅当：

1. **Spivak 法丛存在**：存在稳定球面丛 $\nu_X$ 使得 Thom 空间 $Th(\nu_X)$ 有底细胞
2. **Surgery 阻碍消失**：法丛约化到 $BSO$ 后，度一正常映射 $f: M \to X$ 的 surgery 阻碍 $\sigma(f) = 0 \in L_n(1)$

*证明概要*：

1. **存在法丛**：Poincaré 复形有稳定球面丛（Spivak）。

2. **约化到 $BSO$**：阻碍在 $H^*(X; \mathbb{Z}/2)$（$w_1, w_2$）。

3. **Thom-Pontryagin**：给出度一正常映射 $f: M \to X$。

4. **Surgery 精确列**：$\mathcal{S}(X) \to \mathcal{N}(X) \to L_n(1)$。

5. **单连通 $L$-群**：$L_{4k}(1) = \mathbb{Z}$（标志差），$L_{4k+2}(1) = \mathbb{Z}/2$（Arf），$L_{2k+1}(1) = 0$。

---

### (b) 同伦球面的分类

**定义**：$\Theta_n = \{h\text{-cobordism 类的 } n\text{-维同伦球面}\}$。

**定理（Kervaire-Milnor, 1963）**：$\Theta_n$ 是有限 Abel 群（$n \neq 3$）。

**正合列**：

$$0 \to bP_{n+1} \to \Theta_n \to \Theta_n / bP_{n+1} \to 0$$

- $bP_{n+1}$：边界可平行化的同伦球面（与 surgery 阻碍相关）
- $\Theta_n / bP_{n+1} \hookrightarrow \pi_n^S / J(\pi_n(SO))$（J-同态的余核）

**具体值**：

| $n$ | $\Theta_n$ | $bP_{n+1}$ |
|-----|-----------|-----------|
| 5,6 | 0 | 0 |
| 7 | $\mathbb{Z}/28$ | $\mathbb{Z}/28$ |
| 8 | $\mathbb{Z}/2$ | 0 |
| 9 | $\mathbb{Z}/2 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/2$ | $\mathbb{Z}/2$ |
| 10 | $\mathbb{Z}/6$ | $\mathbb{Z}/6$ |
| 11 | $\mathbb{Z}/992$ | $\mathbb{Z}/992$ |

---

### (c) 高维 Poincaré 猜想

**定理（Smale, 1961；Stallings, Zeeman）**：$n \geq 5$ 时，同伦等价于 $S^n$ 的拓扑流形同胚于 $S^n$。

*Surgery 证明*：

1. **h-配边定理**：单连通 h-配边 $(W; M, M')$ 微分同胚于 $M \times [0,1]$（$n \geq 5$）。

2. **同伦球面 = h-配边边界**：设 $\Sigma^n$ 是同伦球面。取 $W = \Sigma^n \times [0,1]$。

3. **消去流柄**：$W$ 有流柄分解，由 h-配边定理可消去所有流柄。

4. **结论**：$W \cong \Sigma^n \times [0,1]$，故 $\Sigma^n \cong S^n$。

**光滑 Poincaré 猜想**：$n \geq 5$ 时同伦球面是否微分同胚于 $S^n$？

**答案**：否！Milnor 的怪球面 $\Sigma^7$ 同胚但非微分同胚于 $S^7$。

**拓扑 Poincaré 猜想**：Freedman（$n=4$，1982），Perelman（$n=3$，2003）。

---

## 常见错误

- **Surgery 阻碍的方向**：$L_n(1)$ 的生成元对应哪些几何不变量（标志差、Arf）。
- **$\Theta_n$ 的群运算**：连通和，非笛卡尔积。
- **h-配边 vs s-配边**：h-配边要求同伦等价，s-配边要求简单同伦等价（涉及 Whitehead 群）。

## 参考文献

- Browder, *Surgery on Simply-Connected Manifolds*.
- Kervaire & Milnor, *Groups of homotopy spheres I*.
