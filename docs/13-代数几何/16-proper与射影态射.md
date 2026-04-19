---
title: proper与射影态射
description: 深入探讨proper态射、射影态射的定义与判别准则，包括 valuative 判据、Chow 引理以及它们在紧化与模问题中的应用。
msc_primary:
  - 14A15
msc_secondary:
  - 14E05
  - 14D20
  - 14A20
processed_at: '2026-04-20'
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
        - Robin Hartshorne
      publisher: Springer
      year: 1977
      msc: 14-01
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
        - Ravi Vakil
      publisher: self-published
      year: 2024
  databases:
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
---

# proper与射影态射

## 引言

在拓扑学中，紧空间具有极为优良的性质：映射的像紧、连续函数达到最大最小值、序列有收敛子列等。在代数几何中，由于Zariski拓扑远非Hausdorff，传统的"紧性"概念不再适用。然而，通过**proper态射**（proper morphism）这一精巧的定义，代数几何成功地捕捉了"代数紧性"的本质。

proper态射由Grothendieck引入，它推广了紧Hausdorff空间上映射的闭性和逆紧性。射影态射（projective morphism）则是proper态射的重要子类，它直接对应于到射影空间的嵌入和线性系的几何。

本教程深入探讨proper与射影态射的定义、判别准则（包括valuative判据）以及它们在模问题中的应用。

---

## 1. proper态射

### 1.1 定义

**定义 1.1（proper态射）**。概形态射 $f: X \to Y$ 称为**proper的**，如果：
1. $f$ 是**分离的**（separated）：对角线 $\Delta: X \to X \times_Y X$ 是闭浸入。
2. $f$ 是** universally closed**的：对任意基变换 $Y' \to Y$，投影 $X \times_Y Y' \to Y'$ 是闭映射。
3. $f$ 是**有限型**的。

### 1.2 Valuative判据

**定理 1.2（proper的valuative判据）**。有限型分离态射 $f: X \to Y$ 是proper的当且仅当：对任意赋值环 $R$（以 $K$ 为分式域）和任意交换图表

$$\begin{array}{ccc}
\operatorname{Spec} K & \longrightarrow & X \\
\downarrow & & \downarrow f \\
\operatorname{Spec} R & \longrightarrow & Y
\end{array}$$

存在唯一的态射 $\operatorname{Spec} R \to X$ 使图表交换。

*直观*。proper性保证了"极限点"（由赋值环的整闭性编码）在 $X$ 中存在且唯一。

---

## 2. 射影态射

### 2.1 定义

**定义 2.1（射影态射）**。态射 $f: X \to Y$ 称为**射影的**（projective），如果它可分解为闭浸入 $X \hookrightarrow \mathbb{P}^n_Y$ 后接投影 $\mathbb{P}^n_Y \to Y$。

### 2.2 性质

**定理 2.2**。射影态射是proper的。

*证明*。投影 $\mathbb{P}^n_Y \to Y$ 是proper的（可直接验证universally closed），而闭浸入也是proper的，故合成proper。$\square$

**定理 2.3（射影化判据）**。设 $\mathcal{L}$ 为 $X$ 上的丰富线丛（ample line bundle），$f: X \to Y$ 为态射。若 $f$  proper 且 $\mathcal{L}$ 在 $Y$ 上相对丰富（relatively ample），则 $f$ 是射影的。

---

## 3. Chow引理

**定理 3.1（Chow引理）**。设 $X$ 为Noether概形，$f: X \to S$ 为分离有限型态射。则存在真双有理映射 $\pi: \widetilde{X} \to X$ 使得 $f \circ \pi: \widetilde{X} \to S$ 是拟射影的（quasi-projective）。若 $f$  proper，则 $\widetilde{X}$ 可选取为射影的。

*意义*。Chow引理说明任何proper簇都被某个射影簇双有理覆盖，从而将许多问题约化到射影情形。

---

## 4. 重要例子

### 例子 1：proper但非射影

**例 4.1**（Hironaka的例子）。存在光滑proper三维簇不是射影的。构造通过在 $\mathbb{P}^3$ 上沿两条曲线 blow-up，但选择的曲线使得结果不存在丰富除子。

### 例子 2：模空间中的proper性

**例 4.2**。Deligne-Mumford紧化 $\overline{\mathcal{M}}_g$ 是proper的。其proper性通过稳定曲线的**稳定约化定理**证明：任何曲线族在赋值环上的泛 fiber 都可唯一地稳定化为稳定曲线族。

---

## 5. 与已有文档的关联

- [03-概形态射](03-概形态射.md)：proper和射影态射是概形态射的核心子类。
- [15-光滑态射](15-光滑态射.md)：光滑proper态射是研究代数族的理想对象。
- [19-粗糙模空间](19-粗糙模空间.md)：模空间的proper性是存在紧化的关键。

---

## 练习

1. 证明闭浸入是proper的，开浸入一般不是proper的。
2. 验证 $\mathbb{P}^n \to \operatorname{Spec} k$ 满足proper的valuative判据。
3. 说明为什么Chow引理中的"真双有理"条件不可去掉。

---

## 参考文献

1. R. Hartshorne, *Algebraic Geometry*, Springer, 1977. (Ch. II, §4)
2. R. Vakil, *Foundations of Algebraic Geometry*, 2024. (Ch. 10, Ch. 11)
3. W. L. Chow and J. Igusa, "Cohomology theory of varieties over rings", *Proc. Nat. Acad. Sci.*, 1951.
