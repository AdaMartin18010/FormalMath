---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0C6B - 代数叠的商构造

## 1. 基本概念与定义

### 1.1 商叠的定义

**定义（商叠）：** 设 $G$ 为 $S$-群概形，作用于 $S$-概形 $X$。**商叠** $[X/G]$ 定义为：

- **对象：** 三元组 $(T, P, \varphi)$，其中：
  - $T$ 是 $S$-概形
  - $P \to T$ 是 $G$-主丛（principal $G$-bundle）
  - $\varphi: P \to X$ 是 $G$-等变映射

- **态射：** 与 $G$-作用和 $\varphi$ 相容的 $G$-主丛同构

### 1.2 特殊情形

**全局商（Global Quotient）：** $[X/G]$ 是全局商叠。

**局部商：** 叠 $\mathcal{X}$ 称为**局部商叠**，如果对每个点都存在étale邻域 $U$ 使得 $\mathcal{X}|_U \cong [V/G]$。

**重要事实：** 所有DM叠都是局部商叠（Luna slice theorem）。

---

## 2. 数学背景与动机

### 2.1 GIT（几何不变量理论）背景

**问题：** 群作用 $G \curvearrowright X$ 的商空间 $X/G$ 何时"好"？

**GIT答案：** 对于线性化作用，存在开集 $X^{ss} \subseteq X$（半稳定点），使得 categorical quotient $X^{ss}/\!/G$ 存在。

**商叠的优势：**

- 不需要稳定性条件
- 保持所有轨道信息
- 与GIT商的关系：$[X^{ss}/G] \to X^{ss}/\!/G$ 是粗模空间映射

### 2.2 历史发展

**Mumford (1965):** 几何不变量理论

**Deligne-Mumford (1969):** 模叠 $\mathcal{M}_g$ 作为商叠的视角

**现代发展：** 导出商、无限维群作用的商

---

## 3. 形式化性质与定理

### 3.1 商叠的基本性质

**定理：** $[X/G]$ 是Artin叠。当 $G$ 有限时，它是DM叠。

**定理（商叠的模解释）：** $[X/G](T) = \{(P, \varphi)\}/\cong$，其中：

- $P \to T$ 是 $G$-torsor
- $\varphi: P \to X$ 是 $G$-等变

**定理（与GIT商的比较）：** 对于仿射 $X$ 和约化群 $G$：$$[X/G] \cong [X^{ss}/G] \cup [X^{unstable}/G]$$

其中 $X^{ss}/\!/G$ 是 $[X^{ss}/G]$ 的粗模空间。

### 3.2 商叠的映射性质

**定理（万有性质）：** 对于任意叠 $\mathcal{Y}$：$$\text{Hom}([X/G], \mathcal{Y}) = \{(F, \alpha)\}$$

其中 $F: X \to \mathcal{Y}$ 且 $\alpha: F \circ p_1 \xrightarrow{\sim} F \circ p_2$ 是 $G$-作用上的下降数据。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Quotients of Groupoids (Chapter 79)
- **前置Tags：**
  - Tag 0C5Z (Artin叠)
  - Tag 0C6A (DM叠)
  - Tag 044Q (群概形作用)

### 4.2 依赖关系

```
Tag 0C6B (商叠)
├── Tag 0C5Z (Artin叠)
├── Tag 0C6A (DM叠)
├── Tag 044Q (群作用)
├── Tag 0F1C (等变D-模)
└── Tag 0G2A (形变理论)
```

---

## 5. 应用与例子

### 5.1 经典例子

**例1：分类叠 $BG$**

$$BG = [\text{pt}/G]$$

- 对象：$T$ 上的 $G$-torsor
- 这是最简单的非平凡叠

**例2：加权射影空间**

$$\mathbb{P}(w_0, ..., w_n) = [\mathbb{A}^{n+1} \setminus \{0\}/\mathbb{G}_m]$$

其中 $\mathbb{G}_m$ 作用权重为 $(w_0, ..., w_n)$。

**例3：Hassett模空间**

加权稳定曲线的模空间可以表示为商叠。

### 5.2 在数学中的应用

**(1) 枚举几何**

$
|n$ 次平面曲线的模空间：$|\mathbb{P}^{\binom{n+2}{2}-1}/PGL_3]$

**(2) 规范理论（Gauge Theory）**

瞬子模空间：$\mathcal{M}_{inst} = [\mathcal{A}^{asd}/\mathcal{G}]$

其中 $\mathcal{A}^{asd}$ 是反自对偶联络空间，$\mathcal{G}$ 是规范群。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
商叠 (0C6B)
│
├── GIT商 ──→ 粗模空间
├── 等变上同调 ──→ $H^*_G(X) = H^*([X/G])$
├── 等变K-理论 ──→ $K_G(X) = K([X/G])$
├── 扭曲层（Twisted Sheaves） ──→ 叠上的层
└── 导出商 ──→ $[X/G]^{der}$
```

### 6.2 等变理论

| 理论 | 叠解释 | 公式 |
|------|--------|------|
| 等变上同调 | 商叠上同调 | $H^*_G(X) = H^*([X/G])$ |
| 等变K-理论 | 叠K-理论 | $K_G(X) = K([X/G])$ |
| 等变导出范畴 | 叠导出范畴 | $D^b_G(X) = D^b([X/G])$ |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0C6B
- **章节：** Quotients of Groupoids

### 7.2 核心教材

1. **Mumford, Fogarty & Kirwan** *Geometric Invariant Theory*
   - GIT的经典参考书

2. **Dolgachev, I.** *Lectures on Invariant Theory*
   - 群作用与商的几何

3. **Romagny, M.** "Group actions on stacks and applications"

### 7.3 研究论文

- **Kresch, A.** "Cycle groups for Artin stacks"
- **Edidin & Graham** "Equivariant intersection theory"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现方向

```lean
-- 商叠的构造
noncomputable def quotientStack {G : GroupScheme S}
    (X : SchemeOver S) [G.ActionOn X] : ArtinStack S where
  obj T := {P : GTorsor G T // G.EquivariantMap P X}
  map := sorry
  -- 验证Stack条件
  -- 构造光滑覆盖 X → [X/G]

-- 等变上同调 = 商叠上同调
def equivariantCohomology (G : GroupScheme S) (X : SchemeOver S)
    [G.ActionOn X] (n : ℕ) : Type :=
  H^n([X/G], ℤ)
```

### 8.2 形式化挑战

1. **$G$-torsor的范畴化：** 需要主丛的合适定义
2. **等变映射：** 与群作用相容的映射
3. **GIT商的比较：** 需要稳定性理论的形式化

---

## 总结

Tag 0C6B (代数叠的商构造) 将GIT与叠理论联系起来，提供了研究群作用几何的统一框架。商叠不仅是具体叠的重要来源（如加权射影空间、模叠），也是等变上同调、等变K-理论的自然家园。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第86个*
