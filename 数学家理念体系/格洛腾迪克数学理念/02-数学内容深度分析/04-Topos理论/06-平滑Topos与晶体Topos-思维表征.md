# 平滑Topos与晶体Topos：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[06-平滑Topos与晶体Topos](./06-平滑Topos与晶体Topos.md) · [06-平滑Topos与晶体Topos-网络对齐与批判性意见报告](./06-平滑Topos与晶体Topos-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日

---

## 一、术语与符号表（中英对照）

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 平滑 topos | Smooth topos | 无穷小增厚的几何 |
| 晶体 topos | Crystalline topos | $(X/S)_{\mathrm{cris}}$ |
| 晶体上同调 | Crystalline cohomology | $H^n_{\mathrm{cris}}$ |
| 无穷小 | Infinitesimal | 幂零理想、形式邻域 |
| 增厚 | Thickening | $T \twoheadrightarrow S$ 幂零 |

---

## 二、多维概念对比矩阵

### 2.1 上同调类型对比

| 类型 | 定义域 | 适用特征 | 应用 |
|------|--------|----------|------|
| de Rham | 光滑簇 | char=0 | Hodge 理论 |
| 晶体 | 概形/S | 任意 | 韦伊猜想、p 进 |
| étale | 概形 | 任意 | $\ell \neq p$ |
| Hodge | 复簇 | C | 混合 Hodge 结构 |

### 2.2 概念层次（平滑/晶体 topos 到应用）

| 概念 | 含义 | 与本文关系 |
|------|------|------------|
| 平滑 topos（SGA 7） | 无穷小增厚 $T \twoheadrightarrow S$，形式邻域 | 微分形式框架 |
| 晶体 topos $(X/S)_{\mathrm{cris}}$ | 分歧除子、特征 p | 晶体上同调 $H^n_{\mathrm{cris}}$ |
| 与 de Rham | 特征 0 时晶体与 de Rham 一致 | 见 03-上同调理论 |

---

## 三、决策树图（何时用平滑/晶体 Topos）

```text
                    [研究目标：无穷小、特征 p、p 进？]
                                |
            +-------------------+-------------------+
            |                   |                   |
      [无穷小增厚]          [晶体 (X/S)_cris]    [上同调 H^n_cris]
      平滑 topos            分歧、char p        韦伊、p 进
            |                   |                   |
            +-------------------+-------------------+
                                |
                    [工具：SGA 7、03-上同调/晶体、de Rham]
```

---

## 四、概念树图（平滑Topos与晶体Topos概念依赖）

```text
平滑Topos与晶体Topos
├── 平滑 topos（SGA 7）
│   ├── 无穷小增厚 T 到 S
│   ├── 形式邻域、幂零理想
│   └── 微分形式的自然框架
├── 晶体 topos
│   ├── (X/S)_cris
│   ├── 分歧除子、特征 p
│   └── 晶体上同调 H^n_cris
├── 与 de Rham 关系
│   └── 特征 0：晶体 与 de Rham 一致
└── 姊妹：03-上同调理论/04-étale
```

---

## 五、公理–定理–证明树图（核心逻辑链）

```text
[设定] 概形 X/S；S 特征 p 或 0；无穷小增厚 T 到 S

A1. 平滑 topos: 对象为增厚 T 到 S；覆盖由 morphism 定义（SGA 7）.
A2. 晶体 topos: (X/S)_cris 由 X 在 S 上的无穷小邻域、晶体层定义.

        |--- 定理 T1 (晶体上同调): H^n_cris 为 Weil 上同调；有限性、对偶.
        |         (证明: Berthelot、Grothendieck.)
        |
        |--- 定理 T2 (与 de Rham): char 0 时 H_cris 与 H_dR 一致.
        |         (证明: 比较定理.)
        |
        └--- 定理 T3 (韦伊猜想): p 进部分由晶体上同调实现；见 03-上同调.
                  (证明: 晶体、étale 比较.)
```

---

## 六、使用说明与复用

- **正文**：概念与证明以 [06-平滑Topos与晶体Topos](./06-平滑Topos与晶体Topos.md) 为准；本页为配套思维表征与检索用。
- **对齐与批判**：见 [06-平滑Topos与晶体Topos-网络对齐与批判性意见报告](./06-平滑Topos与晶体Topos-网络对齐与批判性意见报告.md)。
- **交叉引用**：[04-étale Topos与平展上同调](./04-étale%20Topos与平展上同调.md)；[05-层的范畴与Grothendieck拓扑](./05-层的范畴与Grothendieck拓扑.md)；03-上同调理论/晶体、de Rham。

**文档状态**：思维表征独立页 v1
**最后更新**：2026年01月31日
