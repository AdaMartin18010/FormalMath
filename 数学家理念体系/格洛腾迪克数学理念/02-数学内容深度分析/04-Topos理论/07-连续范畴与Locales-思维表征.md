# 连续范畴与Locales：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[07-连续范畴与Locales](./07-连续范畴与Locales.md) · [07-连续范畴与Locales-网络对齐与批判性意见报告](./07-连续范畴与Locales-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日

---

## 一、术语与符号表（中英对照）

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 连续范畴 | Continuous category | 定向完备、way-below $\ll$ |
| locale | Locale | 无点拓扑空间， frame $L$ |
| 点化 | Pointification | $\mathrm{pt}(L)$ 恢复点 |
| 定向完备 | Directed complete | 定向集有上确界 |

---

## 二、多维概念对比矩阵

### 2.1 空间 vs Locale 对比

| 类型 | 点 | 开集 | 典型例子 |
|------|----|------|----------|
| 拓扑空间 | 有 | 子集族 | R^n |
| Locale | 无（可恢复） | frame | 谱 Spec(A) |
| sober 空间 | 与 pt(L) 对应 | 同左 | 概形 |

### 2.2 概念层次（连续范畴与 Locale）

| 概念 | 含义 | 与本文关系 |
|------|------|------------|
| 连续范畴 | way-below a 远小于 b，定向完备 | Lawson、Scott 拓扑 |
| Locale | frame L，开集格无点化 | 点 = Hom(L, 2) |
| 点化 | pt: Locale 到 Top 的右伴随 | Johnstone、无点拓扑 |

---

## 三、决策树图（何时用连续范畴/Locale）

```text
                    [研究目标：无点拓扑、格论、定向完备？]
                                |
            +-------------------+-------------------+
            |                   |                   |
      [way-below]           [Locale/frame]      [点化 pt(L)]
      连续范畴、定向完备     无点拓扑、开集格    恢复点、sober
            |                   |                   |
            +-------------------+-------------------+
                                |
                    [工具：Johnstone、nLab、pointless topology]
```

---

## 四、概念树图（连续范畴与Locales概念依赖）

```text
连续范畴与Locales
├── 连续范畴
│   ├── way-below 关系 $a \ll b$
│   ├── 定向完备偏序集
│   └──  Lawson、Scott 拓扑
├── Locale（无点拓扑）
│   ├── frame：有有限交、任意并的格
│   ├── 开集格的无点化
│   └── 点 = frame 的同态 $\mathrm{Hom}(L, 2)$
├── 点化与空间
│   └── pt: Locale → Top 的右伴随
└── Johnstone、nLab、 pointless topology
```

---

## 五、公理–定理–证明树图（核心逻辑链）

```text
[设定] 偏序集 P 或格 L；Locale = frame

A1. 连续范畴: 定向完备，且 任意 x = sup { a : a 远小于 x }；way-below 传递.
A2. Locale: L 为 frame；态射为保有限交与任意并的映射；点 pt(L) = Hom(L,2).

        |--- 定理 T1 (点化伴随): Omega: Top 到 Locale 左伴随于 pt；pt(L) 为 sober.
        |         (证明: 无点拓扑.)
        |
        |--- 定理 T2 (谱): Spec(A) 可视为 Locale；概形 sober.
        |         (证明: 代数几何.)
        |
        └--- 定理 T3 (连续格): 连续格与 Lawson 拓扑见 domain theory.
                  (证明: 域论、Scott 拓扑.)
```

---

## 六、使用说明与复用

- **正文**：概念与证明以 [07-连续范畴与Locales](./07-连续范畴与Locales.md) 为准；本页为配套思维表征与检索用。
- **对齐与批判**：见 [07-连续范畴与Locales-网络对齐与批判性意见报告](./07-连续范畴与Locales-网络对齐与批判性意见报告.md)。
- **交叉引用**：无点拓扑（pointless topology）；概形 sober 空间；domain theory。

**文档状态**：思维表征独立页 v1
**最后更新**：2026年01月31日
