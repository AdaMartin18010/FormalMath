# 分类定理与Topos分类：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[11-分类定理与Topos分类](./11-分类定理与Topos分类.md) · [11-分类定理与Topos分类-网络对齐与批判性意见报告](./11-分类定理与Topos分类-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日

---

## 一、术语与符号表（中英对照）

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 分类定理 | Classification theorem | 几何理论 $\mathbb{T} \leftrightarrow \mathcal{E}_{\mathbb{T}}$ |
| Topos 分类 | Topos classification | 用几何理论分类 Topos |
| 可表示 | Representable | $\mathbf{Geom}(\mathcal{F}, \mathcal{E}_{\mathbb{T}}) \cong \mathbb{T}\text{-Mod}(\mathcal{F})$ |
| 泛性质 | Universal property | Set[T] 的分类性质 |

---

## 🌳 概念树

```text
分类定理与Topos分类
├── 分类定理（Grothendieck）
│   ├── 几何理论 T → 分类 Topos Set[T]
│   ├── T-模型 ↔ 几何态射 → Set[T]
│   └── 泛模型 U_T 的拉回 = 模型
├── Topos 分类
│   ├── 每个 Grothendieck Topos 可表为 Sh(C,J)
│   ├── 等价于某几何理论的分类 Topos
│   └── 逻辑-几何对应
├── 与 10 的关系
│   └── 10 为特例，11 为一般定理
└── 应用：概形、层、内部逻辑
```

---

## 五、公理–定理–证明树图（核心逻辑链）

```text
[设定] 几何理论 T；Grothendieck Topos E

A1. 分类定理: T 对应分类 Topos Set[T]；T-模型 与 几何态射 到 Set[T] 一一对应.
A2. Topos 分类: 每个 Grothendieck Topos E 等价于某 Set[T']（某几何理论）.

        |--- 定理 T1 (分类): 几何理论 T 到 Set[T]；泛模型 U_T.
        |         (证明: 覆盖、层、08.)
        |
        |--- 定理 T2 (可表示): Geom(F, E_T) 同构 T-Mod(F).
        |         (证明: 泛性质、10.)
        |
        └--- 定理 T3 (可分类): E 同构 Sh(C,J) 同构某 Set[T'].
                  (证明: Giraud、几何理论.)
```

---

## 六、使用说明与复用

- **正文**：概念与证明以 [11-分类定理与Topos分类](./11-分类定理与Topos分类.md) 为准；本页为配套思维表征与检索用。
- **对齐与批判**：见 [11-分类定理与Topos分类-网络对齐与批判性意见报告](./11-分类定理与Topos分类-网络对齐与批判性意见报告.md)。
- **交叉引用**：[08-逻辑分类与模型理论](./08-逻辑分类与模型理论.md)；[10-分类Topos与几何点](./10-分类Topos与几何点.md)；[01-Grothendieck Topos](./01-Grothendieck%20Topos.md)。

**文档状态**：思维表征独立页 v1
**最后更新**：2026年01月31日
