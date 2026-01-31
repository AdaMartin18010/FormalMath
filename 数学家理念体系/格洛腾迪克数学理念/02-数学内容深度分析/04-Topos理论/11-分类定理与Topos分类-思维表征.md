# 分类定理与Topos分类：思维表征

**关联文档**：[11-分类定理与Topos分类](./11-分类定理与Topos分类.md) · 同名网络对齐报告

---

## 📋 术语表

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

## 📊 思维导图

```text
    分类定理
        │
    ┌───┴───┐
    │       │
  T → Set[T]  E ≃ Set[T']
 几何理论    Topos 可分类
    │       │
    └───┬───┘
        │
   模型-点-几何态射 一一对应
```

---

**字数**: 约 480 字 | **数学公式**: 4+ | **最后更新**: 2026-01-31
