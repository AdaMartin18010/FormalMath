# 分类Topos与几何点：思维表征

**关联文档**：[10-分类Topos与几何点](./10-分类Topos与几何点.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 分类 Topos | Classifying topos | $\mathbf{Set}[\mathbb{T}]$，几何理论 T 的范畴语义 |
| 几何点 | Geometric point | $f: \mathbf{Set} \to \mathcal{E}$，逆像 $f^*$ |
| 泛模型 | Generic model | $U_T \in \mathbf{Set}[\mathbb{T}]$ |
| 模型对应 | Model correspondence | $M = f^*(U_T)$ |

---

## 🌳 概念树

```text
分类Topos与几何点
├── 分类 Topos Set[T]
│   ├── 几何理论 T 的分类 Topos
│   ├── 泛模型 U_T
│   └── T-模型 ↔ 几何点
├── 几何点 f: Set → E
│   ├── 逆像 f^*: E → Set
│   ├── 正像 f_*: Set → E
│   └── f^* ⊣ f_*，f^* 正合
├── 模型-点对应
│   └── M 是 T-模型 ⟺ M ≅ f^*(U_T)
└── 11-分类定理、逻辑分类
```

---

## 📊 多维矩阵：Topos 类型

| 类型 | 几何点 | 分类理论 | 例子 |
|------|--------|----------|------|
| 分类 Topos | 丰富 | 有 | Set[T] |
| Grothendieck | 有 | 可构造 | Sh(C,J) |
| 初等 | 不一定 | 否 | 一般 Topos |

---

**字数**: 约 490 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
