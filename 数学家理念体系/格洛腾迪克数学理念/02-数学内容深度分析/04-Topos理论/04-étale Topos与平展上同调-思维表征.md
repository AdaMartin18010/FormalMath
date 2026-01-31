# étale Topos与平展上同调：思维表征

**关联文档**：[04-étale Topos与平展上同调](./04-étale%20Topos与平展上同调.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| étale topos | Étale topos | $X_{\mathrm{\acute{e}t}}$ |
| 平展上同调 | Étale cohomology | $H^i_{\mathrm{\acute{e}t}}(X, \mathcal{F})$ |
| étale 覆盖 | Étale covering | 局部有限型、非分歧、平坦 |
| 韦伊猜想 | Weil conjectures | 有理点计数、$\zeta$ 函数 |

---

## 🌳 概念树

```text
étale Topos与平展上同调
├── étale topos X_ét
│   ├── 概形 X 上的 étale 层范畴
│   ├── étale 覆盖族定义的 Grothendieck 拓扑
│   └── 替代 Zariski（对特征 p 不足）
├── 平展上同调
│   ├── H^i_ét(X,F)，F 为 Abel 层
│   ├── 韦伊猜想的证明框架
│   └── ℓ-进上同调 H^i(X, ℚ_ℓ)
├── 与 SGA 4 关系
│   └── 平展上同调的理论基础
└── 姊妹：03-上同调理论/02-étale上同调
```

---

## 📊 多维矩阵：上同调类型

| 类型 | 拓扑 | 适用 | 应用 |
|------|------|------|------|
| Zariski | 开覆盖 | 一般概形 | 凝聚层 |
| étale | étale 覆盖 | 任意特征 | 韦伊猜想 |
| 晶体 | 无穷小增厚 | char p | p 进 |
| de Rham | 微分形式 | char 0 | Hodge |

---

## 🗺️ 思维导图

```text
    étale Topos X_ét
            │
    ┌───────┼───────┐
    │       │       │
  层范畴   覆盖    上同调
  Sh(X_ét) étale   H^i_ét
    │       │       │
    └───────┴───────┘
            │
    韦伊猜想、ℓ-进、Poincaré 对偶
```

---

**字数**: 约 520 字 | **数学公式**: 4+ | **最后更新**: 2026-01-31
