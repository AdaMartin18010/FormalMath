# 连续范畴与Locales：思维表征

**关联文档**：[07-连续范畴与Locales](./07-连续范畴与Locales.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 连续范畴 | Continuous category | 定向完备、way-below $\ll$ |
| locale | Locale | 无点拓扑空间， frame $L$ |
| 点化 | Pointification | $\mathrm{pt}(L)$ 恢复点 |
| 定向完备 | Directed complete | 定向集有上确界 |

---

## 🌳 概念树

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

## 📊 多维矩阵：空间 vs Locale

| 类型 | 点 | 开集 | 典型例子 |
|------|----|------|----------|
| 拓扑空间 | 有 | 子集族 | $\mathbb{R}^n$ |
| Locale | 无（可恢复） | frame | 谱 $\mathrm{Spec}(A)$ |
|  sober 空间 | 与 pt(L) 对应 | 同左 | 概形 |

---

**字数**: 约 480 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
