# 层的范畴与Grothendieck拓扑：思维表征

**关联文档**：[05-层的范畴与Grothendieck拓扑](./05-层的范畴与Grothendieck拓扑.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 层范畴 | Sheaf category | $\mathrm{Sh}(C,J)$ |
| Grothendieck 拓扑 | Grothendieck topology | 覆盖族 $J(U)$，筛 |
| 预层 | Presheaf | $C^{\mathrm{op}} \to \mathbf{Set}$ |
| 层化 | Sheafification | $a: P \mapsto P^+$，$a^2 = a$ |
| 筛 | Sieve | $S \subseteq \mathrm{Hom}(-, U)$ |

---

## 🌳 概念树

```text
层的范畴与Grothendieck拓扑
├── Grothendieck 拓扑 J
│   ├── 覆盖族 J(U) ⊆ {筛}
│   ├── 公理：恒等、限制、传递
│   └── 替代点集拓扑的"开集"
├── 层范畴 Sh(C,J)
│   ├── 对覆盖满足粘合条件的预层
│   ├── 层化 a: PSh → Sh 为左伴随
│   └── Grothendieck Topos 的构造
├── 层条件
│   └── F(U) → ∏F(U_i) ⇉ ∏F(U_i∩U_j) 等化
└── 01-Grothendieck Topos、SGA 4
```

---

## 📊 多维矩阵：拓扑类型

| 拓扑 | 覆盖定义 | 层范畴 | 应用 |
|------|----------|--------|------|
| 平凡 | 恒等筛 | PSh(C) | 预层 |
| Zariski | 开覆盖 | 概形上的 Zariski 层 | 代数几何 |
| étale | étale 覆盖 | 平展层 | 韦伊猜想 |
| fppf | 平坦有限型 | fppf 层 | 群概形 |

---

**字数**: 约 450 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
