# 谱序列与Leray谱序列：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[05-谱序列与Leray谱序列](./05-谱序列与Leray谱序列.md) · [05-谱序列与Leray谱序列-网络对齐与批判性意见报告](./05-谱序列与Leray谱序列-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日
**最后更新**：2026年01月31日

---

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| 谱序列 | Spectral sequence | $E_r^{p,q}$，微分 $d_r$ |
| Leray 谱序列 | Leray spectral sequence | $E_2^{p,q} = H^p(Y, R^q f_*) \Rightarrow H^{p+q}(X)$ |
| 退化 | Degeneration | $E_2 = E_\infty$ |
| 收敛 | Convergence | $E_\infty \Rightarrow H^*$ |

---

## 🌳 概念树

```text
谱序列与Leray谱序列
├── 谱序列基础
│   ├── $E_r^{p,q}$，$d_r: E_r \to E_r$
│   ├── $E_{r+1} = H(E_r, d_r)$
│   └── 收敛到 $H^{p+q}$
├── Leray 谱序列
│   ├── $f: X \to Y$，$\mathcal{F}$ 层
│   ├── $E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F})$
│   └── $\Rightarrow H^{p+q}(X, \mathcal{F})$
├── 退化条件
│   └── $R^q f_*$ 局部常值等
└── 09-Grothendieck谱序列、23-上同调与Leray谱序列应用
```

---

## 📊 多维矩阵：谱序列类型

| 类型 | $E_2$ | 收敛到 | 应用 |
|------|-------|--------|------|
| Leray | $H^p R^q f_*$ | $H^*(X)$ | 纤维化 |
| Grothendieck | $R^p G R^q F$ | $R^{p+q}(GF)$ | 复合函子 |
| Hochschild-Serre | 群上同调 | 扩张 | 伽罗瓦 |

---

**字数**: 约 480 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
