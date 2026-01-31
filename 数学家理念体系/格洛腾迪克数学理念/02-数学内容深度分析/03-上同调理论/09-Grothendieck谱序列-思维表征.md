# Grothendieck谱序列：思维表征

**关联文档**：[09-Grothendieck谱序列](./09-Grothendieck谱序列.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Grothendieck 谱序列 | Grothendieck spectral sequence | 复合函子 $G \circ F$ |
| $E_2$ 页 | $E_2$ page | $E_2^{p,q} = R^p G(R^q F(-))$ |
| Leray-Grothendieck | Leray-Grothendieck | $R^p f_* R^q g_* \Rightarrow R^{p+q}(fg)_*$ |
| 退化条件 | Degeneration | $F$  sends 内射到 $G$-非循环 |

---

## 🌳 概念树

```text
Grothendieck谱序列
├── 复合函子 G∘F
│   ├── $F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$
│   ├── $E_2^{p,q} = R^p G(R^q F(A))$
│   └── $\Rightarrow R^{p+q}(GF)(A)$
├── Leray-Grothendieck 特例
│   ├── $f: X \to Y$，$g: Y \to Z$
│   ├── $E_2^{p,q} = R^p g_* R^q f_* \mathcal{F}$
│   └── $\Rightarrow R^{p+q}(gf)_* \mathcal{F}$
├── 退化条件
│   └── $R^q F(I)$ 为 $G$-非循环
└── 05-谱序列与Leray谱序列、23-上同调与Leray谱序列应用
```

---

## 📊 多维矩阵：谱序列来源

| 来源 | 复合 | $E_2$ |
|------|------|-------|
| Leray | $f: X \to Y$ | $H^p(Y, R^q f_*)$ |
| Grothendieck | $G \circ F$ | $R^p G R^q F$ |
| 滤过 | 滤过复形 | $H^{p+q}(\mathrm{gr})$ |

---

**字数**: 约 510 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
