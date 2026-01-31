# 上同调与Leray谱序列应用：思维表征

**关联文档**：[23-上同调与Leray谱序列应用](./23-上同调与Leray谱序列应用.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Leray 谱序列 | Leray spectral sequence | $E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$ |
| 退化 | Degeneration | $E_2 = E_\infty$（条件） |
| 纤维化 | Fibration | $f: X \to Y$，纤维 $X_y$ |
| 推前 | Pushforward | $Rf_* \mathcal{F}$ |

---

## 🌳 概念树

```text
上同调与Leray谱序列应用
├── Leray 谱序列
│   ├── $E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F})$
│   ├── $E_\infty \Rightarrow H^{p+q}(X, \mathcal{F})$
│   └── 收敛、滤波
├── 退化条件
│   ├── $R^q f_* \mathcal{F}$ 局部常值
│   ├── 平滑纤维化
│   └── 紧支撑变体
├── 应用
│   ├── 纤维化上同调
│   ├── 基变换
│   └── 比较定理
└── 05-谱序列与Leray谱序列、09-Grothendieck谱序列
```

---

## 📊 多维矩阵：谱序列类型

| 类型 | $E_2$ 页 | 收敛到 | 应用 |
|------|----------|--------|------|
| Leray | $H^p(Y, R^q f_*)$ | $H^*(X)$ | 纤维化 |
| Grothendieck | $R^p f_* R^q g_*$ | $R^{p+q}(fg)_*$ | 复合 |
| Hochschild-Serre | 群上同调 | 扩张 | 伽罗瓦 |

---

**字数**: 约 520 字 | **数学公式**: 5+ | **最后更新**: 2026-01-31
