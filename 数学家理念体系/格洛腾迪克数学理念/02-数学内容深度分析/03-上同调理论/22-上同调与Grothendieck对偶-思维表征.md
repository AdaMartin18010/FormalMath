# 上同调与Grothendieck对偶：思维表征

**关联文档**：[22-上同调与Grothendieck对偶](./22-上同调与Grothendieck对偶.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Grothendieck 对偶 | Grothendieck duality | $Rf_* \dashv f^!$，六函子 |
| 例外拉回 | Exceptional inverse image | $f^!$ |
| 推出 | Pushforward | $Rf_*$ |
| 对偶公式 | Duality formula | $\mathrm{Hom}(Rf_* \mathcal{F}, \mathcal{G}) \cong \mathrm{Hom}(\mathcal{F}, f^! \mathcal{G})$ |

---

## 🌳 概念树

```text
上同调与Grothendieck对偶
├── Grothendieck 对偶
│   ├── $f: X \to Y$ 紧合态射
│   ├── $Rf_* \dashv f^!$（导出范畴中）
│   └── 对偶公式
├── 例外拉回 f^!
│   ├── 右伴随于 $Rf_*$
│   ├── 对偶化复形 $\omega_{X/Y}$
│   └── 光滑时：$f^! = f^* \otimes \omega_{X/Y}[n]$
├── 与 Serre 对偶
│   └── Serre = Grothendieck 对 $X \to \mathrm{pt}$
└── 06-导出版上同调、11-上同调与对偶理论、21-上同调与Serre对偶
```

---

## 📊 六函子速查

| 函子 | 符号 | 左/右伴 |
|------|------|---------|
| 拉回 | $f^*$ | $f_*$ |
| 推出 | $Rf_*$ | $f^!$ |
| 例外推 | $f_!$ | $f^!$ |

---

**字数**: 约 500 字 | **数学公式**: 6+ | **最后更新**: 2026-01-31
