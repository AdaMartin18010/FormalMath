# 上同调与Ext函子：思维表征

**关联文档**：[19-上同调与Ext函子](./19-上同调与Ext函子.md) · 同名网络对齐报告

---

## 📋 术语表

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Ext 函子 | Ext functor | $\mathrm{Ext}^i(\mathcal{F}, \mathcal{G})$ |
| 同调代数 | Homological algebra | 导出范畴 $\mathbf{D}(X)$ |
| 导出 Hom | Derived Hom | $\mathbf{R}\mathrm{Hom}(\mathcal{F}, \mathcal{G})$ |
| Yoneda 扩张 | Yoneda extension | $\mathrm{Ext}^1$ = 扩张等价类 |

---

## 🌳 概念树

```text
上同调与Ext函子
├── Ext^i 定义
│   ├── $\mathrm{Ext}^i = R^i \mathrm{Hom}$
│   ├── 右导出函子
│   └── 射影/内射分解
├── 同调代数
│   ├── 导出范畴 D(X)
│   ├── 三角范畴、t-结构
│   └── 谱序列
├── Yoneda 解释
│   └── Ext^1(A,B) = 扩张 0→B→E→A→0 的等价类
└── 18-上同调与张量积、30-上同调与Ext函子应用
```

---

## 📊 多维矩阵：Ext 应用

| Ext^i | 几何意义 | 代数意义 |
|-------|----------|----------|
| Ext^0 | Hom | 同态 |
| Ext^1 | 扩张 | 扩张群 |
| Ext^i | 高阶扩张 |  obstructions |

---

**字数**: 约 500 字 | **数学公式**: 6+ | **最后更新**: 2026-01-31
