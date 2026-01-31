# Riemann-Roch定理：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[05-Riemann-Roch定理](./05-Riemann-Roch定理.md) · [05-Riemann-Roch定理-网络对齐与批判性意见报告](./05-Riemann-Roch定理-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日

---

## 一、术语与符号表（中英对照）

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Riemann-Roch 定理 | Riemann-Roch theorem | 经典：χ(O(D)) = deg(D) + 1 - g |
| Hirzebruch-Riemann-Roch | Hirzebruch-Riemann-Roch (HRR) | χ(E) = ∫_X ch(E)·td(X) |
| Grothendieck-Riemann-Roch | Grothendieck-Riemann-Roch (GRR) | ch(f_* α)·td(TY) = f_*(ch(α)·td(TX)) |
| Chern 特征 | Chern character | ch: K_0 → H^*(−) |
| Todd 类 | Todd class | td(TX) 或 td(虚切丛) |
| 推前 | pushforward | f_*: K_0(X) → K_0(Y)，proper f |
| SGA 6 | SGA 6 | Berthelot–Grothendieck–Illusie, LNM 225 (1971) |

---

## 二、多维概念对比矩阵

### 2.1 Riemann-Roch 定理层次对比

| 定理 | 对象 | 公式 | 典型文献 |
|------|------|------|----------|
| 经典 R–R | 曲线 C，除子 D | χ(O(D)) = deg(D) + 1 - g | Riemann, Roch |
| HRR | 光滑射影 X，向量丛 E | χ(E) = ∫_X ch(E)·td(X) | Hirzebruch 1954 |
| GRR | proper f: X→Y，α∈K_0(X) | ch(f_* α)·td(TY) = f_*(ch(α)·td(TX)) | SGA 6 (1971) |

### 2.2 概念层次（R–R → 应用）

| 概念 | 含义 | 与 R–R 关系 |
|------|------|-------------|
| ch, td | Chern 特征、Todd 类 | GRR/HRR 核心 |
| 相交理论 | 相交积、陈类 | SGA 6；见 [06-相交理论](./06-相交理论.md) |
| K 理论 K_0 | Grothendieck 群 | SGA 6；见 [07-K理论](./07-K理论.md) |

---

## 三、决策树图（何时用何种 R–R）

```text
                    [问题：Euler 特征 / 指标 / 推前]
                                    |
            +-----------------------+-----------------------+
            |                       |                       |
      [曲线 + 除子/线丛]       [光滑射影 + 向量丛]     [proper 态射 + K_0]
            |                       |                       |
      经典 Riemann-Roch          Hirzebruch-Riemann-Roch   Grothendieck-Riemann-Roch
      χ(O(D)) = deg(D)+1−g       χ(E) = ∫ ch·td            ch(f_* α)·td(Y) = f_*(ch(α)·td(X))
            |                       |                       |
            +-----------------------+-----------------------+
                                    |
                    [工具：相交理论、K 理论；SGA 6]
```

---

## 四、概念树图（Riemann-Roch 概念依赖）

```text
Riemann-Roch 定理 (Riemann-Roch Theorems)
├── 经典（曲线）
│   ├── χ(C, O(D)) = deg(D) + 1 - g(C)
│   └── Serre 对偶、亏格
│
├── Hirzebruch-Riemann-Roch (1954)
│   ├── 光滑射影 X，向量丛 E
│   ├── χ(X,E) = ∫_X ch(E)·td(X)
│   └── ch, td 定义
│
├── Grothendieck-Riemann-Roch (SGA 6, 1971)
│   ├── proper f: X → Y
│   ├── ch(f_* α)·td(TY) = f_*(ch(α)·td(TX))
│   ├── f_*: K_0(X) → K_0(Y)
│   └── 非光滑时虚切丛
│
├── 相交理论（SGA 6）
│   └── 见 06-相交理论
│
├── K 理论（K_0, 高 K 群）
│   └── 见 07-K理论
│
└── 应用
    ├── 分类、枚举
    └── Bezout、相交数
```

---

## 五、公理–定理–证明树图（核心逻辑链）

```text
[设定] 曲线 C / 光滑射影 X / proper f: X→Y

A1. 经典 R–R: χ(C,O(D)) = deg(D) + 1 - g.
A2. HRR: χ(X,E) = ∫_X ch(E)·td(TX)，X 光滑射影.
A3. GRR: f proper，则 ch(f_* α)·td(TY) = f_*(ch(α)·td(TX)).

        |--- 定理 T1 (经典): 曲线情形，Serre 对偶可推出.
        |
        |--- 定理 T2 (HRR): Hirzebruch 1954；陈类与 Todd 类.
        |
        |--- 定理 T3 (GRR): SGA 6；K_0 推前与 ch、td 相容.
        |
        └--- 定理 T4 (应用): 相交数、Bezout、分类；见相交理论、K 理论.
```

---

## 六、使用说明与复用

- **正文**：概念与证明以 [05-Riemann-Roch定理](./05-Riemann-Roch定理.md) 为准；本页为配套思维表征与检索用。
- **对齐与批判**：见 [05-Riemann-Roch定理-网络对齐与批判性意见报告](./05-Riemann-Roch定理-网络对齐与批判性意见报告.md)。
- **交叉引用**：[06-相交理论](./06-相交理论.md)；[07-K理论](./07-K理论.md)。

**文档状态**：思维表征独立页 v1
**最后更新**：2026年01月31日
