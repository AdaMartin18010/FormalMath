# Grothendieck群理论：思维表征与可复用模板

**文档类型**：思维表征 · 概念矩阵 · 决策树 · 概念树 · 公理–定理树 · 术语表
**关联文档**：[10-Grothendieck群理论](./10-Grothendieck群理论.md) · [10-Grothendieck群理论-网络对齐与批判性意见报告](./10-Grothendieck群理论-网络对齐与批判性意见报告.md)
**创建日期**：2026年01月31日

---

## 一、术语与符号表（中英对照）

| 中文 | 英文 | 符号/备注 |
|------|------|-----------|
| Grothendieck 群 | Grothendieck group | K_0(X)；正合列关系 [E]=[E']+[E''] |
| Picard 群 | Picard group | Pic(X)；线丛同构类 |
| Chern 特征 | Chern character | ch: K_0(X)→H^*(X,ℚ) |
| Riemann-Roch | Riemann-Roch | 见 [05-Riemann-Roch定理](./05-Riemann-Roch定理.md) |

---

## 二、多维概念对比矩阵

### 2.1 K_0 vs Pic vs 高 K 群

| 概念 | 定义 | 与其它篇关系 |
|------|------|--------------|
| K_0(X) | 向量丛 Grothendieck 群，正合列关系 | 07-K理论；05-Riemann-Roch |
| Pic(X) | 线丛同构类；c_1: Pic→H^2 | 05-Riemann-Roch；06-相交理论 |
| Chern 特征 ch | K_0→H^*；GRR | 05-Riemann-Roch定理 |

### 2.2 概念层次（Grothendieck 群 → 应用）

| 概念 | 含义 | 与其它篇关系 |
|------|------|--------------|
| K_0、正合列 | [E]=[E']+[E''] 当 0→E'→E→E''→0 | 07-K理论 |
| GRR | ch 与 Todd、Riemann-Roch | 05-Riemann-Roch定理 |

---

## 三、决策树图（何时用 Grothendieck 群理论）

```text
                    [目标：向量丛/线丛的群、不变量、GRR]
                                    |
        +----------------------------+----------------------------+
        |                            |                            |
  [向量丛的等价类]              [线丛 Pic、c_1]              [Chern、GRR]
        |                            |                            |
   K_0(X)、正合列关系            Pic(X)、c_1: Pic→H^2         ch、Todd、05-GRR
   高 K 群见 07                 与 05、06 联系                 见 05-Riemann-Roch
        |                            |                            |
        +----------------------------+----------------------------+
                                    |
                    [工具：05-Riemann-Roch、07-K理论、06-相交理论]
```

---

## 四、概念树图（Grothendieck 群概念依赖）

```text
Grothendieck 群理论 (K_0, Pic, Chern)
├── K_0(X)：向量丛的 Grothendieck 群，正合列关系
├── Pic(X)：线丛；Pic(X) 与 K_0、c_1 联系
├── Chern 特征 ch: K_0→H^*；GRR（见 05）
└── 高 K 群（见 07-K理论）
```

---

## 五、公理–定理–证明树图（核心逻辑链）

```text
[设定] X 概形，向量丛/拟凝聚层范畴；正合列关系。

A1. K_0(X) 为向量丛的 Grothendieck 群：生成元 [E]，关系 [E]=[E']+[E''] 当 0→E'→E→E''→0 正合。
A2. Pic(X) 为线丛同构类；c_1: Pic(X)→H^2(X,Z)（若适用）；Chern 特征 ch: K_0(X)→H^*(X,Q)。

        |--- 定理 T1 (GRR): ch(E)=Todd(X)∩(某种类)；见 05-Riemann-Roch定理.
        |         (证明: 05-Riemann-Roch.)
        |
        |--- 定理 T2 (K_0 与 Pic): 线丛 L 对应 [L]∈K_0；c_1(L) 与 ch 联系.
        |         (证明: 标准.)
        |
        └--- 定理 T3 (高 K 群): K_i、i>0 见 07-K理论；与 K_0 构成环.
                  (证明: 07-K理论.)
```

---

## 六、使用说明与复用

- **正文**：以 [10-Grothendieck群理论](./10-Grothendieck群理论.md) 为准。
- **对齐与批判**：见 [10-Grothendieck群理论-网络对齐与批判性意见报告](./10-Grothendieck群理论-网络对齐与批判性意见报告.md)。
- **交叉引用**：[05-Riemann-Roch定理](./05-Riemann-Roch定理.md)；[07-K理论](./07-K理论.md)；[06-相交理论](./06-相交理论.md)。

**文档状态**：思维表征独立页 v1
**最后更新**：2026年01月31日
