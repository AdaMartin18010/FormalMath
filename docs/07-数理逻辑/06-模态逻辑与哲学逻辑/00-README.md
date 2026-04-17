---
title: "模态逻辑与哲学逻辑 (Modal and Philosophical Logic)"
msc_primary: "03B45"
msc_secondary: ['03B42', '03B44', '03B48', '03B60']
processed_at: '2026-04-05'
references:
  textbooks:
    - id: enderton_logic
      type: textbook
      title: A Mathematical Introduction to Logic
      authors:
      - Herbert B. Enderton
      publisher: Academic Press
      edition: 2nd
      year: 2001
      isbn: 978-0122384523
      msc: 03-01
      chapters: []
      url: ~
    - id: mendelson_logic
      type: textbook
      title: Introduction to Mathematical Logic
      authors:
      - Elliott Mendelson
      publisher: Chapman and Hall/CRC
      edition: 6th
      year: 2015
      isbn: 978-1482237725
      msc: 03-01
      chapters: []
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 模态逻辑与哲学逻辑 (Modal and Philosophical Logic)

**最后更新**: 2026年4月5日
**MSC分类**: 03B45 (模态逻辑), 03B42 (认知逻辑), 03B44 (时态逻辑)

---

## 1. 引言

模态逻辑研究必然性、可能性、知识、信念、义务等模态概念的形式化推理。从Aristotle的模态三段论到Kripke的可能世界语义，从Lewis的模态实在论到Hintikka的知识模型，模态逻辑已成为分析哲学、理论计算机科学、语言学和人工智能的核心工具。

---

## 2. 基本模态逻辑

### 2.1 语法与语义

**定义 2.1** (模态语言): 模态语言由以下文法生成：
$$\varphi ::= p \mid \neg\varphi \mid \varphi \land \psi \mid \Box\varphi \mid \Diamond\varphi$$
其中 $\Box$ 读作"必然"，$\Diamond$ 读作"可能"。

**定义 2.2** (Kripke模型): Kripke模型是三元组 $\mathcal{M} = (W, R, V)$，其中：

- $W$: 可能世界非空集
- $R \subseteq W \times W$: 可达关系
- $V: \text{Prop} \to \mathcal{P}(W)$: 赋值函数

**定义 2.3** (满足关系): $\mathcal{M}, w \models \varphi$ 定义为：

- $\mathcal{M}, w \models p$ iff $w \in V(p)$
- $\mathcal{M}, w \models \Box\varphi$ iff $\forall v (wRv \Rightarrow \mathcal{M}, v \models \varphi)$
- $\mathcal{M}, w \models \Diamond\varphi$ iff $\exists v (wRv \land \mathcal{M}, v \models \varphi)$

**定理 2.1** (对偶性): $\Diamond\varphi \leftrightarrow \neg\Box\neg\varphi$ 在所有Kripke模型中有效。

---

### 2.2 公理系统

**定义 2.4** (系统K): 最小正规模态逻辑K包含：

- 命题重言式的所有代入实例
- **K公理**: $\Box(p \to q) \to (\Box p \to \Box q)$
- **必然化规则 (Nec)**: 从 $\varphi$ 推出 $\Box\varphi$
- **假言推理 (MP)**: 从 $\varphi$ 和 $\varphi \to \psi$ 推出 $\psi$

**常见模态公式及其框架条件**:

| 公理 | 名称 | 框架条件 |
|------|------|----------|
| $\Box p \to p$ | T (自反性) | $R$ 自反 |
| $\Box p \to \Box\Box p$ | 4 (传递性) | $R$ 传递 |
| $p \to \Box\Diamond p$ | B (对称性) | $R$ 对称 |
| $\Diamond p \to \Box\Diamond p$ | 5 (欧几里得性) | $R$ 欧几里得 |
| $\Box p \to \Box\Box p$ | S4 | $R$ 预序 |
| $\Box p \to p$, $p \to \Box\Diamond p$ | S5 | $R$ 等价关系 |

**定理 2.2** (对应理论): 公式 $\varphi$ 在框架类 $\mathcal{F}$ 上有效当且仅当 $\varphi$ 对应一阶条件定义 $\mathcal{F}$。

---

## 3. 认知逻辑

### 3.1 知识与信念

**定义 3.1** (认知算子):

- $K_i\varphi$: 主体 $i$ 知道 $\varphi$
- $B_i\varphi$: 主体 $i$ 相信 $\varphi$

**定义 3.2** (知识公理系统S5):

- **(K)**: $K(\varphi \to \psi) \to (K\varphi \to K\psi)$ (分配)
- **(T)**: $K\varphi \to \varphi$ (真实性)
- **(4)**: $K\varphi \to KK\varphi$ (正自省)
- **(5)**: $\neg K\varphi \to K\neg K\varphi$ (负自省)

**定理 3.1**: S5是完全的，对应于等价关系框架。

---

### 3.2 公共知识

**定义 3.3** (群体知识):

- $E_G\varphi$: 群体中每个成员都知道 $\varphi$
- $C_G\varphi$: $\varphi$ 是群体 $G$ 的公共知识

**定义 3.4** (公共知识固定点): $C_G\varphi \leftrightarrow E_G(\varphi \land C_G\varphi)$

**定理 3.2** (Aumann, 1976): 在划分模型中，事件是公共知识当且仅当它是包含该事件的所有划分单元的交集。

---

## 4. 时态逻辑

### 4.1 线性时态逻辑

**定义 4.1** (LTL算子):

- $X\varphi$: 下一时刻 $\varphi$
- $F\varphi$: 将来某时刻 $\varphi$
- $G\varphi$: 永远 $\varphi$
- $\varphi U \psi$: $\varphi$ 一直成立直到 $\psi$ 成立

**定义 4.2** (LTL语义): 在序列 $\pi = s_0, s_1, s_2, \ldots$ 上：

- $\pi \models X\varphi$ iff $\pi^1 \models \varphi$（从 $s_1$ 开始的子序列）
- $\pi \models F\varphi$ iff $\exists i \geq 0, \pi^i \models \varphi$
- $\pi \models G\varphi$ iff $\forall i \geq 0, \pi^i \models \varphi$
- $\pi \models \varphi U \psi$ iff $\exists j (\pi^j \models \psi \land \forall i < j, \pi^i \models \varphi)$

---

### 4.2 计算树逻辑

**定义 4.3** (CTL路径量词):

- $A\varphi$: 所有路径满足 $\varphi$
- $E\varphi$: 存在路径满足 $\varphi$

**定义 4.4** (CTL公式): CTL结合路径量词和时态算子，如 $AF\varphi$（所有路径最终 $\varphi$），$EG\varphi$（存在路径永远 $\varphi$）。

**定理 4.1**: CTL和LTL表达能力不可比，但CTL*同时包含两者。

---

## 5. 道义逻辑

### 5.1 义务与许可

**定义 5.1** (道义算子):

- $O\varphi$: 应该 $\varphi$（义务）
- $P\varphi$: 可以 $\varphi$（许可）
- $F\varphi$: 禁止 $\varphi$

**对偶关系**: $O\varphi \leftrightarrow \neg P\neg\varphi$，$F\varphi \leftrightarrow O\neg\varphi$

---

### 5.2 标准道义逻辑

**定义 5.2** (SDL): 标准道义逻辑包含：

- K公理应用于 $O$
- **(D)**: $O\varphi \to P\varphi$（或 $\neg(O\varphi \land O\neg\varphi)$）

**定理 5.1**: SDL对应于serial框架（每个世界有可达世界）。

---

## 6. 非经典模态逻辑

### 6.1 直觉主义模态逻辑

**定义 6.1** (IK): 直觉主义模态逻辑IK扩展直觉主义命题逻辑，添加：

- $\Box$ 和 $\Diamond$ 对偶性在构造性意义下解释
- Kripke语义要求相容性和单调性条件

---

### 6.2 概率模态逻辑

**定义 6.2** (概率算子): $P_{\geq r}\varphi$ 表示"$\varphi$ 的概率至少为 $r$"。

**定理 6.1**: 概率模态逻辑可以完全公理化。

---

## 7. 目录结构

```
docs/07-数理逻辑/06-模态逻辑与哲学逻辑/
├── 00-README.md                    # 本文件
├── 01-基本模态逻辑.md               # Kripke语义
├── 02-规范模态系统.md               # T, S4, S5
├── 03-认知逻辑.md                   # 知识、信念、公共知识
├── 04-时态逻辑.md                   # LTL, CTL
├── 05-道义逻辑.md                   # 义务、许可
├── 06-条件句逻辑.md                 # 反事实条件句
└── 07-实战问题.md                   # 模态公式验证
```

---

## 8. 学习路径

### 8.1 基础路径

**模态语言** → **Kripke语义** → **完全性定理** → **应用逻辑**

### 8.2 应用路径

- **程序验证**: 时态逻辑、模型检测
- **博弈论**: 认知逻辑、公共知识
- **伦理学**: 道义逻辑
- **AI**: 知识表示、规划

---

**最后更新**: 2026年4月5日
**维护者**: FormalMath项目组
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
