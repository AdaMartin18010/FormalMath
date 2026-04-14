---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 📊 按难度分级索引
---
# 📊 按难度分级索引

> 根据学习阶段选择适合的内容

---

## 🎯 难度分级体系

| 级别 | 标识 | 对应阶段 | 知识要求 |
|------|------|----------|----------|
| 🟢 入门级 | ⭐-⭐⭐ | 高中/本科低年级 | 基础数学概念 |
| 🟡 中级 | ⭐⭐⭐ | 本科高年级 | 专业基础课程 |
| 🟠 高级 | ⭐⭐⭐⭐ | 研究生 | 高级专业课程 |
| 🔴 研究级 | ⭐⭐⭐⭐⭐ | 前沿专题 | 研究文献阅读 |

---

## 🟢 入门级 (高中/本科低年级)

### 适合人群

- 高中生准备数学竞赛
- 大一/大二数学学生
- 对数学感兴趣的初学者

### Mathlib4 注释 - 入门级

| 定理 | 领域 | 难度 | 先修知识 | 链接 |
|------|------|------|----------|------|
| 拉格朗日定理 | 代数学 | ⭐⭐ | 群论基础 | [查看](./02-Mathlib4-Annotations/Algebra/lagrange-theorem.md) |
| 微分中值定理 | 分析学 | ⭐⭐ | 微积分基础 | [查看](./02-Mathlib4-Annotations/Analysis/mean-value-theorem.md) |
| 费马小定理 | 数论 | ⭐⭐ | 模运算 | [查看](./02-Mathlib4-Annotations/NumberTheory/fermat-little-theorem.md) |
| 秩-零化度定理 | 线性代数 | ⭐⭐ | 线性空间 | [查看](./02-Mathlib4-Annotations/LinearAlgebra/rank-nullity-theorem.md) |
| 凯莱定理 | 代数学 | ⭐⭐ | 置换群 | [查看](./02-Mathlib4-Annotations/Algebra/cayley-theorem.md) |

### IMO 题目 - 入门级

| 年份 | 题号 | 领域 | 难度 | 关键技巧 | 链接 |
|------|------|------|------|----------|------|
| 2007 | P2 | 代数 | 2分 | Lagrange 乘数 | [查看](./03-IMO-Competition/2007/Problem-02.md) |
| 2006 | P6 | 代数 | 4分 | Ravi 代换 | [查看](./03-IMO-Competition/2006/Problem-06.md) |
| 2007 | P4 | 几何 | 5分 | 角度追踪 | [查看](./03-IMO-Competition/2007/Problem-04.md) |

### 学习建议

**预计学习时间**: 2-4 周/主题

**推荐路径**:

1. 先阅读定理的教育直观解释
2. 尝试理解 Lean4 代码的基本结构
3. 完成 IMO 入门级题目建立信心
4. 参考 [LEARNING-PATHS.md](./LEARNING-PATHS.md) 的系统路径

---

## 🟡 中级 (本科高年级)

### 适合人群

- 大三/大四数学专业学生
- 准备研究生入学考试的学生
- 有一定数学基础的自学者

### Mathlib4 注释 - 中级

| 定理 | 领域 | 难度 | 先修知识 | 链接 |
|------|------|------|----------|------|
| 群同态基本定理 | 代数学 | ⭐⭐⭐ | 商群、同态 | [查看](./02-Mathlib4-Annotations/Algebra/first-isomorphism-theorem.md) |
| 中国剩余定理 | 代数学 | ⭐⭐⭐ | 理想、环论 | [查看](./02-Mathlib4-Annotations/Algebra/chinese-remainder-theorem.md) |
| 凯莱-哈密顿定理 | 线性代数 | ⭐⭐⭐ | 特征多项式 | [查看](./02-Mathlib4-Annotations/LinearAlgebra/cayley-hamilton-theorem.md) |
| 约当标准型 | 线性代数 | ⭐⭐⭐⭐ | 广义特征向量 | [查看](./02-Mathlib4-Annotations/LinearAlgebra/jordan-normal-form.md) |

### IMO 题目 - 中级

| 年份 | 题号 | 领域 | 难度 | 关键技巧 | 链接 |
|------|------|------|------|----------|------|
| 2006 | P1 | 几何 | 3分 | 调和共轭 | [查看](./03-IMO-Competition/2006/Problem-01.md) |
| 2007 | P1 | 组合 | 4分 | 极值原理 | [查看](./03-IMO-Competition/2007/Problem-01.md) |
| 2006 | P3 | 代数 | 5分 | Schur 不等式 | [查看](./03-IMO-Competition/2006/Problem-03.md) |

### 国际课程对齐

| 课程 | 学校 | 对应内容 | 对齐度 | 链接 |
|------|------|----------|--------|------|
| 线性代数 (18.700) | MIT | 线性代数注释 | 90% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |
| 抽象代数 (18.704) | MIT | 代数注释 | 85% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |
| 实分析 (18.100) | MIT | 分析学基础 | 88% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |

### 学习建议

**预计学习时间**: 4-8 周/主题

**推荐路径**:

1. 系统学习相关国际课程（MIT OCW）
2. 深入理解定理证明的每个步骤
3. 尝试在 Lean4 中形式化简单命题
4. 阅读 04-International-Alignment 的对照文档

---

## 🟠 高级 (研究生)

### 适合人群

- 数学专业研究生
- 准备博士资格考试的学生
- 高级数学爱好者

### Mathlib4 注释 - 高级

| 定理 | 领域 | 难度 | 先修知识 | 链接 |
|------|------|------|----------|------|
| 西罗定理 | 代数学 | ⭐⭐⭐⭐ | p-群理论 | [查看](./02-Mathlib4-Annotations/Algebra/sylow-theorem.md) |
| 柯西积分公式 | 分析学 | ⭐⭐⭐⭐ | 复分析 | [查看](./02-Mathlib4-Annotations/Analysis/cauchy-integral-formula.md) |
| 留数定理 | 分析学 | ⭐⭐⭐⭐ | 全纯函数 | [查看](./02-Mathlib4-Annotations/Analysis/residue-theorem.md) |
| 傅里叶变换 | 分析学 | ⭐⭐⭐⭐ | 泛函分析 | [查看](./02-Mathlib4-Annotations/Analysis/fourier-transform.md) |
| 隐函数定理 | 分析学 | ⭐⭐⭐⭐ | 多元微积分 | [查看](./02-Mathlib4-Annotations/Analysis/implicit-function-theorem.md) |
| 谱定理 | 线性代数 | ⭐⭐⭐⭐ | 正规算子 | [查看](./02-Mathlib4-Annotations/LinearAlgebra/spectral-theorem.md) |
| 布劳威尔不动点定理 | 拓扑学 | ⭐⭐⭐⭐ | 代数拓扑 | [查看](./02-Mathlib4-Annotations/Topology/brouwer-fixed-point.md) |

### IMO 题目 - 高级

| 年份 | 题号 | 领域 | 难度 | 关键技巧 | 链接 |
|------|------|------|------|----------|------|
| 2006 | P4 | 代数 | 6分 | 对称方程组 | [查看](./03-IMO-Competition/2006/Problem-04.md) |
| 2007 | P5 | 数论 | 6分 | Vieta 跳跃 | [查看](./03-IMO-Competition/2007/Problem-05.md) |

### 国际课程对齐 - 高级

| 课程 | 学校 | 对应内容 | 对齐度 | 链接 |
|------|------|----------|--------|------|
| 代数几何 I (18.725) | MIT | 概形理论 | 97% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |
| 代数拓扑 (18.905) | MIT | 拓扑学注释 | 88% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |
| 复分析 (18.112) | MIT | 复分析注释 | 85% | [查看](./04-International-Alignment/02-MIT-Course18-详细对照表.md) |
| FOAG 第 1-15 章 | Stanford | 代数几何基础 | 93% | [查看](./04-International-Alignment/03-Stanford-FOAG-章节对照.md) |

### 学习建议

**预计学习时间**: 8-12 周/主题

**推荐路径**:

1. 系统阅读研究生教材（如 FOAG）
2. 深入理解 Mathlib4 的完整形式化代码
3. 尝试证明相关引理和扩展定理
4. 参考前沿专题建立研究视野

---

## 🔴 研究级 (前沿专题)

### 适合人群

- 博士研究生
- 数学研究人员
- 前沿技术开发者

### 前沿专题内容

| 专题 | 核心人物 | 难度 | 先修要求 | 链接 |
|------|----------|------|----------|------|
| 🧩 凝聚数学 | Peter Scholze | ⭐⭐⭐⭐⭐ | 代数几何、拓扑学 | [查看](./06-Modern-Frontiers/01-凝聚数学.md) |
| ♾️ ∞-范畴论 | Jacob Lurie | ⭐⭐⭐⭐⭐ | 同伦论、高阶范畴 | [查看](./06-Modern-Frontiers/02-无穷范畴论.md) |
| 🌊 粗糙分析 | Terry Lyons | ⭐⭐⭐⭐⭐ | 随机分析、微分方程 | [查看](./06-Modern-Frontiers/03-粗糙分析.md) |
| 🔬 科学机器学习 | - | ⭐⭐⭐⭐⭐ | 机器学习、偏微分方程 | [查看](./06-Modern-Frontiers/04-科学机器学习.md) |
| 🔷 Langlands 纲领 | Gaitsgory 等 | ⭐⭐⭐⭐⭐ | 表示论、代数数论 | [查看](./06-Modern-Frontiers/05-Langlands纲领.md) |
| 🏗️ 同伦类型论 | Voevodsky | ⭐⭐⭐⭐⭐ | 类型论、代数拓扑 | [查看](./06-Modern-Frontiers/06-同伦类型论.md) |

### Mathlib4 注释 - 研究级

| 定理 | 领域 | 难度 | 先修知识 | 链接 |
|------|------|------|----------|------|
| 素数定理 | 数论 | ⭐⭐⭐⭐⭐ | 解析数论 | [查看](./02-Mathlib4-Annotations/NumberTheory/prime-number-theorem.md) |
| 二次互反律 | 数论 | ⭐⭐⭐⭐ | 代数数论 | [查看](./02-Mathlib4-Annotations/NumberTheory/quadratic-reciprocity.md) |
| 狄利克雷定理 | 数论 | ⭐⭐⭐⭐⭐ | L-函数 | [查看](./02-Mathlib4-Annotations/NumberTheory/dirichlet-theorem.md) |

### IMO 题目 - 研究级

| 年份 | 题号 | 领域 | 难度 | 关键技巧 | 链接 |
|------|------|------|------|----------|------|
| 2006 | P2 | 组合 | 7分 | 极值组合 | [查看](./03-IMO-Competition/2006/Problem-02.md) |
| 2007 | P6 | 组合 | 7分 | 格点几何 | [查看](./03-IMO-Competition/2007/Problem-06.md) |

### AI 形式化项目

| 项目 | 难度 | 应用领域 | 链接 |
|------|------|----------|------|
| KELPS | ⭐⭐⭐⭐⭐ | 多语言自动形式化 | [查看](./05-AI-Formalization/01-KELPS.md) |
| DeepSeek-Math | ⭐⭐⭐⭐⭐ | 数学推理大模型 | [查看](./05-AI-Formalization/02-DeepSeek-Math.md) |
| LeanAgent | ⭐⭐⭐⭐⭐ | 终身学习证明器 | [查看](./05-AI-Formalization/03-LeanAgent.md) |
| IMO Lean | ⭐⭐⭐⭐⭐ | IMO 形式化库 | [查看](./05-AI-Formalization/04-IMO-Lean.md) |
| AlphaProof | ⭐⭐⭐⭐⭐ | 自动定理证明 | [查看](./05-AI-Formalization/05-AlphaProof.md) |

### 学习建议

**预计学习时间**: 持续学习，无固定期限

**推荐路径**:

1. 阅读原始研究论文和专著
2. 参与相关学术会议和讨论
3. 使用 AI 形式化工具辅助研究
4. 关注 06-Modern-Frontiers 的最新进展

---

## 📈 进阶路线图

```
入门级 (⭐-⭐⭐)
    │
    ├── 完成基础定理注释阅读
    ├── 解决 IMO 简单题目
    └── 建立数学直觉
    │
    ▼
中级 (⭐⭐⭐)
    │
    ├── 系统学习国际课程
    ├── 理解完整证明过程
    └── 初步形式化练习
    │
    ▼
高级 (⭐⭐⭐⭐)
    │
    ├── 研究生课程深度研读
    ├── 掌握复杂形式化代码
    └── 开始原创性工作
    │
    ▼
研究级 (⭐⭐⭐⭐⭐)
    │
    ├── 前沿专题研究
    ├── AI 工具开发应用
    └── 产生原创贡献
```

---

## 🔗 相关索引

- 🏷️ [按主题分类索引](./BY-TOPIC.md) - 按数学主题查找
- 🎓 [学习路径推荐](./LEARNING-PATHS.md) - 系统性学习规划
- 📋 [快速参考卡片](./QUICK-REF.md) - 公式与编码速查

---

*索引最后更新：2026年4月3日*
