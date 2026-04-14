import os

def write_md(path, title, lean, background, intuition, formal, proof, examples, apps, concepts, refs):
    content = f"""---
msc_primary: 00A99
processed_at: '2026-04-15'
title: {title}
---
# {title}

## Mathlib4 引用

```lean
{lean}
```

## 数学背景

{background}

## 直观解释

{intuition}

## 形式化表述

{formal}

## 证明思路

{proof}

## 示例

{examples}

## 应用

{apps}

## 相关概念

{concepts}

## 参考

{refs}

---

*最后更新：2026-04-15 | 版本：v1.0.0*
"""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print(f'Created {path}')

theorems = []

theorems.append((
    "Probability/chebyshev-inequality.md",
    "切比雪夫不等式 (Chebyshev's Inequality)",
    "import Mathlib.Probability.Variance\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Measurable X) (hX2 : Integrable (fun ω => (X ω)^2) P)\n\n/-- 切比雪夫不等式：随机变量偏离期望超过 ε 的概率不超过方差除以 ε² -/\ntheorem chebyshev_inequality (μ : ℝ) (hμ : μ = expectation X P) (ε : ℝ) (hε : 0 < ε) :\n    P {ω | |X ω - μ| ≥ ε} ≤ variance X P / ε^2 := by\n  -- 由马尔可夫不等式应用于 (X - μ)² 得到\n  sorry\n\nend ProbabilityTheory",
    "切比雪夫不等式由俄罗斯数学家帕夫努季·切比雪夫（Pafnuty Chebyshev）于1867年证明，是概率论中最基本且应用广泛的不等式之一。该不等式给出了随机变量偏离其期望值的一个普适上界，仅依赖于方差，而不要求随机变量服从任何特定分布。这使得它在统计推断、大数定律证明和随机算法分析中具有不可替代的地位。",
    "切比雪夫不等式提供了一个非常直观的保证：如果一个随机变量的方差很小，那么它取值的波动也会很小。可以想象一个班级的考试成绩，如果平均分是75分且方差很小，那么切比雪夫不等式告诉我们，成绩偏离75分很远的同学比例是有明确上界的。无论成绩的分布是正态、偏态还是其他任何形状，这个保证都成立——这正是它的强大之处。",
    "设 $X$ 是一个具有有限期望 $\\mu = \\mathbb{E}[X]$ 和有限方差 $\\sigma^2 = \\text{Var}(X)$ 的随机变量，则对任意 $\\varepsilon > 0$：\n\n$$P(|X - \\mu| \\geq \\varepsilon) \\leq \\frac{\\sigma^2}{\\varepsilon^2}$$\n\n等价地，用标准差表示：\n\n$$P(|X - \\mu| \\geq k\\sigma) \\leq \\frac{1}{k^2}$$\n\n其中：\n\n- $\\mu = \\mathbb{E}[X]$ 是 $X$ 的数学期望\n- $\\sigma^2 = \\mathbb{E}[(X - \\mu)^2]$ 是 $X$ 的方差\n- $\\varepsilon > 0$ 和 $k > 0$ 是任意正数",
    "1. **构造非负随机变量**：考虑 $(X - \\mu)^2$，这是一个非负随机变量\\n2. **应用马尔可夫不等式**：对 $(X - \\mu)^2$ 应用马尔可夫不等式\\n3. **事件转换**：利用 $\\{|X - \\mu| \\geq \\varepsilon\\} = \\{(X - \\mu)^2 \\geq \\varepsilon^2\\}$\\n4. **化简得结论**：$P(|X - \\mu| \\geq \\varepsilon) = P((X - \\mu)^2 \\geq \\varepsilon^2) \\leq \\mathbb{E}[(X - \\mu)^2]/\\varepsilon^2 = \\sigma^2/\\varepsilon^2$\n\n核心洞察在于将偏差控制问题转化为非负随机变量的期望控制问题。",
    "### 示例 1：正态分布\n\n设 $X \\sim N(\\mu, \\sigma^2)$。根据切比雪夫不等式，$P(|X - \\mu| \\geq 2\\sigma) \\leq 1/4 = 25\\%$。实际上正态分布的精确概率约为 4.6\\%，说明切比雪夫不等式是较宽松的上界，但具有普适性。\n\n### 示例 2：掷骰子的均值\n\n设掷一枚公平骰子，$X$ 为点数。$\\mathbb{E}[X] = 3.5$，$\\text{Var}(X) = 35/12 \\approx 2.92$。切比雪夫不等式给出 $P(|X - 3.5| \\geq 3) \\leq 2.92/9 \\approx 0.324$。实际概率为 0（骰子点数不可能偏离 3.5 超过 2.5），这再次说明了不等式的保守性。\n\n### 示例 3：质量控制\n\n某零件长度均值为 10cm，方差为 0.01cm²。切比雪夫不等式保证长度偏离均值超过 0.5cm 的比例不超过 $0.01 / 0.25 = 4\\%$。",
    "- **大数定律**：证明弱大数定律和强大数定律的关键工具\n- **统计估计**：构造置信区间和样本量估计\n- **随机算法**：分析随机算法的收敛速度和失败概率\n- **质量控制**：评估产品参数的波动范围和合格率\n- **金融风险**：估计资产收益率的极端偏离概率",
    "- 马尔可夫不等式 (Markov's Inequality)：切比雪夫不等式的基础\n- 方差 (Variance)：衡量随机变量离散程度的核心指标\n- 大数定律 (Law of Large Numbers)：大量独立随机变量平均值的稳定性\n- 置信区间 (Confidence Interval)：统计估计中的误差范围\n- 中心极限定理 (Central Limit Theorem)：独立随机变量和的正态收敛",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 6]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 1]\n\n### 在线资源\n\n- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)\n- [Wikipedia - Chebyshev's inequality](https://en.wikipedia.org/wiki/Chebyshev%27s_inequality)"
))

theorems.append((
    "Probability/law-of-large-numbers.md",
    "大数定律 (Law of Large Numbers)",
    "import Mathlib.Probability.IdentDistrib\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- 弱大数定律：独立同分布随机变量序列的样本均值依概率收敛于期望 -/\ntheorem weak_law_large_numbers (hind : Pairwise (Independent identDistrib X P))\n    (hμ : Integrable (X 0) P) :\n    Tendsto (fun n => (1 / n) * ∑ i in Finset.range n, X i) atTop (𝓝 (expectation (X 0) P)) := by\n  -- 利用切比雪夫不等式证明依概率收敛\n  sorry\n\nend ProbabilityTheory",
    "大数定律是概率论中最重要的极限定理之一，由雅各布·伯努利（Jacob Bernoulli）在17世纪末首次提出并于1713年发表。该定理揭示了在重复独立试验中，随机事件的频率会稳定在其概率附近。大数定律为统计学、保险精算、物理学中的统计力学以及现代机器学习奠定了理论基础，是连接概率与频率的桥梁。",
    "大数定律的直观含义非常深刻：当你反复抛掷一枚硬币时，虽然每次的结果都是随机的，但随着抛掷次数的增加，正面朝上的比例会越来越接近 50%。这就像一个漫长的赌博游戏——短期内你可能大赚或大亏，但只要玩得足够久，结果就会趋向于期望的平均值。这个定理解释了为什么保险公司能够准确预测大量保单的整体赔付率，以及为什么民意调查的样本量越大结果越可靠。",
    "设 $X_1, X_2, \\dots$ 是独立同分布的随机变量序列，$\\mathbb{E}[X_1] = \\mu$，$\\text{Var}(X_1) = \\sigma^2 < \\infty$。定义样本均值为：\n\n$$\\bar{X}_n = \\frac{1}{n} \\sum_{i=1}^n X_i$$\n\n**弱大数定律（WLLN）**：\n$$\\bar{X}_n \\xrightarrow{P} \\mu \quad (n \\to \\infty)$$\n\n**强大数定律（SLLN）**：\n$$\\bar{X}_n \\xrightarrow{a.s.} \\mu \quad (n \\to \\infty)$$\n\n其中：\n\n- $\\xrightarrow{P}$ 表示依概率收敛\n- $\\xrightarrow{a.s.}$ 表示几乎必然收敛\n- $\\mu = \\mathbb{E}[X_1]$ 是共同的数学期望",
    "1. **期望和方差计算**：计算样本均值 $\\bar{X}_n$ 的期望为 $\\mu$，方差为 $\\sigma^2/n$\\n2. **切比雪夫不等式**：对弱大数定律，应用切比雪夫不等式于 $\\bar{X}_n$\\n3. **概率上界**：得到 $P(|\\bar{X}_n - \\mu| \\geq \\varepsilon) \\leq \\sigma^2/(n\\varepsilon^2) \\to 0$\\n4. **Borel-Cantelli 引理**：对强大数定律，利用 Borel-Cantelli 引理证明几乎必然收敛\n\n核心洞察在于独立性的方差可加性使得样本均值的波动以 $1/n$ 的速度衰减。",
    "### 示例 1：抛硬币实验\n\n抛掷一枚公平硬币 $n$ 次，设 $X_i = 1$ 表示第 $i$ 次正面朝上。$\\bar{X}_n$ 是正面频率。大数定律保证当 $n \\to \\infty$ 时，正面频率依概率收敛于 $1/2$。\n\n### 示例 2：蒙特卡洛积分\n\n计算定积分 $\\int_0^1 f(x) dx$ 时，可以生成 $n$ 个均匀随机点 $U_i$，用 $\\frac{1}{n} \\sum_{i=1}^n f(U_i)$ 近似。大数定律保证这个估计随 $n$ 增大而收敛到真实积分值。\n\n### 示例 3：保险精算\n\n某保险公司有 10000 份同质保单，每份保单的赔付额是独立同分布的随机变量。大数定律使得公司能够精确预测总赔付额，从而合理定价保费。",
    "- **统计学基础**：频率学派的概率解释和统计推断的理论根基\n- **蒙特卡洛方法**：数值积分和模拟仿真的收敛性保证\n- **保险与金融**：风险评估、期权定价和资产组合管理的理论依据\n- **统计力学**：气体分子运动论中宏观量与微观平均的对应\n- **机器学习**：经验风险最小化的渐近一致性分析",
    "- 中心极限定理 (Central Limit Theorem)：描述大数定律收敛速度的更精细结果\n- 切比雪夫不等式 (Chebyshev's Inequality)：证明弱大数定律的关键工具\n- 依概率收敛 (Convergence in Probability)：弱大数定律中的收敛模式\n- 几乎必然收敛 (Almost Sure Convergence)：强大数定律中的收敛模式\n- 样本均值 (Sample Mean)：随机变量序列的算术平均",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 22]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 2]\n\n### 历史文献\n\n- [J. Bernoulli. Ars Conjectandi. 1713]\n\n### 在线资源\n\n- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)"
))

theorems.append((
    "Probability/central-limit-theorem.md",
    "中心极限定理 (Central Limit Theorem)",
    "import Mathlib.Probability.Distributions.Gaussian\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- 中心极限定理：独立同分布随机变量序列的标准化和依分布收敛于标准正态分布 -/\ntheorem central_limit_theorem (hind : Pairwise (Independent identDistrib X P))\n    (hμ2 : Integrable (fun ω => (X 0 ω)^2) P) (hμ : expectation (X 0) P = μ) (hσ : variance (X 0) P = σ^2) (hσpos : 0 < σ) :\n    Tendsto (fun n => (1 / (σ * sqrt n)) * ∑ i in Finset.range n, (X i - μ)) atTop\n      (𝓝 (gaussianReal 0 1)) := by\n  -- 证明通常基于特征函数或矩生成函数的收敛\n  sorry\n\nend ProbabilityTheory",
    "中心极限定理是概率论中最深刻、影响最广泛的定理之一，由棣莫弗（De Moivre）于1733年对二项分布首次发现，后经拉普拉斯（Laplace）和李雅普诺夫（Lyapunov）等人推广到一般情形。该定理断言：大量独立随机变量之和的标准化形式，无论原始分布如何，都会趋近于标准正态分布。这一定理解释了正态分布在自然界和社会科学中无处不在的原因，是统计学、物理学、经济学和工程学的基石。",
    "中心极限定理揭示了一个令人惊叹的数学规律：当我们把许多微小的、独立的随机影响因素叠加在一起时，最终的分布总是呈现出优美的钟形曲线——正态分布。想象一下一个班级学生的身高：它受到遗传、营养、运动、睡眠等众多独立因素的共同影响。每个因素单独作用时可能服从完全不同的分布，但它们的综合效果却神奇地趋向于正态分布。这就是为什么考试成绩、测量误差、股票价格变动等大量现象都近似服从正态分布的深层原因。",
    "设 $X_1, X_2, \\dots$ 是独立同分布的随机变量序列，$\\mathbb{E}[X_1] = \\mu$，$\\text{Var}(X_1) = \\sigma^2 < \\infty$。定义部分和 $S_n = \\sum_{i=1}^n X_i$，则标准化和：\n\n$$Z_n = \\frac{S_n - n\\mu}{\\sigma\\sqrt{n}} = \\frac{1}{\\sigma\\sqrt{n}} \\sum_{i=1}^n (X_i - \\mu)$$\n\n依分布收敛于标准正态分布：\n\n$$Z_n \\xrightarrow{d} N(0, 1) \quad (n \\to \\infty)$$\n\n即对任意实数 $z$：\n\n$$\\lim_{n \\to \\infty} P(Z_n \\leq z) = \\Phi(z) = \\frac{1}{\\sqrt{2\\pi}} \\int_{-\\infty}^z e^{-t^2/2} dt$$\n\n其中：\n\n- $\\Phi(z)$ 是标准正态分布的累积分布函数\n- $\\xrightarrow{d}$ 表示依分布收敛",
    "1. **特征函数**：引入随机变量 $X_i$ 的特征函数 $\\varphi_X(t) = \\mathbb{E}[e^{itX}]$\\n2. **泰勒展开**：在 $t=0$ 附近展开 $\\varphi_X(t) = 1 + it\\mu - \\frac{t^2\\sigma^2}{2} + o(t^2)$\\n3. **独立性利用**：$Z_n$ 的特征函数为 $\\varphi_{Z_n}(t) = [\\varphi_X(t/(\\sigma\\sqrt{n}))]^n$\\n4. **极限计算**：取对数并利用 $\\ln(1+x) \\sim x$ 得到 $\\ln \\varphi_{Z_n}(t) \\to -t^2/2$，即标准正态分布的特征函数\n\n核心洞察在于大量微小独立效应的叠加会产生一种普适的极限分布。",
    "### 示例 1：二项分布的正态近似\n\n抛掷一枚公平硬币 $n = 100$ 次，正面次数 $S_n \\sim \\text{Binomial}(100, 0.5)$。根据中心极限定理，$P(S_n \\leq 55) \\approx P(Z \\leq (55.5 - 50)/5) = P(Z \\leq 1.1) \\approx 0.864$。\n\n### 示例 2：骰子点数和\n\n掷 30 枚公平骰子，每枚期望为 3.5，方差为 35/12。总点数和的标准化近似服从 $N(0,1)$。这解释了为什么大量骰子点数和的分布接近钟形曲线。\n\n### 示例 3：测量误差\n\n某物理量的测量受到 100 个独立微小误差源的影响。根据中心极限定理，总测量误差近似服从正态分布，这正是经典误差理论的基础假设。",
    "- **统计推断**：假设检验、置信区间和参数估计的理论基础\n- **质量管理**：六西格玛管理中的正态假设和过程控制\n- **金融工程**：Black-Scholes 期权定价模型和风险管理\n- **信号处理**：噪声分析和滤波器设计的统计模型\n- **生物统计学**：临床试验和大规模流行病学研究中的样本量计算",
    "- 正态分布 (Normal Distribution)：中心极限定理的极限分布\n- 大数定律 (Law of Large Numbers)：描述均值收敛的相伴定理\n- 特征函数 (Characteristic Function)：证明中心极限定理的核心工具\n- 依分布收敛 (Convergence in Distribution)：中心极限定理中的收敛模式\n- 棣莫弗-拉普拉斯定理 (De Moivre-Laplace Theorem)：中心极限定理在二项分布中的特例",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 27]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 3]\n\n### 在线资源\n\n- [Mathlib4 - Gaussian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html)"
))

theorems.append((
    "Probability/markov-inequality.md",
    "马尔可夫不等式 (Markov's Inequality)",
    "import Mathlib.MeasureTheory.Integral.Lebesgue\n\nnamespace MeasureTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Measurable X) (hXnonneg : 0 ≤ X)\n\n/-- 马尔可夫不等式：非负随机变量超过 ε 的概率不超过期望除以 ε -/\ntheorem markov_inequality (ε : ℝ) (hε : 0 < ε) :\n    P {ω | X ω ≥ ε} ≤ (expectation X P) / ε := by\n  -- 由积分单调性和指示函数性质直接得到\n  sorry\n\nend MeasureTheory",
    "马尔可夫不等式由俄国数学家安德雷·马尔可夫（Andrey Markov）提出，是概率论和测度论中最基本的不等式之一。该不等式仅利用随机变量的非负性和期望，给出了尾部概率的一个简单上界。虽然这个上界通常比较宽松，但它的普适性极强——不要求任何关于分布形状的假设。马尔可夫不等式是切比雪夫不等式、Chernoff 界等更精细结果的基础，在随机算法分析和统计估计中具有核心地位。",
    "马尔可夫不等式的含义非常直观：如果一个非负随机变量的平均值很小，那么它取很大值的概率也不可能很大。想象一个城市的居民收入分布：如果平均收入是 5 万元，那么收入超过 100 万元的人口比例不可能超过 5%。这个结论不需要知道收入分布的任何细节——无论它是正态分布、幂律分布还是其他任何分布。虽然 5% 这个上界可能很宽松，但它几乎不需要任何前提条件，这是马尔可夫不等式的独特价值。",
    "设 $X$ 是一个非负随机变量（即 $X \\geq 0$ 几乎必然），$\\mathbb{E}[X] < \\infty$，则对任意 $\\varepsilon > 0$：\n\n$$P(X \\geq \\varepsilon) \\leq \\frac{\\mathbb{E}[X]}{\\varepsilon}$$\n\n其中：\n\n- $X$ 是非负随机变量\n- $\\mathbb{E}[X]$ 是 $X$ 的数学期望\n- $\\varepsilon > 0$ 是任意正数\n\n注意：不等式仅对非负随机变量成立，对可取负值的随机变量不适用。",
    "1. **指示函数**：将事件 $\\{X \\geq \\varepsilon\\}$ 用指示函数 $\\mathbf{1}_{\\{X \\geq \\varepsilon\\}}$ 表示\\n2. **不等式控制**：注意到 $X \\geq \\varepsilon \\cdot \\mathbf{1}_{\\{X \\geq \\varepsilon\\}}$（因为 $X$ 非负）\\n3. **期望单调性**：对两边取期望得 $\\mathbb{E}[X] \\geq \\varepsilon \\cdot \\mathbb{E}[\\mathbf{1}_{\\{X \\geq \\varepsilon\\}}] = \\varepsilon \\cdot P(X \\geq \\varepsilon)$\\n4. **整理得证**：两边除以 $\\varepsilon$ 即得结论\n\n核心洞察在于非负性使得期望可以\"控制\"尾部概率的质量。",
    "### 示例 1：等待时间\n\n设某服务台的平均等待时间为 10 分钟。马尔可夫不等式保证等待时间超过 30 分钟的概率不超过 $10/30 = 1/3 \\approx 33.3\\%$。\n\n### 示例 2：网页加载\n\n某网站页面的平均加载时间为 2 秒。根据马尔可夫不等式，加载时间超过 10 秒的比例不超过 $2/10 = 20\\%$。\n\n### 示例 3：与切比雪夫不等式的联系\n\n对随机变量 $Y$，设 $X = (Y - \\mu)^2 \\geq 0$，$\\mathbb{E}[X] = \\sigma^2$。对 $X$ 应用马尔可夫不等式（取 $\\varepsilon = t^2$）即得切比雪夫不等式 $P(|Y - \\mu| \\geq t) \\leq \\sigma^2/t^2$。",
    "- **概率上界估计**：为复杂分布提供简单但普适的尾部概率上界\n- **切比雪夫不等式**：马尔可夫不等式的直接推论\n- **Chernoff 界**：通过矩母函数得到更紧的集中不等式\n- **随机算法分析**：分析随机算法运行时间和空间复杂度的概率保证\n- **排队论**：等待时间和服务强度的基本分析工具",
    "- 切比雪夫不等式 (Chebyshev's Inequality)：马尔可夫不等式的推广\n- Chernoff 界 (Chernoff Bound)：利用矩母函数得到的更紧上界\n- 期望 (Expectation)：随机变量的平均值或重心\n- 指示函数 (Indicator Function)：事件概率与期望之间的桥梁\n- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望波动的概率界",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 5]\n- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 2]\n\n### 在线资源\n\n- [Mathlib4 - Lebesgue Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue.html)"
))

theorems.append((
    "Probability/bayes-theorem.md",
    "贝叶斯定理 (Bayes' Theorem)",
    "import Mathlib.Probability.ConditionalProbability\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBpos : 0 < P B)\n\n/-- 贝叶斯定理：在已知 B 发生的条件下 A 的条件概率\n    可以用 A 发生时 B 的条件概率和各自的先验概率表示 -/\ntheorem bayes_theorem :\n    P[A|B] = P[B|A] * P A / P B := by\n  -- 由条件概率的定义 P[A|B] = P(A ∩ B) / P(B) 直接推导\n  sorry\n\nend ProbabilityTheory",
    "贝叶斯定理由英国牧师和数学家托马斯·贝叶斯（Thomas Bayes）在18世纪提出，发表于1763年的《论有关机遇问题的求解》一文中。该定理革命性地将条件概率的计算方向进行了逆转：从 $P(B|A)$ 推导 $P(A|B)$。这一思想构成了贝叶斯统计学的基石，对科学推理、机器学习、医学诊断、法律证据评估和人工智能产生了深远影响。贝叶斯方法强调用新证据不断更新对假设的信念程度。",
    "贝叶斯定理可以用一个医学检测的例子来理解：假设某种疾病在人群中的患病率是 1%（先验概率），检测的准确率是 99%。如果一个人检测呈阳性，他实际患病的概率是多少？直觉上可能会认为是 99%，但贝叶斯定理告诉我们答案要低得多（约 50%），因为疾病本身很罕见，假阳性的数量可能超过真阳性。这个定理教会我们如何在获得新证据后，理性地修正原有的信念——这正是科学方法和人工智能推理的核心机制。",
    "设 $A$ 和 $B$ 是两个事件，$P(B) > 0$，则：\n\n$$P(A|B) = \\frac{P(B|A) \\cdot P(A)}{P(B)}$$\n\n若 $\\{A_1, A_2, \\dots, A_n\\}$ 构成样本空间的一个划分，则全概率公式给出：\n\n$$P(B) = \\sum_{i=1}^n P(B|A_i) \\cdot P(A_i)$$\n\n因此贝叶斯定理也可写成：\n\n$$P(A_j|B) = \\frac{P(B|A_j) \\cdot P(A_j)}{\\sum_{i=1}^n P(B|A_i) \\cdot P(A_i)}$$\n\n其中：\n\n- $P(A|B)$ 称为**后验概率**（观察到 $B$ 后 $A$ 的概率）\n- $P(A)$ 称为**先验概率**（观察 $B$ 前 $A$ 的概率）\n- $P(B|A)$ 称为**似然**（$A$ 发生时观察到 $B$ 的概率）",
    "1. **条件概率定义**：$P(A|B) = P(A \\cap B) / P(B)$ 和 $P(B|A) = P(A \\cap B) / P(A)$\\n2. **联合概率等价**：两个表达式中的 $P(A \\cap B)$ 相同\\n3. **代入整理**：将 $P(A \\cap B) = P(B|A) \\cdot P(A)$ 代入第一个等式\\n4. **全概率公式**：当需要计算 $P(B)$ 时，利用划分 $\\{A_i\\}$ 和全概率公式展开\n\n核心洞察在于新证据的作用是通过似然比来更新先验信念。",
    "### 示例 1：医学检测\n\n设疾病患病率 $P(D) = 0.01$，检测灵敏度 $P(T+|D) = 0.99$，特异度 $P(T-|\\neg D) = 0.99$。则：\n$$P(D|T+) = \\frac{0.99 \\times 0.01}{0.99 \\times 0.01 + 0.01 \\times 0.99} = 0.5$$\n即检测阳性者实际患病的概率只有 50\\%。\n\n### 示例 2：垃圾邮件过滤\n\n设某词在垃圾邮件中出现的概率为 5\\%，在正常邮件中为 1\\%，垃圾邮件占收件箱的 40\\%。则包含该词的邮件是垃圾邮件的概率为 $(0.05 \\times 0.4) / (0.05 \\times 0.4 + 0.01 \\times 0.6) \\approx 0.769$。\n\n### 示例 3：法庭证据\n\n某 DNA 证据在嫌疑人无罪时匹配的概率为百万分之一。若该城市有 100 万人，根据贝叶斯定理，即使 DNA 匹配，嫌疑人实际有罪的概率也需考虑其他证据，不能仅由匹配概率推断。",
    "- **机器学习**：朴素贝叶斯分类器、贝叶斯网络和概率图模型\n- **医学诊断**：基于症状和检测结果的疾病概率推断\n- **信息检索**：垃圾邮件过滤、搜索引擎排序和推荐系统\n- **金融风险管理**：信用评分、欺诈检测和投资决策\n- **人工智能**：贝叶斯优化、强化学习和不确定性量化",
    "- 条件概率 (Conditional Probability)：在已知某事件发生条件下另一事件的概率\n- 全概率公式 (Law of Total Probability)：通过划分计算无条件概率\n- 先验概率 (Prior Probability)：观察证据前对假设的概率评估\n- 后验概率 (Posterior Probability)：观察证据后对假设的更新概率\n- 贝叶斯推断 (Bayesian Inference)：基于贝叶斯定理的统计推断框架",
    "### 教材\n\n- [D. Koller, N. Friedman. Probabilistic Graphical Models. MIT Press, 2009. Chapter 2]\n- [E. T. Jaynes. Probability Theory: The Logic of Science. Cambridge, 2003. Chapter 4]\n\n### 历史文献\n\n- [T. Bayes. An Essay towards solving a Problem in the Doctrine of Chances. 1763]\n\n### 在线资源\n\n- [Mathlib4 - ConditionalProbability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html)"
))

theorems.append((
    "Probability/expectation-linearity.md",
    "期望的线性性 (Linearity of Expectation)",
    "import Mathlib.MeasureTheory.Integral.Bochner\n\nnamespace MeasureTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)\n\n/-- 期望的线性性：E[X + Y] = E[X] + E[Y] -/\ntheorem expectation_add :\n    expectation (X + Y) P = expectation X P + expectation Y P := by\n  -- 由积分的线性性直接得到\n  sorry\n\n/-- 期望的数乘性：E[cX] = cE[X] -/\ntheorem expectation_smul (c : ℝ) :\n    expectation (c • X) P = c * expectation X P := by\n  -- 由积分的齐次性直接得到\n  sorry\n\nend MeasureTheory",
    "期望的线性性是概率论和测度论中最基本、最常用的性质之一。该性质断言：随机变量之和的期望等于各自期望之和，即 $\\mathbb{E}[X + Y] = \\mathbb{E}[X] + \\mathbb{E}[Y]$。这一结论的惊人之处在于它完全不需要 $X$ 和 $Y$ 具有任何独立性或其他关系。期望的线性性为复杂随机量的分析提供了强大的简化工具，在组合计数、算法分析、统计物理和博弈论中都有无可替代的作用。",
    "期望的线性性可以看作是一种\"平均值的分配律\"。想象你和你的朋友一起经营两家公司，总利润的平均值必然等于两家公司各自平均利润之和——无论两家公司的业绩是互相促进还是此消彼长。这个看似平凡的性质在概率论中却威力无穷。例如，在分析一个复杂系统（如社交网络中的三角关系数、随机图中的特定结构数）时，往往可以直接将总量拆分为若干指示变量之和，然后利用线性性分别计算每个指示变量的期望，从而避免处理复杂的联合分布。",
    "设 $X$ 和 $Y$ 是同一概率空间上的随机变量，$a, b \\in \\mathbb{R}$ 是常数，则：\n\n$$\\mathbb{E}[aX + bY] = a\\mathbb{E}[X] + b\\mathbb{E}[Y]$$\n\n更一般地，对任意有限个随机变量 $X_1, X_2, \\dots, X_n$ 和常数 $c_1, c_2, \\dots, c_n$：\n\n$$\\mathbb{E}\\left[\\sum_{i=1}^n c_i X_i\\right] = \\sum_{i=1}^n c_i \\mathbb{E}[X_i]$$\n\n其中：\n\n- $\\mathbb{E}[X]$ 表示随机变量 $X$ 的数学期望\n- 此性质**不要求** $X_i$ 之间相互独立\n- 此性质成立的前提是各个期望 $\\mathbb{E}[X_i]$ 均存在",
    "1. **积分线性性**：期望本质上是关于概率测度的积分，而积分具有线性性\\n2. **离散情形**：$\\mathbb{E}[X+Y] = \\sum_\\omega (X(\\omega) + Y(\\omega)) P(\\omega) = \\sum_\\omega X(\\omega)P(\\omega) + \\sum_\\omega Y(\\omega)P(\\omega) = \\mathbb{E}[X] + \\mathbb{E}[Y]$\\n3. **一般测度空间**：通过简单函数逼近和 Bochner 积分的线性性推广到一般情形\\n4. **数乘性**：利用积分的齐次性 $\\int cX \\, dP = c \\int X \\, dP$\n\n核心洞察在于期望作为线性泛函，其线性性根植于积分的构造本身。",
    "### 示例 1：掷两枚骰子\n\n设 $X, Y$ 分别为两枚骰子的点数。$\\mathbb{E}[X] = \\mathbb{E}[Y] = 3.5$。由线性性，点数之和的期望为 $\\mathbb{E}[X+Y] = 3.5 + 3.5 = 7$。这与直接计算 36 种等概率结果的平均值完全一致。\n\n### 示例 2：随机图中的三角形数\n\n在 $n$ 个顶点的随机图 $G(n, p)$ 中，设 $X$ 为三角形数。将 $X$ 表示为 $\\binom{n}{3}$ 个指示变量之和，每个指示变量对应一个潜在三角形是否存在。由期望线性性，$\\mathbb{E}[X] = \\binom{n}{3} p^3$，无需考虑不同三角形之间的复杂相关性。\n\n### 示例 3：优惠券收集问题\n\n收集全部 $n$ 种优惠券所需次数的期望可以分解为收集第 $k$ 张新优惠券所需等待时间的期望之和。由线性性，总期望为 $n(1 + 1/2 + \\dots + 1/n) \\approx n \\ln n$。",
    "- **组合概率**：计算复杂随机结构中特定子结构期望数量的标准方法\n- **算法分析**：分析随机算法和启发式算法的期望性能\n- **博弈论**：计算多人博弈中期望收益和最优策略\n- **统计物理**：配分函数和自由能的线性近似计算\n- **机器学习**：集成方法（如随机森林）中基学习器期望误差的分解",
    "- 数学期望 (Expected Value)：随机变量取值的概率加权平均\n- 指示随机变量 (Indicator Random Variable)：仅取 0 或 1 的随机变量\n- Bochner 积分 (Bochner Integral)：向量值函数的积分，期望的测度论基础\n- 方差可加性 (Additivity of Variance)：独立随机变量和的方差等于方差之和\n- 全期望公式 (Law of Total Expectation)：$\\mathbb{E}[X] = \\mathbb{E}[\\mathbb{E}[X|Y]]$",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 15]\n- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Bochner Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html)"
))

theorems.append((
    "Probability/variance-sum-independent.md",
    "独立随机变量和的方差 (Variance of Sum of Independent Random Variables)",
    "import Mathlib.Probability.Variance\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X Y : Ω → ℝ} (hX : Integrable (fun ω => (X ω)^2) P)\n    (hY : Integrable (fun ω => (Y ω)^2) P)\n\n/-- 独立随机变量和的方差等于方差之和 -/\ntheorem variance_add_independent (hindep : Independent X Y P) :\n    variance (X + Y) P = variance X P + variance Y P := by\n  -- 展开方差定义，利用独立性消去协方差项\n  sorry\n\nend ProbabilityTheory",
    "独立随机变量和的方差公式是概率论中最基本且实用的结果之一。该公式断言：若 $X$ 和 $Y$ 独立，则 $\\text{Var}(X + Y) = \\text{Var}(X) + \\text{Var}(Y)$。这一性质是风险分散、投资组合理论、统计抽样和实验设计的理论基础。它揭示了一个深刻的道理：当独立的不确定性来源叠加时，总波动性并非简单放大，而是以平方和的方式增长——这意味着相对风险实际上在减小，这正是\"不要把鸡蛋放在一个篮子里\"的数学原理。",
    "这个定理可以用投资组合的例子来理解：假设你同时投资两只互不相关的股票。每只股票的日收益率都有各自的波动（方差）。根据这个定理，组合总收益的方差就是两只股票方差之和。如果你将全部资金投入一只股票，你承担的是该股票的完整波动；但如果你平均分配到两只独立股票上，总波动的增长速度慢于预期收益的增长速度，从而提高了风险调整后的收益。这就是多元化投资能够降低风险的核心数学原理——独立性使得波动不会相互放大。",
    "设 $X$ 和 $Y$ 是两个独立的随机变量，且方差均存在，则：\n\n$$\\text{Var}(X + Y) = \\text{Var}(X) + \\text{Var}(Y)$$\n\n更一般地，若 $X_1, X_2, \\dots, X_n$ 两两独立（或更弱地，不相关），则：\n\n$$\\text{Var}\\left(\\sum_{i=1}^n X_i\\right) = \\sum_{i=1}^n \\text{Var}(X_i)$$\n\n其中：\n\n- $\\text{Var}(X) = \\mathbb{E}[(X - \\mathbb{E}[X])^2]$ 是随机变量 $X$ 的方差\n- 独立性条件至关重要；若 $X, Y$ 不独立，则有 $\\text{Var}(X+Y) = \\text{Var}(X) + \\text{Var}(Y) + 2\\text{Cov}(X,Y)$\n- $\\text{Cov}(X,Y) = \\mathbb{E}[(X-\\mu_X)(Y-\\mu_Y)]$ 是协方差",
    "1. **方差定义展开**：$\\text{Var}(X+Y) = \\mathbb{E}[(X+Y - \\mu_X - \\mu_Y)^2]$\\n2. **平方展开**：$= \\mathbb{E}[(X-\\mu_X)^2 + (Y-\\mu_Y)^2 + 2(X-\\mu_X)(Y-\\mu_Y)]$\\n3. **期望线性性**：$= \\text{Var}(X) + \\text{Var}(Y) + 2\\text{Cov}(X,Y)$\\n4. **独立性利用**：若 $X, Y$ 独立，则 $\\text{Cov}(X,Y) = 0$，从而得证\n\n核心洞察在于独立性消除了交叉项（协方差），使得总方差呈现可加性。",
    "### 示例 1：掷骰子\n\n掷两枚公平骰子，设 $X, Y$ 为点数。$\\text{Var}(X) = \\text{Var}(Y) = 35/12 \\approx 2.92$。由独立性，点数之和的方差为 $35/12 + 35/12 = 35/6 \\approx 5.83$。\n\n### 示例 2：抽样调查\n\n对 100 名受访者进行独立问卷调查，每人回答的得分方差为 4。则总分方差为 $100 \\times 4 = 400$，标准差为 20。平均得分的方差为 $400/100^2 = 0.04$，标准差为 0.2。这解释了为什么大样本均值更加稳定。\n\n### 示例 3：投资组合\n\n两只独立股票的收益率方差分别为 0.04 和 0.09。等权重投资组合的收益率方差为 $(0.04 + 0.09)/4 = 0.0325$，标准差约为 0.18，小于任何一只股票的标准差（0.2 和 0.3），体现了风险分散效应。",
    "- **投资组合理论**：现代资产组合理论（MPT）中风险分散的数学基础\n- **统计抽样**：样本均值标准误差的计算和置信区间的构造\n- **实验设计**：随机化实验中方差分析和显著性检验的理论依据\n- **质量控制**：多工序生产过程中的总质量波动预测\n- **保险精算**：独立保单组合总赔付风险的聚合计算",
    "- 方差 (Variance)：衡量随机变量偏离期望程度的指标\n- 协方差 (Covariance)：描述两个随机变量联合变化趋势的指标\n- 独立性 (Independence)：一个随机变量的分布不受另一个变量取值影响的性质\n- 不相关性 (Uncorrelatedness)：协方差为零的较弱的条件\n- 大数定律 (Law of Large Numbers)：独立随机变量和方差可加性的渐近结果",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 21]\n- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)"
))

theorems.append((
    "Probability/jensen-inequality.md",
    "Jensen 不等式 (Jensen's Inequality)",
    "import Mathlib.Probability.Moments\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Integrable X P)\n\n/-- Jensen 不等式：对凸函数 φ，有 φ(E[X]) ≤ E[φ(X)] -/\ntheorem jensen_inequality {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)\n    (hφX : Integrable (φ ∘ X) P) :\n    φ (expectation X P) ≤ expectation (φ ∘ X) P := by\n  -- 利用凸函数的支撑超平面性质和期望的单调性证明\n  sorry\n\nend ProbabilityTheory",
    "Jensen 不等式由丹麦数学家约翰·延森（Johan Jensen）于1906年证明，是数学分析、概率论和凸优化中的核心不等式。该不等式断言：对于凸函数 $\\phi$，有 $\\phi(\\mathbb{E}[X]) \\leq \\mathbb{E}[\\phi(X)]$；对于凹函数，不等号方向相反。Jensen 不等式统一了众多著名不等式（如算术-几何平均不等式、Hölder 不等式、琴生不等式的离散形式），在信息论、经济学、统计学和机器学习中有广泛应用。",
    "Jensen 不等式的几何直觉非常优美：想象一个凸函数图像（如抛物线 $y = x^2$），曲线上任意两点的连线都在曲线的上方。如果把随机变量 $X$ 的取值看作曲线上的一系列点，那么这些点的"平均位置"（即期望）对应的函数值，必然小于或等于这些点函数值的平均。换句话说，凸函数会"放大"离散性——先取平均再代入函数，结果不会大于先代入函数再取平均。这就是为什么人们常说\"波动性对凸函数有利\"的数学根源。",
    "设 $X$ 是一个随机变量，$\\phi: \\mathbb{R} \\to \\mathbb{R}$ 是一个凸函数，且 $\\mathbb{E}[X]$ 和 $\\mathbb{E}[\\phi(X)]$ 均存在，则：\n\n$$\\phi(\\mathbb{E}[X]) \\leq \\mathbb{E}[\\phi(X)]$$\n\n若 $\\phi$ 是严格凸函数，且 $X$ 不是几乎必然的常数，则严格不等式成立：\n\n$$\\phi(\\mathbb{E}[X]) < \\mathbb{E}[\\phi(X)]$$\n\n对于凹函数 $\\psi$，不等号反向：\n\n$$\\psi(\\mathbb{E}[X]) \\geq \\mathbb{E}[\\psi(X)]$$\n\n其中：\n\n- $\\phi$ 是凸函数意味着对任意 $x, y$ 和 $t \\in [0,1]$：$\\phi(tx + (1-t)y) \\leq t\\phi(x) + (1-t)\\phi(y)$\n- 概率测度 $P$ 可以推广到一般的概率空间",
    "1. **支撑超平面**：凸函数在每一点都存在支撑超平面，即存在斜率 $m$ 使得 $\\phi(x) \\geq \\phi(a) + m(x-a)$ 对所有 $x$ 成立\\n2. **取 $a = \\mathbb{E}[X]$**：得到 $\\phi(X) \\geq \\phi(\\mathbb{E}[X]) + m(X - \\mathbb{E}[X])$\\n3. **两边取期望**：$\\mathbb{E}[\\phi(X)] \\geq \\phi(\\mathbb{E}[X]) + m\\mathbb{E}[X - \\mathbb{E}[X]] = \\phi(\\mathbb{E}[X])$\\n4. **严格凸情形**：若 $X$ 非常数，则存在正概率使 $X \\neq \\mathbb{E}[X]$，由严格凸性得严格不等式\n\n核心洞察在于凸函数的图像总是位于其切线的上方。",
    "### 示例 1：算术-几何平均不等式\n\n取 $\\phi(x) = -\\ln x$（在 $x > 0$ 上凸），对正随机变量 $X$ 应用 Jensen 不等式得 $-\\ln(\\mathbb{E}[X]) \\leq -\\mathbb{E}[\\ln X]$，即 $\\mathbb{E}[X] \\geq e^{\\mathbb{E}[\\ln X]}$。对离散均匀分布即得经典的算术-几何平均不等式。\n\n### 示例 2：方差非负性\n\n取 $\\phi(x) = x^2$（凸函数），得 $(\\mathbb{E}[X])^2 \\leq \\mathbb{E}[X^2]$，即 $\\text{Var}(X) = \\mathbb{E}[X^2] - (\\mathbb{E}[X])^2 \\geq 0$。\n\n### 示例 3：信息论中的 KL 散度\n\n在信息论中，相对熵（KL 散度）的非负性可以通过 Jensen 不等式（对凸函数 $\\phi(x) = x \\ln x$）证明。这说明真实分布与近似分布之间的信息损失总是非负的。",
    "- **信息论**：KL 散度非负性、熵和互信息的性质推导\n- **经济学**：风险厌恶者的效用函数分析（凹效用函数下的确定性等价）\n- **统计学习**：EM 算法和变分推断中的下界优化\n- **金融数学**：期权定价中的凸性偏误和 Jensen's gap\n- **概率不等式**：推导 Hoeffding、Bernstein 等集中不等式",
    "- 凸函数 (Convex Function)：图像位于任意弦下方的函数\n- 支撑超平面 (Supporting Hyperplane)：凸函数图像的切线或切平面推广\n- 算术-几何平均不等式 (AM-GM Inequality)：Jensen 不等式的经典推论\n- KL 散度 (Kullback-Leibler Divergence)：衡量两个概率分布差异的信息论指标\n- 琴生不等式 (Jensen's Inequality in Discrete Form)：有限点情形的 Jensen 不等式",
    "### 教材\n\n- [W. Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 3]\n- [S. Boyd, L. Vandenberghe. Convex Optimization. Cambridge, 2004. Section 3.1]\n\n### 在线资源\n\n- [Mathlib4 - Moments](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html)"
))

theorems.append((
    "Probability/chernoff-bound.md",
    "Chernoff 界 (Chernoff Bound)",
    "import Mathlib.Probability.IdentDistrib\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- Chernoff 界：独立伯努利变量和偏离期望的指数衰减上界 -/\ntheorem chernoff_bound_upper (hind : Pairwise (Independent identDistrib X P))\n    (hX01 : ∀ i ω, X i ω ∈ {0, 1}) (hμ : expectation (X 0) P = p)\n    (ε : ℝ) (hε : 0 < ε) :\n    P {ω | (1 / n) * ∑ i in Finset.range n, X i ω ≥ p + ε} ≤\n      Real.exp (-2 * n * ε^2) := by\n  -- 利用矩母函数和 Markov 不等式推导\n  sorry\n\nend ProbabilityTheory",
    "Chernoff 界是概率论和计算机科学中最重要的集中不等式之一，以赫尔曼·切尔诺夫（Herman Chernoff）的名字命名。与切比雪夫不等式提供的多项式衰减不同，Chernoff 界给出了独立随机变量和偏离其期望的**指数衰减**上界。这使得它在分析大量独立试验时极其强大，是随机算法分析、机器学习理论、统计假设检验和通信理论中不可或缺的工具。",
    "Chernoff 界的威力在于它描述了"大数定律的收敛速度"。想象抛掷一枚有偏硬币 1000 次，正面朝上的概率为 60%。切比雪夫不等式只能告诉你正面频率偏离 60% 超过 5% 的概率不超过某个多项式衰减的值，而 Chernoff 界则能给出这个概率小于 $e^{-50}$——这是一个极其微小的数。这说明当独立随机变量的数量很大时，样本均值几乎不可能显著偏离期望值。这个指数集中现象是现代随机计算和统计学习理论能够给出强保证的根本原因。",
    "设 $X_1, X_2, \\dots, X_n$ 是独立的伯努利随机变量，$P(X_i = 1) = p_i$，$P(X_i = 0) = 1 - p_i$。令 $S_n = \\sum_{i=1}^n X_i$，$\\mu = \\mathbb{E}[S_n] = \\sum_{i=1}^n p_i$。则对任意 $\\delta > 0$：\n\n**上尾**：\n$$P(S_n \\geq (1+\\delta)\\mu) \\leq \\left(\\frac{e^\\delta}{(1+\\delta)^{1+\\delta}}\\right)^\\mu$$\n\n**下尾**：\n$$P(S_n \\leq (1-\\delta)\\mu) \\leq \\left(\\frac{e^{-\\delta}}{(1-\\delta)^{1-\\delta}}\\right)^\\mu$$\n\n对于 $0 < \\delta < 1$，有更简洁的形式：\n\n$$P(|S_n - \\mu| \\geq \\delta\\mu) \\leq 2e^{-\\mu\\delta^2/3}$$\n\n若所有 $p_i = p$，则对样本均值 $\\bar{X}_n = S_n/n$：\n\n$$P(|\\bar{X}_n - p| \\geq \\varepsilon) \\leq 2e^{-2n\\varepsilon^2}$$\n\n其中：\n\n- $S_n$ 是 $n$ 个独立伯努利变量之和\n- $\\mu = \\mathbb{E}[S_n]$ 是期望总和\n- 不等式右端随 $n$ 指数衰减",
    "1. **矩母函数**：计算单个伯努利变量的矩母函数 $M_{X_i}(t) = \\mathbb{E}[e^{tX_i}] = 1 - p_i + p_i e^t$\\n2. **独立性利用**：$S_n$ 的矩母函数为各 $M_{X_i}(t)$ 的乘积\\n3. **Markov 不等式**：对 $e^{tS_n}$ 应用 Markov 不等式，取最优的 $t > 0$\\n4. **优化与放缩**：利用 $1 + x \\leq e^x$ 等不等式放缩，得到指数形式的上界\n\n核心洞察在于独立性的矩母函数可分解性使得能够精细控制尾部概率。",
    "### 示例 1：民意调查\n\n调查 1000 名选民，真实支持率为 55\\%。Chernoff 界给出样本支持率偏离真实值超过 3\\% 的概率不超过 $2e^{-2 \\times 1000 \\times 0.03^2} = 2e^{-1.8} \\approx 0.33$。若样本量增至 10000，该上界降至约 $2e^{-18} \\approx 3 \\times 10^{-8}$。\n\n### 示例 2：随机算法\n\n某蒙特卡洛算法每次运行以概率 $p \\geq 0.6$ 给出正确答案。运行 $n = 100$ 次后取多数表决。Chernoff 界保证错误概率小于 $e^{-2 \\times 100 \\times 0.1^2} = e^{-2} \\approx 0.135$。若 $n = 1000$，错误概率小于 $e^{-20} \\approx 2 \\times 10^{-9}$。\n\n### 示例 3：负载均衡\n\n将 $n$ 个球独立随机投入 $n$ 个箱子。Chernoff 界可用于证明最大负载以高概率不超过 $O(\\ln n / \\ln \\ln n)$，这是 balls-into-bins 问题的经典结果。",
    "- **随机算法分析**：分析拉斯维加斯和蒙特卡洛算法的失败概率和运行时间\n- **机器学习理论**：PAC 学习框架中的样本复杂度和泛化误差界\n- **通信与编码**：信道容量、纠错码性能和网络吞吐量分析\n- **负载均衡**：分布式系统中任务分配和资源调度的概率保证\n- **统计假设检验**：大规模数据下的显著性水平和检验功效分析",
    "- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望集中的概率界\n- 矩母函数 (Moment Generating Function)：$M_X(t) = \\mathbb{E}[e^{tX}]$，推导 Chernoff 界的核心工具\n- Hoeffding 不等式 (Hoeffding's Inequality)：Chernoff 界在有界随机变量上的推广\n- 伯努利试验 (Bernoulli Trial)：仅有两个可能结果的独立随机试验\n- PAC 学习 (PAC Learning)：计算学习理论中的概率近似正确框架",
    "### 教材\n\n- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 4]\n- [S. Shalev-Shwartz, S. Ben-David. Understanding Machine Learning. Cambridge, 2014. Chapter B]\n\n### 在线资源\n\n- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)"
))

theorems.append((
    "Probability/optional-stopping-theorem.md",
    "可选停时定理 (Optional Stopping Theorem)",
    "import Mathlib.Probability.Martingale.Convergence\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {ℱ : Filtration ℕ (MeasureSpace.toMeasurableSpace Ω)}\n  {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ P)\n\n/-- 可选停时定理：在适当条件下，鞅在停时的期望等于初始期望 -/\ntheorem optional_stopping (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ τ)\n    (hbdd : ∃ N, ∀ ω, τ ω ≤ N)\n    (hbddM : ∀ n, ∀ᵐ ω ∂P, |M n ω| ≤ C) :\n    expectation (M τ) P = expectation (M 0) P := by\n  -- 利用鞅的有界收敛性和停时的可测性证明\n  sorry\n\nend ProbabilityTheory",
    "可选停时定理（Optional Stopping Theorem, OST）是鞅论中的核心结果，由约瑟夫·杜布（Joseph L. Doob）系统发展。该定理断言：在适当条件下，一个鞅（martingale）在停时（stopping time）处的期望等于其初始期望。这一定理在金融数学、博弈论和随机过程理论中具有基础性地位。它解释了为什么在公平博弈中，无论采用何种"停时策略"（如在赢够某个数额后退出），期望收益都不会改变——前提是满足定理的有界性条件。",
    "可选停时定理可以用一个赌场博弈的例子来理解：假设你参与一个"公平"的赌博游戏，每次下注的期望收益为零（这是一个鞅）。定理告诉你：无论你采用多么复杂的退出策略——比如"连赢三把就走"、"输光本金就停"或"达到某个目标利润就退出"——你的总期望收益始终等于你开始时的本金。这似乎是反直觉的，因为某些策略在特定路径上看起来非常有利。但关键在于"期望"是对所有可能路径的平均，而那些看似有利的策略也伴随着同样多的不利路径。当然，这个结论只在满足有界性条件时成立；如果条件被违反（如"加倍投注法"需要无限资金），期望确实可能改变。",
    "设 $(M_n)_{n \\geq 0}$ 是一个关于滤子 $(\\mathcal{F}_n)_{n \\geq 0}$ 的鞅，$\\tau$ 是一个关于同一滤子的停时。在以下任一条件下：\n\n$$\\mathbb{E}[M_\\tau] = \\mathbb{E}[M_0]$$\n\n**常见充分条件**：\n\n1. $\\tau$ 是有界停时（存在 $N$ 使得 $\\tau \\leq N$ a.s.）\n2. $M$ 一致有界且 $\\mathbb{E}[\\tau] < \\infty$\n3. $M$ 一致可积\n\n其中：\n\n- **鞅**（Martingale）：满足 $\\mathbb{E}[M_{n+1} | \\mathcal{F}_n] = M_n$ 的随机过程\n- **停时**（Stopping Time）：时刻 $n$ 是否停止仅依赖于截至 $n$ 的信息，即 $\\{\\tau \\leq n\\} \\in \\mathcal{F}_n$\n- $M_\\tau$ 表示鞅在停时 $\\tau$ 处的值",
    "1. **离散停时逼近**：将一般有界停时 $\\tau$ 用取有限值的停时 $\\tau \\wedge n$ 逼近\\n2. **鞅性质保持**：证明 $(M_{\\tau \\wedge n})$ 仍然是鞅\\n3. **期望不变性**：对任意 $n$，$\\mathbb{E}[M_{\\tau \\wedge n}] = \\mathbb{E}[M_0]$\\n4. **控制收敛**：在有界性条件下，令 $n \\to \\infty$ 并应用控制收敛定理得到 $\\mathbb{E}[M_\\tau] = \\mathbb{E}[M_0]$\n\n核心洞察在于鞅的"公平性"在"可预见的"停时策略下保持不变。",
    "### 示例 1：简单随机游走的停时\n\n设 $(S_n)$ 是对称简单随机游走，$S_0 = 0$，$\\tau = \\min\\{n : S_n = 1\\}$。虽然这是停时，但 $\\mathbb{E}[\\tau] = \\infty$，不满足可选停时定理的条件。事实上 $\\mathbb{E}[S_\\tau] = 1 \\neq 0 = \\mathbb{E}[S_0]$。\n\n### 示例 2：有界退出策略\n\n设 $(S_n)$ 同上，但令 $\\tau = \\min\\{n \\leq 100 : S_n = 1\\}$（若 100 步内未到达则停于 100）。此时 $\\tau$ 有界，OST 适用，$\\mathbb{E}[S_\\tau] = 0$。\n\n### 示例 3：美式期权定价\n\n在风险中性测度下，贴现股价过程是鞅。美式期权的提前执行时间是一个停时。可选停时定理说明在无套利条件下，美式期权的价值等于最优停时策略下的期望贴现收益。",
    "- **金融数学**：美式期权定价、最优执行策略和套利分析\n- **博弈论**：公平博弈中各种退出策略的期望收益分析\n- **统计学**：序贯分析中的停止规则和检验功效\n- **随机控制**：最优停止问题和动态决策理论\n- **数学金融**：风险中性定价和对冲策略的形式化推导",
    "- 鞅 (Martingale)：公平博弈的数学模型，条件期望等于当前值\n- 停时 (Stopping Time)：仅依赖于当前和历史信息的随机时间\n- 滤子 (Filtration)：随时间递增的信息结构\n- 控制收敛定理 (Dominated Convergence Theorem)：交换极限与积分顺序的核心工具\n- 美式期权 (American Option)：可以在到期前任意时间执行的金融衍生品",
    "### 教材\n\n- [R. Williams. Probability with Martingales. Cambridge, 1991. Chapter 10]\n- [S. Shreve. Stochastic Calculus for Finance I. Springer, 2004. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Martingale Convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)"
))

for args in theorems:
    write_md(*args)
