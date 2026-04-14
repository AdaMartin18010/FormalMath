import os

def write_md(path, title, lean, background, intuition, formal, proof, examples, apps, concepts, refs):
    lines = [
        "---",
        "msc_primary: 00A99",
        "processed_at: '2026-04-15'",
        f"title: {title}",
        "---",
        f"# {title}",
        "",
        "## Mathlib4 引用",
        "",
        "```lean",
        lean,
        "```",
        "",
        "## 数学背景",
        "",
        background,
        "",
        "## 直观解释",
        "",
        intuition,
        "",
        "## 形式化表述",
        "",
        formal,
        "",
        "## 证明思路",
        "",
        proof,
        "",
        "## 示例",
        "",
        examples,
        "",
        "## 应用",
        "",
        apps,
        "",
        "## 相关概念",
        "",
        concepts,
        "",
        "## 参考",
        "",
        refs,
        "",
        "---",
        "",
        "*最后更新：2026-04-15 | 版本：v1.0.0*",
    ]
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f'Created {path}')

theorems = []

theorems.append((
    "Probability/chebyshev-inequality.md",
    "切比雪夫不等式 (Chebyshev's Inequality)",
    "import Mathlib.Probability.Variance\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Measurable X) (hX2 : Integrable (fun ω => (X ω)^2) P)\n\n/-- 切比雪夫不等式：随机变量偏离期望超过 ε 的概率不超过方差除以 ε² -/\ntheorem chebyshev_inequality (μ : ℝ) (hμ : μ = expectation X P) (ε : ℝ) (hε : 0 < ε) :\n    P {ω | |X ω - μ| ≥ ε} ≤ variance X P / ε^2 := by\n  -- 由马尔可夫不等式应用于 (X - μ)² 得到\n  sorry\n\nend ProbabilityTheory",
    "切比雪夫不等式由俄罗斯数学家帕夫努季·切比雪夫（Pafnuty Chebyshev）于1867年证明，是概率论中最基本且应用广泛的不等式之一。该不等式给出了随机变量偏离其期望值的一个普适上界，仅依赖于方差，而不要求随机变量服从任何特定分布。",
    "切比雪夫不等式提供了一个非常直观的保证：如果一个随机变量的方差很小，那么它取值的波动也会很小。可以想象一个班级的考试成绩，如果平均分是75分且方差很小，那么切比雪夫不等式告诉我们，成绩偏离75分很远的同学比例是有明确上界的。",
    "设 $X$ 是一个具有有限期望 $\\mu = \\mathbb{E}[X]$ 和有限方差 $\\sigma^2 = \\text{Var}(X)$ 的随机变量，则对任意 $\\varepsilon > 0$：\n\n$$P(|X - \\mu| \\geq \\varepsilon) \\leq \\frac{\\sigma^2}{\\varepsilon^2}$$\n\n等价地，用标准差表示：\n\n$$P(|X - \\mu| \\geq k\\sigma) \\leq \\frac{1}{k^2}$$\n\n其中：\n\n- $\\mu = \\mathbb{E}[X]$ 是 $X$ 的数学期望\n- $\\sigma^2 = \\mathbb{E}[(X - \\mu)^2]$ 是 $X$ 的方差\n- $\\varepsilon > 0$ 和 $k > 0$ 是任意正数",
    "1. **构造非负随机变量**：考虑 $(X - \\mu)^2$，这是一个非负随机变量\n2. **应用马尔可夫不等式**：对 $(X - \\mu)^2$ 应用马尔可夫不等式\n3. **事件转换**：利用 $\\{|X - \\mu| \\geq \\varepsilon\\} = \\{(X - \\mu)^2 \\geq \\varepsilon^2\\}$\n4. **化简得结论**：$P(|X - \\mu| \\geq \\varepsilon) = P((X - \\mu)^2 \\geq \\varepsilon^2) \\leq \\mathbb{E}[(X - \\mu)^2]/\\varepsilon^2 = \\sigma^2/\\varepsilon^2$\n\n核心洞察在于将偏差控制问题转化为非负随机变量的期望控制问题。",
    "### 示例 1：正态分布\n\n设 $X \\sim N(\\mu, \\sigma^2)$。根据切比雪夫不等式，$P(|X - \\mu| \\geq 2\\sigma) \\leq 1/4 = 25\\%$。实际上正态分布的精确概率约为 4.6\\%，说明切比雪夫不等式是较宽松的上界，但具有普适性。\n\n### 示例 2：掷骰子的均值\n\n设掷一枚公平骰子，$X$ 为点数。$\\mathbb{E}[X] = 3.5$，$\\text{Var}(X) = 35/12 \\approx 2.92$。切比雪夫不等式给出 $P(|X - 3.5| \\geq 3) \\leq 2.92/9 \\approx 0.324$。实际概率为 0（骰子点数不可能偏离 3.5 超过 2.5），这再次说明了不等式的保守性。\n\n### 示例 3：质量控制\n\n某零件长度均值为 10cm，方差为 0.01cm²。切比雪夫不等式保证长度偏离均值超过 0.5cm 的比例不超过 $0.01 / 0.25 = 4\\%$。",
    "- **大数定律**：证明弱大数定律和强大数定律的关键工具\n- **统计估计**：构造置信区间和样本量估计\n- **随机算法**：分析随机算法的收敛速度和失败概率\n- **质量控制**：评估产品参数的波动范围和合格率\n- **金融风险**：估计资产收益率的极端偏离概率",
    "- 马尔可夫不等式 (Markov's Inequality)：切比雪夫不等式的基础\n- 方差 (Variance)：衡量随机变量离散程度的核心指标\n- 大数定律 (Law of Large Numbers)：大量独立随机变量平均值的稳定性\n- 置信区间 (Confidence Interval)：统计估计中的误差范围\n- 中心极限定理 (Central Limit Theorem)：独立随机变量和的正态收敛",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 6]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 1]\n\n### 在线资源\n\n- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)\n- [Wikipedia - Chebyshev's inequality](https://en.wikipedia.org/wiki/Chebyshev%27s_inequality)"
))

theorems.append((
    "Probability/law-of-large-numbers.md",
    "大数定律 (Law of Large Numbers)",
    "import Mathlib.Probability.IdentDistrib\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- 弱大数定律：独立同分布随机变量序列的样本均值依概率收敛于期望 -/\ntheorem weak_law_large_numbers (hind : Pairwise (Independent identDistrib X P))\n    (hμ : Integrable (X 0) P) :\n    Tendsto (fun n => (1 / n) * ∑ i in Finset.range n, X i) atTop (𝓝 (expectation (X 0) P)) := by\n  -- 利用切比雪夫不等式证明依概率收敛\n  sorry\n\nend ProbabilityTheory",
    "大数定律是概率论中最重要的极限定理之一，由雅各布·伯努利（Jacob Bernoulli）在17世纪末首次提出并于1713年发表。该定理揭示了在重复独立试验中，随机事件的频率会稳定在其概率附近。",
    "大数定律的直观含义非常深刻：当你反复抛掷一枚硬币时，虽然每次的结果都是随机的，但随着抛掷次数的增加，正面朝上的比例会越来越接近 50%%。这就像一个漫长的赌博游戏——短期内你可能大赚或大亏，但只要玩得足够久，结果就会趋向于期望的平均值。",
    "设 $X_1, X_2, \\dots$ 是独立同分布的随机变量序列，$\\mathbb{E}[X_1] = \\mu$，$\\text{Var}(X_1) = \\sigma^2 < \\infty$。定义样本均值为：\n\n$$\\bar{X}_n = \\frac{1}{n} \\sum_{{i=1}}^n X_i$$\n\n**弱大数定律（WLLN）**：\n$$\\bar{X}_n \\xrightarrow{{P}} \\mu \\quad (n \\to \\infty)$$\n\n**强大数定律（SLLN）**：\n$$\\bar{X}_n \\xrightarrow{{a.s.}} \\mu \\quad (n \\to \\infty)$$\n\n其中：\n\n- $\\xrightarrow{{P}}$ 表示依概率收敛\n- $\\xrightarrow{{a.s.}}$ 表示几乎必然收敛\n- $\\mu = \\mathbb{E}[X_1]$ 是共同的数学期望",
    "1. **期望和方差计算**：计算样本均值 $\\bar{X}_n$ 的期望为 $\\mu$，方差为 $\\sigma^2/n$\n2. **切比雪夫不等式**：对弱大数定律，应用切比雪夫不等式于 $\\bar{X}_n$\n3. **概率上界**：得到 $P(|\\bar{X}_n - \\mu| \\geq \\varepsilon) \\leq \\sigma^2/(n\\varepsilon^2) \\to 0$\n4. **Borel-Cantelli 引理**：对强大数定律，利用 Borel-Cantelli 引理证明几乎必然收敛\n\n核心洞察在于独立性的方差可加性使得样本均值的波动以 $1/n$ 的速度衰减。",
    "### 示例 1：抛硬币实验\n\n抛掷一枚公平硬币 $n$ 次，设 $X_i = 1$ 表示第 $i$ 次正面朝上。$\\bar{X}_n$ 是正面频率。大数定律保证当 $n \\to \\infty$ 时，正面频率依概率收敛于 $1/2$。\n\n### 示例 2：蒙特卡洛积分\n\n计算定积分 $\\int_0^1 f(x) dx$ 时，可以生成 $n$ 个均匀随机点 $U_i$，用 $\\frac{1}{n} \\sum_{{i=1}}^n f(U_i)$ 近似。大数定律保证这个估计随 $n$ 增大而收敛到真实积分值。\n\n### 示例 3：保险精算\n\n某保险公司有 10000 份同质保单，每份保单的赔付额是独立同分布的随机变量。大数定律使得公司能够精确预测总赔付额，从而合理定价保费。",
    "- **统计学基础**：频率学派的概率解释和统计推断的理论根基\n- **蒙特卡洛方法**：数值积分和模拟仿真的收敛性保证\n- **保险与金融**：风险评估、期权定价和资产组合管理的理论依据\n- **统计力学**：气体分子运动论中宏观量与微观平均的对应\n- **机器学习**：经验风险最小化的渐近一致性分析",
    "- 中心极限定理 (Central Limit Theorem)：描述大数定律收敛速度的更精细结果\n- 切比雪夫不等式 (Chebyshev's Inequality)：证明弱大数定律的关键工具\n- 依概率收敛 (Convergence in Probability)：弱大数定律中的收敛模式\n- 几乎必然收敛 (Almost Sure Convergence)：强大数定律中的收敛模式\n- 样本均值 (Sample Mean)：随机变量序列的算术平均",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 22]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 2]\n\n### 历史文献\n\n- [J. Bernoulli. Ars Conjectandi. 1713]\n\n### 在线资源\n\n- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)"
))

theorems.append((
    "Probability/central-limit-theorem.md",
    "中心极限定理 (Central Limit Theorem)",
    "import Mathlib.Probability.Distributions.Gaussian\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- 中心极限定理：独立同分布随机变量序列的标准化和依分布收敛于标准正态分布 -/\ntheorem central_limit_theorem (hind : Pairwise (Independent identDistrib X P))\n    (hμ2 : Integrable (fun ω => (X 0 ω)^2) P) (hμ : expectation (X 0) P = μ) (hσ : variance (X 0) P = σ^2) (hσpos : 0 < σ) :\n    Tendsto (fun n => (1 / (σ * sqrt n)) * ∑ i in Finset.range n, (X i - μ)) atTop\n      (𝓝 (gaussianReal 0 1)) := by\n  -- 证明通常基于特征函数或矩生成函数的收敛\n  sorry\n\nend ProbabilityTheory",
    "中心极限定理是概率论中最深刻、影响最广泛的定理之一，由棣莫弗（De Moivre）于1733年对二项分布首次发现，后经拉普拉斯（Laplace）和李雅普诺夫（Lyapunov）等人推广到一般情形。",
    "中心极限定理揭示了一个令人惊叹的数学规律：当我们把许多微小的、独立的随机影响因素叠加在一起时，最终的分布总是呈现出优美的钟形曲线——正态分布。想象一下一个班级学生的身高：它受到遗传、营养、运动、睡眠等众多独立因素的共同影响。每个因素单独作用时可能服从完全不同的分布，但它们的综合效果却神奇地趋向于正态分布。",
    "设 $X_1, X_2, \\dots$ 是独立同分布的随机变量序列，$\\mathbb{E}[X_1] = \\mu$，$\\text{Var}(X_1) = \\sigma^2 < \\infty$。定义部分和 $S_n = \\sum_{{i=1}}^n X_i$，则标准化和：\n\n$$Z_n = \\frac{{S_n - n\\mu}}{{\\sigma\\sqrt{{n}}}} = \\frac{{1}}{{\\sigma\\sqrt{{n}}}} \\sum_{{i=1}}^n (X_i - \\mu)$$\n\n依分布收敛于标准正态分布：\n\n$$Z_n \\xrightarrow{{d}} N(0, 1) \\quad (n \\to \\infty)$$\n\n即对任意实数 $z$：\n\n$$\\lim_{{n \\to \\infty}} P(Z_n \\leq z) = \\Phi(z) = \\frac{{1}}{{\\sqrt{{2\\pi}}}} \\int_{{-\\infty}}^z e^{{-t^2/2}} dt$$\n\n其中：\n\n- $\\Phi(z)$ 是标准正态分布的累积分布函数\n- $\\xrightarrow{{d}}$ 表示依分布收敛",
    "1. **特征函数**：引入随机变量 $X_i$ 的特征函数 $\\varphi_X(t) = \\mathbb{E}[e^{{itX}}]$\n2. **泰勒展开**：在 $t=0$ 附近展开 $\\varphi_X(t) = 1 + it\\mu - \\frac{{t^2\\sigma^2}}{{2}} + o(t^2)$\n3. **独立性利用**：$Z_n$ 的特征函数为 $\\varphi_{{Z_n}}(t) = [\\varphi_X(t/(\\sigma\\sqrt{{n}}))]^n$\n4. **极限计算**：取对数并利用 $\\ln(1+x) \\sim x$ 得到 $\\ln \\varphi_{{Z_n}}(t) \\to -t^2/2$，即标准正态分布的特征函数\n\n核心洞察在于大量微小独立效应的叠加会产生一种普适的极限分布。",
    "### 示例 1：二项分布的正态近似\n\n抛掷一枚公平硬币 $n = 100$ 次，正面次数 $S_n \\sim \\text{Binomial}(100, 0.5)$。根据中心极限定理，$P(S_n \\leq 55) \\approx P(Z \\leq (55.5 - 50)/5) = P(Z \\leq 1.1) \\approx 0.864$。\n\n### 示例 2：骰子点数和\n\n掷 30 枚公平骰子，每枚期望为 3.5，方差为 35/12。总点数和的标准化近似服从 $N(0,1)$。这解释了为什么大量骰子点数和的分布接近钟形曲线。\n\n### 示例 3：测量误差\n\n某物理量的测量受到 100 个独立微小误差源的影响。根据中心极限定理，总测量误差近似服从正态分布，这正是经典误差理论的基础假设。",
    "- **统计推断**：假设检验、置信区间和参数估计的理论基础\n- **质量管理**：六西格玛管理中的正态假设和过程控制\n- **金融工程**：Black-Scholes 期权定价模型和风险管理\n- **信号处理**：噪声分析和滤波器设计的统计模型\n- **生物统计学**：临床试验和大规模流行病学研究中的样本量计算",
    "- 正态分布 (Normal Distribution)：中心极限定理的极限分布\n- 大数定律 (Law of Large Numbers)：描述均值收敛的相伴定理\n- 特征函数 (Characteristic Function)：证明中心极限定理的核心工具\n- 依分布收敛 (Convergence in Distribution)：中心极限定理中的收敛模式\n- 棣莫弗-拉普拉斯定理 (De Moivre-Laplace Theorem)：中心极限定理在二项分布中的特例",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 27]\n- [R. Durrett. Probability: Theory and Examples. Cambridge, 5th edition, 2019. Chapter 3]\n\n### 在线资源\n\n- [Mathlib4 - Gaussian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html)"
))

theorems.append((
    "Probability/markov-inequality.md",
    "马尔可夫不等式 (Markov's Inequality)",
    "import Mathlib.MeasureTheory.Integral.Lebesgue\n\nnamespace MeasureTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Measurable X) (hXnonneg : 0 ≤ X)\n\n/-- 马尔可夫不等式：非负随机变量超过 ε 的概率不超过期望除以 ε -/\ntheorem markov_inequality (ε : ℝ) (hε : 0 < ε) :\n    P {ω | X ω ≥ ε} ≤ (expectation X P) / ε := by\n  -- 由积分单调性和指示函数性质直接得到\n  sorry\n\nend MeasureTheory",
    "马尔可夫不等式由俄国数学家安德雷·马尔可夫（Andrey Markov）提出，是概率论和测度论中最基本的不等式之一。该不等式仅利用随机变量的非负性和期望，给出了尾部概率的一个简单上界。",
    "马尔可夫不等式的含义非常直观：如果一个非负随机变量的平均值很小，那么它取很大值的概率也不可能很大。想象一个城市的居民收入分布：如果平均收入是 5 万元，那么收入超过 100 万元的人口比例不可能超过 5%%。这个结论不需要知道收入分布的任何细节——无论它是正态分布、幂律分布还是其他任何分布。",
    "设 $X$ 是一个非负随机变量（即 $X \\geq 0$ 几乎必然），$\\mathbb{E}[X] < \\infty$，则对任意 $\\varepsilon > 0$：\n\n$$P(X \\geq \\varepsilon) \\leq \\frac{\\mathbb{E}[X]}{\\varepsilon}$$\n\n其中：\n\n- $X$ 是非负随机变量\n- $\\mathbb{E}[X]$ 是 $X$ 的数学期望\n- $\\varepsilon > 0$ 是任意正数\n\n注意：不等式仅对非负随机变量成立，对可取负值的随机变量不适用。",
    "1. **指示函数**：将事件 $\\{X \\geq \\varepsilon\\}$ 用指示函数 $\\mathbf{1}_{{\\{X \\geq \\varepsilon\\}}}$ 表示\n2. **不等式控制**：注意到 $X \\geq \\varepsilon \\cdot \\mathbf{1}_{{\\{X \\geq \\varepsilon\\}}}$（因为 $X$ 非负）\n3. **期望单调性**：对两边取期望得 $\\mathbb{E}[X] \\geq \\varepsilon \\cdot \\mathbb{E}[\\mathbf{1}_{{\\{X \\geq \\varepsilon\\}}}] = \\varepsilon \\cdot P(X \\geq \\varepsilon)$\n4. **整理得证**：两边除以 $\\varepsilon$ 即得结论\n\n核心洞察在于非负性使得期望可以控制尾部概率的质量。",
    "### 示例 1：等待时间\n\n设某服务台的平均等待时间为 10 分钟。马尔可夫不等式保证等待时间超过 30 分钟的概率不超过 $10/30 = 1/3 \\approx 33.3%%$。\n\n### 示例 2：网页加载\n\n某网站页面的平均加载时间为 2 秒。根据马尔可夫不等式，加载时间超过 10 秒的比例不超过 $2/10 = 20%%$。\n\n### 示例 3：与切比雪夫不等式的联系\n\n对随机变量 $Y$，设 $X = (Y - \\mu)^2 \\geq 0$，$\\mathbb{E}[X] = \\sigma^2$。对 $X$ 应用马尔可夫不等式（取 $\\varepsilon = t^2$）即得切比雪夫不等式 $P(|Y - \\mu| \\geq t) \\leq \\sigma^2/t^2$。",
    "- **概率上界估计**：为复杂分布提供简单但普适的尾部概率上界\n- **切比雪夫不等式**：马尔可夫不等式的直接推论\n- **Chernoff 界**：通过矩母函数得到更紧的集中不等式\n- **随机算法分析**：分析随机算法运行时间和空间复杂度的概率保证\n- **排队论**：等待时间和服务强度的基本分析工具",
    "- 切比雪夫不等式 (Chebyshev's Inequality)：马尔可夫不等式的推广\n- Chernoff 界 (Chernoff Bound)：利用矩母函数得到的更紧上界\n- 期望 (Expectation)：随机变量的平均值或重心\n- 指示函数 (Indicator Function)：事件概率与期望之间的桥梁\n- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望波动的概率界",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 5]\n- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 2]\n\n### 在线资源\n\n- [Mathlib4 - Lebesgue Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue.html)"
))

for args in theorems:
    write_md(*args)
