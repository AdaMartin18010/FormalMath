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
    "Probability/bayes-theorem.md",
    "贝叶斯定理 (Bayes' Theorem)",
    "import Mathlib.Probability.ConditionalProbability\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBpos : 0 < P B)\n\n/-- 贝叶斯定理：在已知 B 发生的条件下 A 的条件概率\n    可以用 A 发生时 B 的条件概率和各自的先验概率表示 -/\ntheorem bayes_theorem :\n    P[A|B] = P[B|A] * P A / P B := by\n  -- 由条件概率的定义 P[A|B] = P(A ∩ B) / P(B) 直接推导\n  sorry\n\nend ProbabilityTheory",
    "贝叶斯定理由英国牧师和数学家托马斯·贝叶斯（Thomas Bayes）在18世纪提出，发表于1763年。该定理革命性地将条件概率的计算方向进行了逆转：从 P(B|A) 推导 P(A|B)。这一思想构成了贝叶斯统计学的基石，对科学推理、机器学习、医学诊断和人工智能产生了深远影响。",
    "贝叶斯定理可以用一个医学检测的例子来理解：假设某种疾病在人群中的患病率是 1%%（先验概率），检测的准确率是 99%%。如果一个人检测呈阳性，他实际患病的概率是多少？直觉上可能会认为是 99%%，但贝叶斯定理告诉我们答案要低得多（约 50%%），因为疾病本身很罕见，假阳性的数量可能超过真阳性。",
    "设 $A$ 和 $B$ 是两个事件，$P(B) > 0$，则：\n\n$$P(A|B) = \\frac{{P(B|A) \\cdot P(A)}}{{P(B)}}$$\n\n若 $\\{A_1, A_2, \\dots, A_n\\}$ 构成样本空间的一个划分，则全概率公式给出：\n\n$$P(B) = \\sum_{{i=1}}^n P(B|A_i) \\cdot P(A_i)$$\n\n因此贝叶斯定理也可写成：\n\n$$P(A_j|B) = \\frac{{P(B|A_j) \\cdot P(A_j)}}{{\\sum_{{i=1}}^n P(B|A_i) \\cdot P(A_i)}}$$\n\n其中：\n\n- $P(A|B)$ 称为后验概率（观察到 $B$ 后 $A$ 的概率）\n- $P(A)$ 称为先验概率（观察 $B$ 前 $A$ 的概率）\n- $P(B|A)$ 称为似然（$A$ 发生时观察到 $B$ 的概率）",
    "1. **条件概率定义**：$P(A|B) = P(A \\cap B) / P(B)$ 和 $P(B|A) = P(A \\cap B) / P(A)$\n2. **联合概率等价**：两个表达式中的 $P(A \\cap B)$ 相同\n3. **代入整理**：将 $P(A \\cap B) = P(B|A) \\cdot P(A)$ 代入第一个等式\n4. **全概率公式**：当需要计算 $P(B)$ 时，利用划分 $\\{A_i\\}$ 和全概率公式展开\n\n核心洞察在于新证据的作用是通过似然比来更新先验信念。",
    "### 示例 1：医学检测\n\n设疾病患病率 $P(D) = 0.01$，检测灵敏度 $P(T+|D) = 0.99$，特异度 $P(T-|[la] D) = 0.99$。则：\n$$P(D|T+) = \\frac{{0.99 \\times 0.01}}{{0.99 \\times 0.01 + 0.01 \\times 0.99}} = 0.5$$\n即检测阳性者实际患病的概率只有 50%%。\n\n### 示例 2：垃圾邮件过滤\n\n设某词在垃圾邮件中出现的概率为 5%%，在正常邮件中为 1%%，垃圾邮件占收件箱的 40%%。则包含该词的邮件是垃圾邮件的概率为 $(0.05 \\times 0.4) / (0.05 \\times 0.4 + 0.01 \\times 0.6) \\approx 0.769$。\n\n### 示例 3：法庭证据\n\n某 DNA 证据在嫌疑人无罪时匹配的概率为百万分之一。若该城市有 100 万人，根据贝叶斯定理，即使 DNA 匹配，嫌疑人实际有罪的概率也需考虑其他证据，不能仅由匹配概率推断。",
    "- **机器学习**：朴素贝叶斯分类器、贝叶斯网络和概率图模型\n- **医学诊断**：基于症状和检测结果的疾病概率推断\n- **信息检索**：垃圾邮件过滤、搜索引擎排序和推荐系统\n- **金融风险管理**：信用评分、欺诈检测和投资决策\n- **人工智能**：贝叶斯优化、强化学习和不确定性量化",
    "- 条件概率 (Conditional Probability)：在已知某事件发生条件下另一事件的概率\n- 全概率公式 (Law of Total Probability)：通过划分计算无条件概率\n- 先验概率 (Prior Probability)：观察证据前对假设的概率评估\n- 后验概率 (Posterior Probability)：观察证据后对假设的更新概率\n- 贝叶斯推断 (Bayesian Inference)：基于贝叶斯定理的统计推断框架",
    "### 教材\n\n- [D. Koller, N. Friedman. Probabilistic Graphical Models. MIT Press, 2009. Chapter 2]\n- [E. T. Jaynes. Probability Theory: The Logic of Science. Cambridge, 2003. Chapter 4]\n\n### 历史文献\n\n- [T. Bayes. An Essay towards solving a Problem in the Doctrine of Chances. 1763]\n\n### 在线资源\n\n- [Mathlib4 - ConditionalProbability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html)"
))

theorems.append((
    "Probability/expectation-linearity.md",
    "期望的线性性 (Linearity of Expectation)",
    "import Mathlib.MeasureTheory.Integral.Bochner\n\nnamespace MeasureTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)\n\n/-- 期望的线性性：E[X + Y] = E[X] + E[Y] -/\ntheorem expectation_add :\n    expectation (X + Y) P = expectation X P + expectation Y P := by\n  -- 由积分的线性性直接得到\n  sorry\n\n/-- 期望的数乘性：E[cX] = cE[X] -/\ntheorem expectation_smul (c : ℝ) :\n    expectation (c • X) P = c * expectation X P := by\n  -- 由积分的齐次性直接得到\n  sorry\n\nend MeasureTheory",
    "期望的线性性是概率论和测度论中最基本、最常用的性质之一。该性质断言：随机变量之和的期望等于各自期望之和，即 E[X + Y] = E[X] + E[Y]。这一结论的惊人之处在于它完全不需要 X 和 Y 具有任何独立性或其他关系。",
    "期望的线性性可以看作是一种平均值的分配律。想象你和你的朋友一起经营两家公司，总利润的平均值必然等于两家公司各自平均利润之和——无论两家公司的业绩是互相促进还是此消彼长。这个看似平凡的性质在概率论中却威力无穷。",
    "设 $X$ 和 $Y$ 是同一概率空间上的随机变量，$a, b \\in \\mathbb{{R}}$ 是常数，则：\n\n$$\\mathbb{E}[aX + bY] = a\\mathbb{E}[X] + b\\mathbb{E}[Y]$$\n\n更一般地，对任意有限个随机变量 $X_1, X_2, \\dots, X_n$ 和常数 $c_1, c_2, \\dots, c_n$：\n\n$$\\mathbb{E}\\left[\\sum_{{i=1}}^n c_i X_i\\right] = \\sum_{{i=1}}^n c_i \\mathbb{E}[X_i]$$\n\n其中：\n\n- $\\mathbb{E}[X]$ 表示随机变量 $X$ 的数学期望\n- 此性质不要求 $X_i$ 之间相互独立\n- 此性质成立的前提是各个期望 $\\mathbb{E}[X_i]$ 均存在",
    "1. **积分线性性**：期望本质上是关于概率测度的积分，而积分具有线性性\n2. **离散情形**：$\\mathbb{E}[X+Y] = \\sum_\\omega (X(\\omega) + Y(\\omega)) P(\\omega) = \\sum_\\omega X(\\omega)P(\\omega) + \\sum_\\omega Y(\\omega)P(\\omega) = \\mathbb{E}[X] + \\mathbb{E}[Y]$\n3. **一般测度空间**：通过简单函数逼近和 Bochner 积分的线性性推广到一般情形\n4. **数乘性**：利用积分的齐次性 $\\int cX \\, dP = c \\int X \\, dP$\n\n核心洞察在于期望作为线性泛函，其线性性根植于积分的构造本身。",
    "### 示例 1：掷两枚骰子\n\n设 $X, Y$ 分别为两枚骰子的点数。$\\mathbb{E}[X] = \\mathbb{E}[Y] = 3.5$。由线性性，点数之和的期望为 $\\mathbb{E}[X+Y] = 3.5 + 3.5 = 7$。这与直接计算 36 种等概率结果的平均值完全一致。\n\n### 示例 2：随机图中的三角形数\n\n在 $n$ 个顶点的随机图 $G(n, p)$ 中，设 $X$ 为三角形数。将 $X$ 表示为 $\\binom{n}{3}$ 个指示变量之和，每个指示变量对应一个潜在三角形是否存在。由期望线性性，$\\mathbb{E}[X] = \\binom{n}{3} p^3$，无需考虑不同三角形之间的复杂相关性。\n\n### 示例 3：优惠券收集问题\n\n收集全部 $n$ 种优惠券所需次数的期望可以分解为收集第 $k$ 张新优惠券所需等待时间的期望之和。由线性性，总期望为 $n(1 + 1/2 + \\dots + 1/n) \\approx n \\ln n$。",
    "- **组合概率**：计算复杂随机结构中特定子结构期望数量的标准方法\n- **算法分析**：分析随机算法和启发式算法的期望性能\n- **博弈论**：计算多人博弈中期望收益和最优策略\n- **统计物理**：配分函数和自由能的线性近似计算\n- **机器学习**：集成方法（如随机森林）中基学习器期望误差的分解",
    "- 数学期望 (Expected Value)：随机变量取值的概率加权平均\n- 指示随机变量 (Indicator Random Variable)：仅取 0 或 1 的随机变量\n- Bochner 积分 (Bochner Integral)：向量值函数的积分，期望的测度论基础\n- 方差可加性 (Additivity of Variance)：独立随机变量和的方差等于方差之和\n- 全期望公式 (Law of Total Expectation)：$\\mathbb{E}[X] = \\mathbb{E}[\\mathbb{E}[X|Y]]$",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Chapter 15]\n- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Bochner Integral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html)"
))

theorems.append((
    "Probability/variance-sum-independent.md",
    "独立随机变量和的方差 (Variance of Sum of Independent Random Variables)",
    "import Mathlib.Probability.Variance\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X Y : Ω → ℝ} (hX : Integrable (fun ω => (X ω)^2) P)\n    (hY : Integrable (fun ω => (Y ω)^2) P)\n\n/-- 独立随机变量和的方差等于方差之和 -/\ntheorem variance_add_independent (hindep : Independent X Y P) :\n    variance (X + Y) P = variance X P + variance Y P := by\n  -- 展开方差定义，利用独立性消去协方差项\n  sorry\n\nend ProbabilityTheory",
    "独立随机变量和的方差公式是概率论中最基本且实用的结果之一。该公式断言：若 $X$ 和 $Y$ 独立，则 $\\text{Var}(X + Y) = \\text{Var}(X) + \\text{Var}(Y)$。这一性质是风险分散、投资组合理论、统计抽样和实验设计的理论基础。",
    "这个定理可以用投资组合的例子来理解：假设你同时投资两只互不相关的股票。每只股票的日收益率都有各自的波动（方差）。根据这个定理，组合总收益的方差就是两只股票方差之和。如果你将全部资金投入一只股票，你承担的是该股票的完整波动；但如果你平均分配到两只独立股票上，总波动的增长速度慢于预期收益的增长速度，从而提高了风险调整后的收益。",
    "设 $X$ 和 $Y$ 是两个独立的随机变量，且方差均存在，则：\n\n$$\\text{Var}(X + Y) = \\text{Var}(X) + \\text{Var}(Y)$$\n\n更一般地，若 $X_1, X_2, \\dots, X_n$ 两两独立（或更弱地，不相关），则：\n\n$$\\text{Var}\\left(\\sum_{{i=1}}^n X_i\\right) = \\sum_{{i=1}}^n \\text{Var}(X_i)$$\n\n其中：\n\n- $\\text{Var}(X) = \\mathbb{E}[(X - \\mathbb{E}[X])^2]$ 是随机变量 $X$ 的方差\n- 独立性条件至关重要；若 $X, Y$ 不独立，则有 $\\text{Var}(X+Y) = \\text{Var}(X) + \\text{Var}(Y) + 2\\text{Cov}(X,Y)$\n- $\\text{Cov}(X,Y) = \\mathbb{E}[(X-\\mu_X)(Y-\\mu_Y)]$ 是协方差",
    "1. **方差定义展开**：$\\text{Var}(X+Y) = \\mathbb{E}[(X+Y - \\mu_X - \\mu_Y)^2]$\n2. **平方展开**：$= \\mathbb{E}[(X-\\mu_X)^2 + (Y-\\mu_Y)^2 + 2(X-\\mu_X)(Y-\\mu_Y)]$\n3. **期望线性性**：$= \\text{Var}(X) + \\text{Var}(Y) + 2\\text{Cov}(X,Y)$\n4. **独立性利用**：若 $X, Y$ 独立，则 $\\text{Cov}(X,Y) = 0$，从而得证\n\n核心洞察在于独立性消除了交叉项（协方差），使得总方差呈现可加性。",
    "### 示例 1：掷骰子\n\n掷两枚公平骰子，设 $X, Y$ 为点数。$\\text{Var}(X) = \\text{Var}(Y) = 35/12 \\approx 2.92$。由独立性，点数之和的方差为 $35/12 + 35/12 = 35/6 \\approx 5.83$。\n\n### 示例 2：抽样调查\n\n对 100 名受访者进行独立问卷调查，每人回答的得分方差为 4。则总分方差为 $100 \\times 4 = 400$，标准差为 20。平均得分的方差为 $400/100^2 = 0.04$，标准差为 0.2。这解释了为什么大样本均值更加稳定。\n\n### 示例 3：投资组合\n\n两只独立股票的收益率方差分别为 0.04 和 0.09。等权重投资组合的收益率方差为 $(0.04 + 0.09)/4 = 0.0325$，标准差约为 0.18，小于任何一只股票的标准差（0.2 和 0.3），体现了风险分散效应。",
    "- **投资组合理论**：现代资产组合理论（MPT）中风险分散的数学基础\n- **统计抽样**：样本均值标准误差的计算和置信区间的构造\n- **实验设计**：随机化实验中方差分析和显著性检验的理论依据\n- **质量控制**：多工序生产过程中的总质量波动预测\n- **保险精算**：独立保单组合总赔付风险的聚合计算",
    "- 方差 (Variance)：衡量随机变量偏离期望程度的指标\n- 协方差 (Covariance)：描述两个随机变量联合变化趋势的指标\n- 独立性 (Independence)：一个随机变量的分布不受另一个变量取值影响的性质\n- 不相关性 (Uncorrelatedness)：协方差为零的较弱的条件\n- 大数定律 (Law of Large Numbers)：独立随机变量和方差可加性的渐近结果",
    "### 教材\n\n- [P. Billingsley. Probability and Measure. Wiley, 3rd edition, 1995. Section 21]\n- [S. Ross. A First Course in Probability. Pearson, 10th edition, 2018. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Variance](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html)"
))

theorems.append((
    "Probability/jensen-inequality.md",
    "Jensen 不等式 (Jensen's Inequality)",
    "import Mathlib.Probability.Moments\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : Ω → ℝ} (hX : Integrable X P)\n\n/-- Jensen 不等式：对凸函数 φ，有 φ(E[X]) ≤ E[φ(X)] -/\ntheorem jensen_inequality {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)\n    (hφX : Integrable (φ ∘ X) P) :\n    φ (expectation X P) ≤ expectation (φ ∘ X) P := by\n  -- 利用凸函数的支撑超平面性质和期望的单调性证明\n  sorry\n\nend ProbabilityTheory",
    "Jensen 不等式由丹麦数学家约翰·延森（Johan Jensen）于1906年证明，是数学分析、概率论和凸优化中的核心不等式。该不等式断言：对于凸函数 $\\phi$，有 $\\phi(\\mathbb{E}[X]) \\leq \\mathbb{E}[\\phi(X)]$；对于凹函数，不等号方向相反。",
    "Jensen 不等式的几何直觉非常优美：想象一个凸函数图像（如抛物线 $y = x^2$），曲线上任意两点的连线都在曲线的上方。如果把随机变量 $X$ 的取值看作曲线上的一系列点，那么这些点的平均位置（即期望）对应的函数值，必然小于或等于这些点函数值的平均。换句话说，凸函数会放大离散性——先取平均再代入函数，结果不会大于先代入函数再取平均。",
    "设 $X$ 是一个随机变量，$\\phi: \\mathbb{{R}} \\to \\mathbb{{R}}$ 是一个凸函数，且 $\\mathbb{E}[X]$ 和 $\\mathbb{E}[\\phi(X)]$ 均存在，则：\n\n$$\\phi(\\mathbb{E}[X]) \\leq \\mathbb{E}[\\phi(X)]$$\n\n若 $\\phi$ 是严格凸函数，且 $X$ 不是几乎必然的常数，则严格不等式成立：\n\n$$\\phi(\\mathbb{E}[X]) < \\mathbb{E}[\\phi(X)]$$\n\n对于凹函数 $\\psi$，不等号反向：\n\n$$\\psi(\\mathbb{E}[X]) \\geq \\mathbb{E}[\\psi(X)]$$\n\n其中：\n\n- $\\phi$ 是凸函数意味着对任意 $x, y$ 和 $t \\in [0,1]$：$\\phi(tx + (1-t)y) \\leq t\\phi(x) + (1-t)\\phi(y)$\n- 概率测度 $P$ 可以推广到一般的概率空间",
    "1. **支撑超平面**：凸函数在每一点都存在支撑超平面，即存在斜率 $m$ 使得 $\\phi(x) \\geq \\phi(a) + m(x-a)$ 对所有 $x$ 成立\n2. **取 $a = \\mathbb{E}[X]$**：得到 $\\phi(X) \\geq \\phi(\\mathbb{E}[X]) + m(X - \\mathbb{E}[X])$\n3. **两边取期望**：$\\mathbb{E}[\\phi(X)] \\geq \\phi(\\mathbb{E}[X]) + m\\mathbb{E}[X - \\mathbb{E}[X]] = \\phi(\\mathbb{E}[X])$\n4. **严格凸情形**：若 $X$ 非常数，则存在正概率使 $X \\neq \\mathbb{E}[X]$，由严格凸性得严格不等式\n\n核心洞察在于凸函数的图像总是位于其切线的上方。",
    "### 示例 1：算术-几何平均不等式\n\n取 $\\phi(x) = -\\ln x$（在 $x > 0$ 上凸），对正随机变量 $X$ 应用 Jensen 不等式得 $-\\ln(\\mathbb{E}[X]) \\leq -\\mathbb{E}[\\ln X]$，即 $\\mathbb{E}[X] \\geq e^{\\mathbb{E}[\\ln X]}$。对离散均匀分布即得经典的算术-几何平均不等式。\n\n### 示例 2：方差非负性\n\n取 $\\phi(x) = x^2$（凸函数），得 $(\\mathbb{E}[X])^2 \\leq \\mathbb{E}[X^2]$，即 $\\text{Var}(X) = \\mathbb{E}[X^2] - (\\mathbb{E}[X])^2 \\geq 0$。\n\n### 示例 3：信息论中的 KL 散度\n\n在信息论中，相对熵（KL 散度）的非负性可以通过 Jensen 不等式（对凸函数 $\\phi(x) = x \\ln x$）证明。这说明真实分布与近似分布之间的信息损失总是非负的。",
    "- **信息论**：KL 散度非负性、熵和互信息的性质推导\n- **经济学**：风险厌恶者的效用函数分析（凹效用函数下的确定性等价）\n- **统计学习**：EM 算法和变分推断中的下界优化\n- **金融数学**：期权定价中的凸性偏误和 Jensen's gap\n- **概率不等式**：推导 Hoeffding、Bernstein 等集中不等式",
    "- 凸函数 (Convex Function)：图像位于任意弦下方的函数\n- 支撑超平面 (Supporting Hyperplane)：凸函数图像的切线或切平面推广\n- 算术-几何平均不等式 (AM-GM Inequality)：Jensen 不等式的经典推论\n- KL 散度 (Kullback-Leibler Divergence)：衡量两个概率分布差异的信息论指标\n- 琴生不等式 (Jensen's Inequality in Discrete Form)：有限点情形的 Jensen 不等式",
    "### 教材\n\n- [W. Rudin. Real and Complex Analysis. McGraw-Hill, 3rd edition, 1987. Chapter 3]\n- [S. Boyd, L. Vandenberghe. Convex Optimization. Cambridge, 2004. Section 3.1]\n\n### 在线资源\n\n- [Mathlib4 - Moments](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html)"
))

theorems.append((
    "Probability/chernoff-bound.md",
    "Chernoff 界 (Chernoff Bound)",
    "import Mathlib.Probability.IdentDistrib\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {X : ℕ → Ω → ℝ}\n\n/-- Chernoff 界：独立伯努利变量和偏离期望的指数衰减上界 -/\ntheorem chernoff_bound_upper (hind : Pairwise (Independent identDistrib X P))\n    (hX01 : ∀ i ω, X i ω ∈ {0, 1}) (hμ : expectation (X 0) P = p)\n    (ε : ℝ) (hε : 0 < ε) :\n    P {ω | (1 / n) * ∑ i in Finset.range n, X i ω ≥ p + ε} ≤\n      Real.exp (-2 * n * ε^2) := by\n  -- 利用矩母函数和 Markov 不等式推导\n  sorry\n\nend ProbabilityTheory",
    "Chernoff 界是概率论和计算机科学中最重要的集中不等式之一，以赫尔曼·切尔诺夫（Herman Chernoff）的名字命名。与切比雪夫不等式提供的多项式衰减不同，Chernoff 界给出了独立随机变量和偏离其期望的指数衰减上界。",
    "Chernoff 界的威力在于它描述了大数定律的收敛速度。想象抛掷一枚有偏硬币 1000 次，正面朝上的概率为 60%%。切比雪夫不等式只能告诉你正面频率偏离 60%% 超过 5%% 的概率不超过某个多项式衰减的值，而 Chernoff 界则能给出这个概率小于 $e^{{-50}}$——这是一个极其微小的数。这说明当独立随机变量的数量很大时，样本均值几乎不可能显著偏离期望值。",
    "设 $X_1, X_2, \\dots, X_n$ 是独立的伯努利随机变量，$P(X_i = 1) = p_i$，$P(X_i = 0) = 1 - p_i$。令 $S_n = \\sum_{{i=1}}^n X_i$，$\\mu = \\mathbb{E}[S_n] = \\sum_{{i=1}}^n p_i$。则对任意 $\\delta > 0$：\n\n**上尾**：\n$$P(S_n \\geq (1+\\delta)\\mu) \\leq \\left(\\frac{{e^\\delta}}{{(1+\\delta)^{{1+\\delta}}}}\\right)^\\mu$$\n\n**下尾**：\n$$P(S_n \\leq (1-\\delta)\\mu) \\leq \\left(\\frac{{e^{{-\\delta}}}}{{(1-\\delta)^{{1-\\delta}}}}\\right)^\\mu$$\n\n对于 $0 < \\delta < 1$，有更简洁的形式：\n\n$$P(|S_n - \\mu| \\geq \\delta\\mu) \\leq 2e^{{-\\mu\\delta^2/3}}$$\n\n若所有 $p_i = p$，则对样本均值 $\\bar{X}_n = S_n/n$：\n\n$$P(|\\bar{X}_n - p| \\geq \\varepsilon) \\leq 2e^{{-2n\\varepsilon^2}}$$\n\n其中：\n\n- $S_n$ 是 $n$ 个独立伯努利变量之和\n- $\\mu = \\mathbb{E}[S_n]$ 是期望总和\n- 不等式右端随 $n$ 指数衰减",
    "1. **矩母函数**：计算单个伯努利变量的矩母函数 $M_{{X_i}}(t) = \\mathbb{E}[e^{{tX_i}}] = 1 - p_i + p_i e^t$\n2. **独立性利用**：$S_n$ 的矩母函数为各 $M_{{X_i}}(t)$ 的乘积\n3. **Markov 不等式**：对 $e^{{tS_n}}$ 应用 Markov 不等式，取最优的 $t > 0$\n4. **优化与放缩**：利用 $1 + x \\leq e^x$ 等不等式放缩，得到指数形式的上界\n\n核心洞察在于独立性的矩母函数可分解性使得能够精细控制尾部概率。",
    "### 示例 1：民意调查\n\n调查 1000 名选民，真实支持率为 55%%。Chernoff 界给出样本支持率偏离真实值超过 3%% 的概率不超过 $2e^{{-2 \\times 1000 \\times 0.03^2}} = 2e^{{-1.8}} \\approx 0.33$。若样本量增至 10000，该上界降至约 $2e^{{-18}} \\approx 3 \\times 10^{{-8}}$。\n\n### 示例 2：随机算法\n\n某蒙特卡洛算法每次运行以概率 $p \\geq 0.6$ 给出正确答案。运行 $n = 100$ 次后取多数表决。Chernoff 界保证错误概率小于 $e^{{-2 \\times 100 \\times 0.1^2}} = e^{{-2}} \\approx 0.135$。若 $n = 1000$，错误概率小于 $e^{{-20}} \\approx 2 \\times 10^{{-9}}$。\n\n### 示例 3：负载均衡\n\n将 $n$ 个球独立随机投入 $n$ 个箱子。Chernoff 界可用于证明最大负载以高概率不超过 $O(\\ln n / \\ln \\ln n)$，这是 balls-into-bins 问题的经典结果。",
    "- **随机算法分析**：分析拉斯维加斯和蒙特卡洛算法的失败概率和运行时间\n- **机器学习理论**：PAC 学习框架中的样本复杂度和泛化误差界\n- **通信与编码**：信道容量、纠错码性能和网络吞吐量分析\n- **负载均衡**：分布式系统中任务分配和资源调度的概率保证\n- **统计假设检验**：大规模数据下的显著性水平和检验功效分析",
    "- 集中不等式 (Concentration Inequality)：描述随机变量围绕期望集中的概率界\n- 矩母函数 (Moment Generating Function)：$M_X(t) = \\mathbb{E}[e^{{tX}}]$，推导 Chernoff 界的核心工具\n- Hoeffding 不等式 (Hoeffding's Inequality)：Chernoff 界在有界随机变量上的推广\n- 伯努利试验 (Bernoulli Trial)：仅有两个可能结果的独立随机试验\n- PAC 学习 (PAC Learning)：计算学习理论中的概率近似正确框架",
    "### 教材\n\n- [M. Mitzenmacher, E. Upfal. Probability and Computing. Cambridge, 2nd edition, 2017. Chapter 4]\n- [S. Shalev-Shwartz, S. Ben-David. Understanding Machine Learning. Cambridge, 2014. Chapter B]\n\n### 在线资源\n\n- [Mathlib4 - IdentDistrib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)"
))

theorems.append((
    "Probability/optional-stopping-theorem.md",
    "可选停时定理 (Optional Stopping Theorem)",
    "import Mathlib.Probability.Martingale.Convergence\n\nnamespace ProbabilityTheory\n\nvariable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]\n  {ℱ : Filtration ℕ (MeasureSpace.toMeasurableSpace Ω)}\n  {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ P)\n\n/-- 可选停时定理：在适当条件下，鞅在停时的期望等于初始期望 -/\ntheorem optional_stopping (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ τ)\n    (hbdd : ∃ N, ∀ ω, τ ω ≤ N)\n    (hbddM : ∀ n, ∀ᵐ ω ∂P, |M n ω| ≤ C) :\n    expectation (M τ) P = expectation (M 0) P := by\n  -- 利用鞅的有界收敛性和停时的可测性证明\n  sorry\n\nend ProbabilityTheory",
    "可选停时定理（Optional Stopping Theorem, OST）是鞅论中的核心结果，由约瑟夫·杜布（Joseph L. Doob）系统发展。该定理断言：在适当条件下，一个鞅在停时处的期望等于其初始期望。这一定理在金融数学、博弈论和随机过程理论中具有基础性地位。",
    "可选停时定理可以用一个赌场博弈的例子来理解：假设你参与一个公平的赌博游戏，每次下注的期望收益为零（这是一个鞅）。定理告诉你：无论你采用多么复杂的退出策略——比如连赢三把就走、输光本金就停或达到某个目标利润就退出——你的总期望收益始终等于你开始时的本金。这似乎是反直觉的，因为某些策略在特定路径上看起来非常有利。但关键在于期望是对所有可能路径的平均，而那些看似有利的策略也伴随着同样多的不利路径。",
    "设 $(M_n)_{{n \\geq 0}}$ 是一个关于滤子 $(\\mathcal{F}_n)_{{n \\geq 0}}$ 的鞅，$\\tau$ 是一个关于同一滤子的停时。在以下任一条件下：\n\n$$\\mathbb{E}[M_\\tau] = \\mathbb{E}[M_0]$$\n\n**常见充分条件**：\n\n1. $\\tau$ 是有界停时（存在 $N$ 使得 $\\tau \\leq N$ a.s.）\n2. $M$ 一致有界且 $\\mathbb{E}[\\tau] < \\infty$\n3. $M$ 一致可积\n\n其中：\n\n- 鞅（Martingale）：满足 $\\mathbb{E}[M_{{n+1}} | \\mathcal{F}_n] = M_n$ 的随机过程\n- 停时（Stopping Time）：时刻 $n$ 是否停止仅依赖于截至 $n$ 的信息，即 $\\{\\tau \\leq n\\} \\in \\mathcal{F}_n$\n- $M_\\tau$ 表示鞅在停时 $\\tau$ 处的值",
    "1. **离散停时逼近**：将一般有界停时 $\\tau$ 用取有限值的停时 $\\tau \\wedge n$ 逼近\n2. **鞅性质保持**：证明 $(M_{{\\tau \\wedge n}})$ 仍然是鞅\n3. **期望不变性**：对任意 $n$，$\\mathbb{E}[M_{{\\tau \\wedge n}}] = \\mathbb{E}[M_0]$\n4. **控制收敛**：在有界性条件下，令 $n \\to \\infty$ 并应用控制收敛定理得到 $\\mathbb{E}[M_\\tau] = \\mathbb{E}[M_0]$\n\n核心洞察在于鞅的公平性在可预见的停时策略下保持不变。",
    "### 示例 1：简单随机游走的停时\n\n设 $(S_n)$ 是对称简单随机游走，$S_0 = 0$，$\\tau = \\min\\{n : S_n = 1\\}$。虽然这是停时，但 $\\mathbb{E}[\\tau] = \\infty$，不满足可选停时定理的条件。事实上 $\\mathbb{E}[S_\\tau] = 1 \\neq 0 = \\mathbb{E}[S_0]$。\n\n### 示例 2：有界退出策略\n\n设 $(S_n)$ 同上，但令 $\\tau = \\min\\{n \\leq 100 : S_n = 1\\}$（若 100 步内未到达则停于 100）。此时 $\\tau$ 有界，OST 适用，$\\mathbb{E}[S_\\tau] = 0$。\n\n### 示例 3：美式期权定价\n\n在风险中性测度下，贴现股价过程是鞅。美式期权的提前执行时间是一个停时。可选停时定理说明在无套利条件下，美式期权的价值等于最优停时策略下的期望贴现收益。",
    "- **金融数学**：美式期权定价、最优执行策略和套利分析\n- **博弈论**：公平博弈中各种退出策略的期望收益分析\n- **统计学**：序贯分析中的停止规则和检验功效\n- **随机控制**：最优停止问题和动态决策理论\n- **数学金融**：风险中性定价和对冲策略的形式化推导",
    "- 鞅 (Martingale)：公平博弈的数学模型，条件期望等于当前值\n- 停时 (Stopping Time)：仅依赖于当前和历史信息的随机时间\n- 滤子 (Filtration)：随时间递增的信息结构\n- 控制收敛定理 (Dominated Convergence Theorem)：交换极限与积分顺序的核心工具\n- 美式期权 (American Option)：可以在到期前任意时间执行的金融衍生品",
    "### 教材\n\n- [R. Williams. Probability with Martingales. Cambridge, 1991. Chapter 10]\n- [S. Shreve. Stochastic Calculus for Finance I. Springer, 2004. Chapter 4]\n\n### 在线资源\n\n- [Mathlib4 - Martingale Convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)"
))

for args in theorems:
    write_md(*args)
