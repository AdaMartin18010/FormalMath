---
title: 概率统计模拟实验与Python实现
msc_primary: 60-08
---

# 概率统计模拟实验与Python实现

## 实验1：大数定律的模拟验证

### 理论

**弱大数定律**：设 $X_1, X_2, ...$ 是i.i.d.随机变量，$E[X_i] = \mu$，则
$$\bar{X}_n = \frac{1}{n}\sum_{i=1}^n X_i \xrightarrow{P} \mu$$

### Python实现

```python
import numpy as np
import matplotlib.pyplot as plt

np.random.seed(42)

# 模拟参数
n_max = 10000
n_trials = 100  # 重复实验次数

# 不同分布的模拟
distributions = {
    'Bernoulli(p=0.3)': lambda n: np.random.binomial(1, 0.3, n),
    'Uniform(0,1)': lambda n: np.random.uniform(0, 1, n),
    'Exponential(λ=1)': lambda n: np.random.exponential(1, n),
    'Standard Normal': lambda n: np.random.standard_normal(n)
}

theoretical_means = {
    'Bernoulli(p=0.3)': 0.3,
    'Uniform(0,1)': 0.5,
    'Exponential(λ=1)': 1.0,
    'Standard Normal': 0.0
}

fig, axes = plt.subplots(2, 2, figsize=(14, 10))
axes = axes.flatten()

for idx, (name, generator) in enumerate(distributions.items()):
    ax = axes[idx]

    # 运行多次实验
    for trial in range(n_trials):
        samples = generator(n_max)
        cumulative_means = np.cumsum(samples) / np.arange(1, n_max + 1)
        ax.plot(range(1, n_max + 1), cumulative_means, alpha=0.1, color='blue')

    # 理论均值
    true_mean = theoretical_means[name]
    ax.axhline(y=true_mean, color='red', linestyle='--', linewidth=2,
               label=f'Theoretical μ = {true_mean}')

    ax.set_xlabel('Sample Size (n)')
    ax.set_ylabel('Sample Mean')
    ax.set_title(f'Law of Large Numbers: {name}')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xscale('log')

plt.tight_layout()
plt.savefig('law_of_large_numbers.png', dpi=150)
plt.show()

print("结论：随着样本量增大，样本均值收敛到理论期望值")
```

---

## 实验2：中心极限定理的模拟验证

### 理论

**中心极限定理**：设 $X_1, X_2, ...$ 是i.i.d.随机变量，$E[X_i] = \mu$，$Var(X_i) = \sigma^2$，则
$$\frac{\bar{X}_n - \mu}{\sigma/\sqrt{n}} \xrightarrow{d} N(0, 1)$$

### Python实现

```python
from scipy import stats

# 实验参数
sample_sizes = [1, 5, 10, 30, 100]
n_experiments = 10000

# 使用指数分布（高度偏态）
lambda_param = 1.0
theoretical_mean = 1 / lambda_param
theoretical_std = 1 / lambda_param

fig, axes = plt.subplots(2, 3, figsize=(15, 10))
axes = axes.flatten()

for idx, n in enumerate(sample_sizes):
    ax = axes[idx]

    # 进行多次实验，计算样本均值
    sample_means = []
    for _ in range(n_experiments):
        samples = np.random.exponential(1/lambda_param, n)
        sample_means.append(np.mean(samples))

    # 标准化
    standardized = (np.array(sample_means) - theoretical_mean) / (theoretical_std / np.sqrt(n))

    # 绘制直方图
    ax.hist(standardized, bins=50, density=True, alpha=0.7, color='skyblue',
            edgecolor='black', label='Simulated')

    # 叠加标准正态分布
    x = np.linspace(-4, 4, 100)
    ax.plot(x, stats.norm.pdf(x, 0, 1), 'r-', linewidth=2, label='Standard Normal')

    ax.set_xlabel('Standardized Sample Mean')
    ax.set_ylabel('Density')
    ax.set_title(f'CLT with n = {n}')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xlim(-4, 4)

# 最后一个子图：QQ图
ax = axes[5]
stats.probplot(standardized, dist="norm", plot=ax)
ax.set_title('Q-Q Plot (n=100)')
ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('central_limit_theorem.png', dpi=150)
plt.show()

print("结论：即使原始分布是偏态的，标准化样本均值的分布也趋近标准正态")
```

---

## 实验3：置信区间的覆盖率验证

```python
# 验证95%置信区间的实际覆盖率
n_samples = 100
n_experiments = 10000
confidence_level = 0.95
true_mean = 5.0
true_std = 2.0

# 理论临界值
z_critical = stats.norm.ppf((1 + confidence_level) / 2)

covered = 0
intervals = []

for _ in range(n_experiments):
    # 生成样本
    sample = np.random.normal(true_mean, true_std, n_samples)
    sample_mean = np.mean(sample)
    sample_std = np.std(sample, ddof=1)

    # 计算置信区间（使用t分布）
    t_critical = stats.t.ppf((1 + confidence_level) / 2, df=n_samples-1)
    margin_error = t_critical * sample_std / np.sqrt(n_samples)

    ci_lower = sample_mean - margin_error
    ci_upper = sample_mean + margin_error

    intervals.append((ci_lower, ci_upper))

    # 检查是否覆盖真实均值
    if ci_lower <= true_mean <= ci_upper:
        covered += 1

coverage_rate = covered / n_experiments
print(f"理论置信水平: {confidence_level*100}%")
print(f"实际覆盖率: {coverage_rate*100:.2f}%")

# 可视化前100个置信区间
fig, ax = plt.subplots(figsize=(12, 8))
for i in range(min(100, n_experiments)):
    ci = intervals[i]
    color = 'blue' if ci[0] <= true_mean <= ci[1] else 'red'
    ax.plot([ci[0], ci[1]], [i, i], color=color, alpha=0.5, linewidth=1)

ax.axvline(x=true_mean, color='green', linestyle='--', linewidth=2, label=f'True μ = {true_mean}')
ax.set_xlabel('Value')
ax.set_ylabel('Experiment Index')
ax.set_title(f'95% Confidence Intervals (Coverage: {coverage_rate*100:.1f}%)')
ax.legend()
ax.grid(True, alpha=0.3)
plt.savefig('confidence_intervals.png', dpi=150)
plt.show()
```

---

## 实验4：假设检验的检验力和错误率

```python
# 检验力分析（Power Analysis）
effect_sizes = np.linspace(0, 1.5, 50)
sample_sizes = [20, 50, 100, 200]
alpha = 0.05
n_simulations = 1000

fig, ax = plt.subplots(figsize=(10, 6))

for n in sample_sizes:
    powers = []
    for effect in effect_sizes:
        rejections = 0
        for _ in range(n_simulations):
            # 生成两组数据：一组均值0，一组均值effect
            group1 = np.random.normal(0, 1, n)
            group2 = np.random.normal(effect, 1, n)

            # t检验
            t_stat, p_value = stats.ttest_ind(group1, group2)
            if p_value < alpha:
                rejections += 1

        power = rejections / n_simulations
        powers.append(power)

    ax.plot(effect_sizes, powers, 'o-', label=f'n = {n}', linewidth=2, markersize=4)

ax.axhline(y=0.05, color='red', linestyle='--', alpha=0.5, label='α = 0.05')
ax.axhline(y=0.8, color='green', linestyle='--', alpha=0.5, label='Power = 0.8')
ax.set_xlabel('Effect Size')
ax.set_ylabel('Statistical Power')
ax.set_title('Power Analysis for Two-Sample t-test')
ax.legend()
ax.grid(True, alpha=0.3)
plt.savefig('power_analysis.png', dpi=150)
plt.show()
```

---

## 实验5： Bootstrap方法

```python
# Bootstrap置信区间
def bootstrap_ci(data, n_bootstrap=10000, confidence=0.95):
    """计算Bootstrap置信区间"""
    bootstrap_means = []
    n = len(data)

    for _ in range(n_bootstrap):
        # 有放回抽样
        sample = np.random.choice(data, size=n, replace=True)
        bootstrap_means.append(np.mean(sample))

    # 百分位数方法
    alpha = (1 - confidence) / 2
    lower = np.percentile(bootstrap_means, alpha * 100)
    upper = np.percentile(bootstrap_means, (1 - alpha) * 100)

    return lower, upper, bootstrap_means

# 生成偏态数据（收入分布）
np.random.seed(42)
income = np.random.lognormal(mean=10, sigma=1, size=100)

# 计算传统置信区间和Bootstrap置信区间
sample_mean = np.mean(income)
sample_std = np.std(income, ddof=1)
n = len(income)

# 传统方法（假设正态）
t_critical = stats.t.ppf(0.975, df=n-1)
traditional_ci = (sample_mean - t_critical * sample_std / np.sqrt(n),
                  sample_mean + t_critical * sample_std / np.sqrt(n))

# Bootstrap方法
boot_lower, boot_upper, boot_means = bootstrap_ci(income)

print(f"样本均值: ${sample_mean:,.2f}")
print(f"传统95% CI: (${traditional_ci[0]:,.2f}, ${traditional_ci[1]:,.2f})")
print(f"Bootstrap 95% CI: (${boot_lower:,.2f}, ${boot_upper:,.2f})")

# 可视化
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

# 原始数据分布
ax1.hist(income, bins=30, density=True, alpha=0.7, color='skyblue', edgecolor='black')
ax1.axvline(x=sample_mean, color='red', linestyle='--', linewidth=2, label=f'Mean = ${sample_mean:,.0f}')
ax1.set_xlabel('Income')
ax1.set_ylabel('Density')
ax1.set_title('Income Distribution (Right-Skewed)')
ax1.legend()
ax1.grid(True, alpha=0.3)

# Bootstrap分布
ax2.hist(boot_means, bins=50, density=True, alpha=0.7, color='lightgreen', edgecolor='black')
ax2.axvline(x=sample_mean, color='red', linestyle='--', linewidth=2, label='Sample Mean')
ax2.axvline(x=boot_lower, color='blue', linestyle=':', linewidth=2, label=f'95% CI: (${boot_lower:,.0f}, ${boot_upper:,.0f})')
ax2.axvline(x=boot_upper, color='blue', linestyle=':', linewidth=2)
ax2.set_xlabel('Bootstrap Sample Mean')
ax2.set_ylabel('Density')
ax2.set_title('Bootstrap Distribution of Mean')
ax2.legend()
ax2.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('bootstrap.png', dpi=150)
plt.show()
```

---

## 习题

### 习题1

用蒙特卡洛方法估计$\pi$的值。

**提示**：在单位正方形内随机撒点，计算落在单位圆内的比例。

```python
n_points = 1000000
x = np.random.uniform(0, 1, n_points)
y = np.random.uniform(0, 1, n_points)

inside_circle = (x**2 + y**2) <= 1
pi_estimate = 4 * np.sum(inside_circle) / n_points
print(f"π的估计值: {pi_estimate:.6f}")
```

### 习题2

验证切比雪夫不等式：$P(|X - \mu| \geq k\sigma) \leq \frac{1}{k^2}$

```python
# 对指数分布验证切比雪夫不等式
k_values = np.linspace(1, 5, 20)
empirical_probs = []
chebyshev_bounds = []

for k in k_values:
    samples = np.random.exponential(1, 100000)
    mean, std = np.mean(samples), np.std(samples)
    prob = np.mean(np.abs(samples - mean) >= k * std)
    empirical_probs.append(prob)
    chebyshev_bounds.append(1 / k**2)

plt.plot(k_values, empirical_probs, 'o-', label='Empirical')
plt.plot(k_values, chebyshev_bounds, 'r--', label='Chebyshev Bound')
plt.xlabel('k')
plt.ylabel('P(|X-μ| ≥ kσ)')
plt.legend()
plt.title("Verification of Chebyshev's Inequality")
plt.grid(True)
```

---

**适用**：docs/06-概率论与统计/
