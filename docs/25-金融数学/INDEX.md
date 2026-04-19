---
title: "金融数学与工程"
msc_primary: 91

msc_secondary: ['60H10', '60J60', '91B25', '91G20']
prerequisites: ['随机过程', '微分方程', '概率论', '数值方法']
processed_at: '2026-04-08'
---

# 金融数学与工程 (Mathematical Finance and Engineering)

**最后更新**: 2026年4月8日  
**MSC分类**: @ (数理金融)  
**课程对齐**: MIT 18.642, Columbia MATH STATS W4291, Stanford MATH 238

---

## 目录结构

### 核心内容

| 文档 | 内容概要 | MSC编码 |
|------|----------|---------|
| [01-随机分析基础](./01-随机分析基础-完整版.md) | 布朗运动、伊藤引理、SDE | 60H10 |
| [02-期权定价理论](./02-期权定价理论-完整版.md) | Black-Scholes、风险中性定价 | 91G20 |
| [03-利率模型](./03-利率模型-完整版.md) | Vasicek、CIR、HJM框架 | 91G30 |
| [04-风险管理](./04-风险管理-完整版.md) | VaR、CVaR、极值理论 | 91G40 |
| [05-衍生品定价](./05-衍生品定价-完整版.md) | 期货、互换、结构化产品 | 91G20 |
| [06-数值方法](./06-数值方法-完整版.md) | 蒙特卡洛、有限差分、树方法 | 91G60 |

### 应用案例库

| 案例 | 应用场景 | 数学工具 |
|------|----------|----------|
| [案例01-欧式期权定价](./cases/01-欧式期权定价.md) | 衍生品交易 | Black-Scholes |
| [案例02-投资组合优化](./cases/02-投资组合优化.md) | 资产管理 | 均值-方差 |
| [案例03-风险价值计算](./cases/03-风险价值计算.md) | 风控 | 极值理论 |
| [案例04-利率衍生品](./cases/04-利率衍生品.md) | 固收 | Hull-White |
| [案例05-外汇对冲策略](./cases/05-外汇对冲策略.md) | 跨国公司 | 随机分析 |

---

## 学习路径

### 基础路径
```
概率论 → 随机过程 → 布朗运动 → 伊藤引理 → 期权定价
```

### 进阶路径
```
Black-Scholes → 利率模型 → 信用风险 → 数值方法
```

### 应用路径
- **量化交易**: 统计套利 + 高频模型 + 机器学习
- **风险管理**: 风险度量 + 压力测试 + 组合优化
- **衍生品定价**: 模型校准 + 希腊字母 + 对冲策略

---

## 核心定理速查

| 定理/公式 | 描述 | 应用 |
|-----------|------|------|
| **伊藤引理** | $df = f_t dt + f_x dX + \frac{1}{2}f_{xx}dt$ | SDE求解 |
| **Black-Scholes** | $\frac{\partial V}{\partial t} + rS\frac{\partial V}{\partial S} + \frac{1}{2}\sigma^2S^2\frac{\partial^2 V}{\partial S^2} = rV$ | 期权定价 |
| **Girsanov定理** | 测度变换 | 风险中性定价 |
| **Feynman-Kac** | PDE与期望的等价 | 数值计算 |

---

## 模型对比

| 模型 | 假设 | 优点 | 局限 |
|------|------|------|------|
| B-S | 对数正态、恒定波动率 | 解析解 | 波动率微笑 |
| 局部波动率 | $\sigma(S,t)$ | 校准市场 | 无动态 |
| 随机波动率 | $dV = ...$ | 波动率微笑 | 复杂 |
| 跳跃扩散 | 泊松跳跃 | 极端事件 | 参数多 |

---

## 参考资源

### 教材
- Shreve, *Stochastic Calculus for Finance I & II*
- Björk, *Arbitrage Theory in Continuous Time*
- Glasserman, *Monte Carlo Methods in Financial Engineering*

### 在线课程
- MIT 18.642: Continuous-Time Financial Mathematics
- Coursera: Financial Engineering and Risk Management (Columbia)

---

**维护者**: FormalMath应用数学组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
