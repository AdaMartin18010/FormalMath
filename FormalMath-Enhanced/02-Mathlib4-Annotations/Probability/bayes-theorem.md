---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 贝叶斯定理 (Bayes' Theorem)
---
# 贝叶斯定理 (Bayes' Theorem)

## Mathlib4 引用

```lean
import Mathlib.Probability.ConditionalProbability

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBpos : 0 < P B)

/-- 贝叶斯定理：在已知 B 发生的条件下 A 的条件概率
    可以用 A 发生时 B 的条件概率和各自的先验概率表示 -/
theorem bayes_theorem :
    P[A|B] = P[B|A] * P A / P B := by
  -- 由条件概率的定义 P[A|B] = P(A ∩ B) / P(B) 直接推导
  sorry

end ProbabilityTheory
```

## 数学背景

贝叶斯定理由英国牧师和数学家托马斯·贝叶斯（Thomas Bayes）在18世纪提出，发表于1763年。该定理革命性地将条件概率的计算方向进行了逆转：从 P(B|A) 推导 P(A|B)。这一思想构成了贝叶斯统计学的基石，对科学推理、机器学习、医学诊断和人工智能产生了深远影响。

## 直观解释

贝叶斯定理可以用一个医学检测的例子来理解：假设某种疾病在人群中的患病率是 1%%（先验概率），检测的准确率是 99%%。如果一个人检测呈阳性，他实际患病的概率是多少？直觉上可能会认为是 99%%，但贝叶斯定理告诉我们答案要低得多（约 50%%），因为疾病本身很罕见，假阳性的数量可能超过真阳性。

## 形式化表述

设 $A$ 和 $B$ 是两个事件，$P(B) > 0$，则：

$$P(A|B) = \frac{{P(B|A) \cdot P(A)}}{{P(B)}}$$

若 $\{A_1, A_2, \dots, A_n\}$ 构成样本空间的一个划分，则全概率公式给出：

$$P(B) = \sum_{{i=1}}^n P(B|A_i) \cdot P(A_i)$$

因此贝叶斯定理也可写成：

$$P(A_j|B) = \frac{{P(B|A_j) \cdot P(A_j)}}{{\sum_{{i=1}}^n P(B|A_i) \cdot P(A_i)}}$$

其中：

- $P(A|B)$ 称为后验概率（观察到 $B$ 后 $A$ 的概率）
- $P(A)$ 称为先验概率（观察 $B$ 前 $A$ 的概率）
- $P(B|A)$ 称为似然（$A$ 发生时观察到 $B$ 的概率）

## 证明思路

1. **条件概率定义**：$P(A|B) = P(A \cap B) / P(B)$ 和 $P(B|A) = P(A \cap B) / P(A)$
2. **联合概率等价**：两个表达式中的 $P(A \cap B)$ 相同
3. **代入整理**：将 $P(A \cap B) = P(B|A) \cdot P(A)$ 代入第一个等式
4. **全概率公式**：当需要计算 $P(B)$ 时，利用划分 $\{A_i\}$ 和全概率公式展开

核心洞察在于新证据的作用是通过似然比来更新先验信念。

## 示例

### 示例 1：医学检测

设疾病患病率 $P(D) = 0.01$，检测灵敏度 $P(T+|D) = 0.99$，特异度 $P(T-|[la] D) = 0.99$。则：
$$P(D|T+) = \frac{{0.99 \times 0.01}}{{0.99 \times 0.01 + 0.01 \times 0.99}} = 0.5$$
即检测阳性者实际患病的概率只有 50%%。

### 示例 2：垃圾邮件过滤

设某词在垃圾邮件中出现的概率为 5%%，在正常邮件中为 1%%，垃圾邮件占收件箱的 40%%。则包含该词的邮件是垃圾邮件的概率为 $(0.05 \times 0.4) / (0.05 \times 0.4 + 0.01 \times 0.6) \approx 0.769$。

### 示例 3：法庭证据

某 DNA 证据在嫌疑人无罪时匹配的概率为百万分之一。若该城市有 100 万人，根据贝叶斯定理，即使 DNA 匹配，嫌疑人实际有罪的概率也需考虑其他证据，不能仅由匹配概率推断。

## 应用

- **机器学习**：朴素贝叶斯分类器、贝叶斯网络和概率图模型
- **医学诊断**：基于症状和检测结果的疾病概率推断
- **信息检索**：垃圾邮件过滤、搜索引擎排序和推荐系统
- **金融风险管理**：信用评分、欺诈检测和投资决策
- **人工智能**：贝叶斯优化、强化学习和不确定性量化

## 相关概念

- 条件概率 (Conditional Probability)：在已知某事件发生条件下另一事件的概率
- 全概率公式 (Law of Total Probability)：通过划分计算无条件概率
- 先验概率 (Prior Probability)：观察证据前对假设的概率评估
- 后验概率 (Posterior Probability)：观察证据后对假设的更新概率
- 贝叶斯推断 (Bayesian Inference)：基于贝叶斯定理的统计推断框架

## 参考

### 教材

- [D. Koller, N. Friedman. Probabilistic Graphical Models. MIT Press, 2009. Chapter 2]
- [E. T. Jaynes. Probability Theory: The Logic of Science. Cambridge, 2003. Chapter 4]

### 历史文献

- [T. Bayes. An Essay towards solving a Problem in the Doctrine of Chances. 1763]

### 在线资源

- [Mathlib4 - ConditionalProbability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*