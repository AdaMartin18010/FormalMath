---
msc_primary: "62Rxx"
msc_secondary: ['68Txx', '62Hxx', '68Qxx']
---

# 数据科学 / Data Science

**最后更新**: 2026年4月4日

---

## 📋 分支概述

数据科学是应用数学、统计学和计算机科学的交叉学科，致力于从数据中提取知识和洞察。核心内容包括统计学习理论、机器学习算法、降维技术、深度学习数学基础等。数据科学为人工智能、大数据分析、模式识别等领域提供了严格的数学理论支撑。

---

## 📁 文档索引

| 文档 | 内容 | MSC分类 | 参考著作 |
|------|------|---------|----------|
| [01-基础概念](./01-基础概念.md) | 统计学习理论、降维方法、深度学习数学 | 62Rxx, 68Txx | Hastie & Tibshirani |
| [02-核心定理](./02-核心定理.md) | VC维理论、通用近似定理 | 68Q32, 41A30 | Vapnik |
| [03-实战问题](./03-实战问题.md) | 10个数据科学问题 | 62Rxx, 68Txx | Bishop |

---

## 🎯 理论架构

```

数据科学
├── 统计学习理论
│   ├── 泛化理论
│   ├── VC维与Rademacher复杂度
│   ├── 偏差-方差分解
│   ├── 正则化理论
│   └── 模型选择
├── 监督学习
│   ├── 线性模型与岭回归
│   ├── 核方法与支持向量机
│   ├── 决策树与集成方法
│   ├── 神经网络
│   └── 贝叶斯方法
├── 无监督学习
│   ├── 主成分分析(PCA)
│   ├── 聚类算法
│   ├── 流形学习
│   ├── 因子分析
│   └── 生成模型
├── 深度学习
│   ├── 前馈网络
│   ├── 反向传播算法
│   ├── 优化理论
│   ├── 卷积网络
│   └── 循环网络
└── 高维统计
    ├── 稀疏恢复
    ├── 压缩感知
    ├── 随机矩阵理论
    └── 高维概率

```

---

## 📚 核心人物

- **Ronald A. Fisher (1890-1962)**: 现代统计学奠基人，最大似然、方差分析
- **Vladimir Vapnik (1936-) & Alexey Chervonenkis**: VC理论、支持向量机
- **Geoffrey Hinton (1947-)**: 深度学习先驱，反向传播、玻尔兹曼机
- **Yann LeCun (1960-)**: 卷积神经网络、计算机视觉
- **Yoshua Bengio (1964-)**: 深度学习理论、表示学习
- **Trevor Hastie, Robert Tibshirani, Jerome Friedman**: 统计学习要素

---

## 🔗 与其他分支的联系

- **概率论与统计**: 统计推断、假设检验、贝叶斯理论
- **优化理论**: 凸优化、随机优化、梯度方法
- **线性代数**: 矩阵分解、特征值计算、子空间方法
- **泛函分析**: 再生核希尔伯特空间、算子理论
- **信息论**: 熵、互信息、KL散度
- **计算复杂性**: 学习算法的计算理论

---

## 📖 学习路径建议

1. **先修知识**: 线性代数、概率统计、优化基础
2. **第一阶段**: 经典统计方法（回归、分类）
3. **第二阶段**: 统计学习理论（泛化、正则化）
4. **第三阶段**: 核方法与SVM
5. **第四阶段**: 深度学习与高维统计

---

## 📖 国际标准对齐

本分支内容严格遵循国际数学界标准，与以下经典教材完全对齐：

- **Trevor Hastie, Robert Tibshirani & Jerome Friedman** - *The Elements of Statistical Learning* (2nd Edition, 2009)
- **Vladimir N. Vapnik** - *Statistical Learning Theory* (1998)
- **Christopher M. Bishop** - *Pattern Recognition and Machine Learning* (2006)
- **Shai Shalev-Shwartz & Shai Ben-David** - *Understanding Machine Learning: From Theory to Algorithms* (2014)
- **Ian Goodfellow, Yoshua Bengio & Aaron Courville** - *Deep Learning* (2016)

---

*最后更新：2026年4月*
