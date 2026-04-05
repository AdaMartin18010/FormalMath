---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 深度学习 - 思维导图
processed_at: '2026-04-05'
---
# 深度学习 - 思维导图

## 概述

深度学习是机器学习的重要分支，通过多层神经网络学习数据的层次化表示。从多层感知机到卷积神经网络、循环神经网络，再到Transformer架构，深度学习在计算机视觉、自然语言处理等领域取得了突破性进展，其数学基础涉及优化理论、线性代数和概率图模型。

---

## 核心思维导图

```mermaid
mindmap
  root((深度学习<br/>Deep Learning))
    神经网络基础
      感知机
        线性分类器
        激活函数
      多层网络
        前向传播
        反向传播
        链式法则
      激活函数
        ReLU
        Sigmoid
        Tanh
        Softmax
    网络架构
      CNN
        卷积层
        池化层
        全连接
        经典网络
      RNN
        序列建模
        LSTM
        GRU
        注意力
      Transformer
        Self-Attention
        多头注意力
        位置编码
        BERT/GPT
    训练技术
      优化器
        SGD
        Momentum
        Adam
        学习率
      正则化
        Dropout
        Batch Norm
        数据增强
      初始化
        Xavier
        He
    理论分析
      表达能力
        万能逼近
        深度优势
      优化景观
        局部极小
        鞍点
        平坦极小

```

---

## 神经网络前向与反向传播

```mermaid
graph TD
    subgraph 前向传播
        A[x] --> B[z¹ = W¹x + b¹]
        B --> C[a¹ = σ(z¹)]
        C --> D[z² = W²a¹ + b²]
        D --> E[ŷ = σ(z²)]
        E --> F[L(ŷ,y)]
    end
    
    subgraph 反向传播
        F --> G[∂L/∂z²]
        G --> H[∂L/∂W² = ∂L/∂z² · a¹ᵀ]
        G --> I[∂L/∂a¹ = W²ᵀ∂L/∂z²]
        I --> J[∂L/∂z¹ = ∂L/∂a¹ ⊙ σ'(z¹)]
        J --> K[∂L/∂W¹ = ∂L/∂z¹ · xᵀ]
    end
    
    style F fill:#e3f2fd
    style H fill:#fff3e0
    style J fill:#e8f5e9

```

---

## 主要架构对比

```mermaid
mindmap
  root((网络架构))
    CNN
      核心操作
        卷积: 局部连接
        权值共享
        平移等变
      经典网络
        LeNet-5
        AlexNet
        VGGNet
        ResNet
        EfficientNet
      应用
        图像分类
        目标检测
        语义分割
    RNN/LSTM
      循环结构
        隐藏状态
        时序依赖
      LSTM改进
        门控机制
        遗忘门
        解决梯度消失
      应用
        语言建模
        机器翻译
        语音识别
    Transformer
      Attention机制
        Q,K,V计算
        缩放点积
      架构
        Encoder-Decoder
        多头注意力
        前馈网络
      代表模型
        BERT
        GPT系列
        T5

```

---

## 优化技术对比

| 技术 | 目的 | 方法 | 效果 |
|------|------|------|------|
| Dropout | 防止过拟合 | 随机失活神经元 | 正则化 |
| Batch Norm | 加速训练 | 层归一化 | 稳定分布 |
| Layer Norm | 稳定训练 | 特征归一化 | Transformer必备 |
| 残差连接 | 训练深层 | Skip connection | 解决退化 |
| 数据增强 | 扩充数据 | 变换样本 | 提高泛化 |
| 早停 | 防止过拟合 | 验证集监控 | 节省计算 |

---

## 训练动力学

```mermaid
graph TD
    subgraph 损失景观
        A[高维非凸] --> B[局部极小]
        A --> C[鞍点]
        A --> D[平坦极小]
    end
    
    subgraph 优化挑战
        E[梯度消失] --> F[深层网络]
        G[梯度爆炸] --> H[梯度裁剪]
        I[局部极小] --> J[随机初始化]
    end
    
    subgraph 解决方案
        K[ReLU] --> L[缓解消失]
        M[残差连接] --> N[直接梯度流]
        O[Batch Norm] --> P[稳定训练]
    end
    
    style B fill:#e3f2fd
    style D fill:#fff3e0
    style N fill:#e8f5e9

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[感知机] --> B[多层感知机]
        B --> C[反向传播]
    end
    
    subgraph L2[架构]
        C --> D[CNN]
        D --> E[RNN/LSTM]
        E --> F[Transformer]
    end
    
    subgraph L3[训练]
        F --> G[优化器]
        G --> H[正则化]
    end
    
    subgraph L4[高级]
        H --> I[生成模型]
        I --> J[GAN/VAE]
        J --> K[自监督学习]
    end
    
    style D fill:#e3f2fd
    style F fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $z^{[l]} = W^{[l]}a^{[l-1]} + b^{[l]}$ | 线性变换 |
| $a^{[l]} = g(z^{[l]})$ | 激活函数 |
| $\delta^{[l]} = (W^{[l+1]})^T\delta^{[l+1]} \odot g'(z^{[l]})$ | 误差反向传播 |
| $\text{Attention}(Q,K,V) = \text{softmax}(\frac{QK^T}{\sqrt{d_k}})V$ | 缩放点积注意力 |
| $\hat{x} = \frac{x-\mu_B}{\sqrt{\sigma_B^2+\epsilon}}$ | Batch Normalization |

---

## 应用领域

- **计算机视觉**: 图像生成、风格迁移
- **自然语言处理**: 大语言模型、对话系统
- **自动驾驶**: 感知、决策
- **医疗影像**: 疾病诊断、分割
- **游戏AI**: AlphaGo、强化学习

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 数据科学 / 思维导图*
