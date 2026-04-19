---
msc_primary: 00

  - 00A99
title: 数学×语言学：计算语言学的统计模型
processed_at: '2026-04-05'
---
# 数学×语言学：计算语言学的统计模型

## 概述

计算语言学运用统计学和机器学习方法来处理和分析自然语言数据。从n-gram语言模型到神经机器翻译，从隐马尔可夫模型到Transformer架构，数学和计算工具推动了自然语言处理的革命性发展。

---

## 核心思维导图

```mermaid
mindmap
  root((计算语言学<br/>Computational Linguistics))
    统计语言模型
      N-gram模型
        马尔可夫假设
        最大似然估计
        平滑技术
      神经网络LM
        前馈网络
        循环网络
        LSTM/GRU
      Transformer
        自注意力
        位置编码
        BERT/GPT
      评估指标
        困惑度
        交叉熵
        BLEU/ROUGE
    词表示学习
      分布式假设
        上下文预测
        共现矩阵
        语义空间
      Word2Vec
        CBOW
        Skip-gram
        负采样
      GloVe
        全局向量
        矩阵分解
        加权最小二乘
      上下文嵌入
        ELMo
        BERT
        动态表示
    句法分析
      上下文无关分析
        CKY算法
        动态规划
        概率CFG
      依存分析
        图算法
        转移系统
        神经网络
      成分分析
        Chart分析
        特征统一
        统计解析
    语义计算
      词义消歧
        监督学习
        向量空间
        图方法
      语义角色标注
        谓词论元
        分类器
        序列标注
      文本蕴含
        自然语言推理
        注意力机制
        预训练微调
      语义解析
        λ演算
        SQL生成
        知识库查询
    机器翻译
      统计机器翻译
        IBM模型
        短语模型
        层次短语
      神经机器翻译
        编码器-解码器
        注意力机制
        Transformer
      无监督翻译
        单语数据
        回译
        共享空间
    语音识别合成
      声学模型
        HMM-GMM
        DNN-HMM
        端到端
      语言模型
        N-gram
        RNN
        Transformer
      语音合成
        拼接合成
        参数合成
        神经网络

```

---

## 语言模型发展

```mermaid
graph TD
    subgraph 统计模型
        N[N-gram] --> S[平滑方法]
        S --> K[Kneser-Ney]
    end
    
    subgraph 神经网络
        NN[NNLM] --> RNN[RNNLM]
        RNN --> LSTM[LSTM/GRU]
        LSTM --> ATT[Seq2Seq+Attention]
    end
    
    subgraph Transformer时代
        TR[Transformer] --> B[BERT]
        TR --> G[GPT]
        B --> L[大规模预训练]
        G --> L
    end
    
    K -.-> NN
    LSTM -.-> TR
    
    style TR fill:#e3f2fd
    style B fill:#e8f5e9
    style G fill:#fff3e0

```

---

## 词嵌入方法对比

| 方法 | 训练目标 | 上下文定义 | 特点 |
|------|----------|------------|------|
| Word2Vec(CBOW) | 上下文预测中心词 | 窗口 | 高效、局部 |
| Word2Vec(Skip-gram) | 中心词预测上下文 | 窗口 | 罕见词友好 |
| GloVe | 共现矩阵重构 | 全局 | 融合全局统计 |
| FastText | 子词预测 | 窗口+子词 | OOV处理 |
| BERT | 掩码语言模型 | 双向上下文 | 上下文相关 |
| ELMo | 双向LM | 整句 | 多层表示 |

---

## Transformer架构

```mermaid
mindmap
  root((Transformer架构))
    自注意力机制
      缩放点积注意力
        Q, K, V矩阵
        Attention = softmax(QKᵀ/√d)V
        并行计算
      多头注意力
        多子空间投影
        h=8 or 16
        拼接+线性变换
      自注意力
        每个位置关注所有位置
        捕获长距离依赖
        可解释性
    位置编码
      正弦编码
        PE(pos,2i) = sin(pos/10000^(2i/d))
        PE(pos,2i+1) = cos(...)
        外推性
      可学习编码
        位置嵌入
        固定长度
    前馈网络
      位置前馈
        FFN(x) = max(0, xW₁+b₁)W₂+b₂
        独立处理每个位置
      残差连接
        LayerNorm(x + Sublayer(x))
        梯度传播
    应用
      编码器(BERT)
        双向上下文
        掩码LM
        下游任务微调
      解码器(GPT)
        单向生成
        自回归
        因果掩码
      编码器-解码器(T5)
        翻译/摘要
        前缀LM

```

---

## 前沿方向

- **多模态学习**: 视觉-语言预训练
- **知识增强**: 符号知识注入
- **因果NLP**: 因果推断与反事实
- **低资源学习**: 跨语言迁移、元学习
- **可解释性**: 注意力分析、探测任务

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数学×语言学 / 交叉学科*
