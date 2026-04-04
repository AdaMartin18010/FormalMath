---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# SIR模型 - 思维导图

## 概述

SIR模型是流行病学中最经典的仓室模型，由Kermack和McKendrick于1927年提出。该模型将人群分为易感者(Susceptible)、感染者(Infected)和康复者(Recovered)三个仓室，通过常微分方程描述传染病的传播动力学，是公共卫生决策的重要理论工具。

---

## 核心思维导图

```mermaid
mindmap
  root((SIR模型<br/>SIR Model))
    基本模型
      仓室定义
        S: 易感者
          可被感染
          初始比例
        I: 感染者
          具有传染性
          感染期
        R: 康复者
          永久免疫
          移除仓室
      动态方程
        dS/dt = -βSI/N
        dI/dt = βSI/N - γI
        dR/dt = γI
      参数解释
        β: 传染率
          接触率 × 传播概率
        γ: 恢复率
          1/平均感染期
    基本再生数R₀
      定义
        一个感染者平均传染人数
        R₀ = β/γ
      阈值行为
        R₀ > 1: 疫情爆发
        R₀ < 1: 疫情消退
       herd免疫
        免疫阈值 = 1 - 1/R₀
    动力学分析
      最终规模
        总感染比例
        超越方程
      峰值分析
        感染峰值时间
        峰值高度
      时间尺度
        倍增时间
        衰减时间
    模型扩展
      SEIR
        暴露期E
        潜伏期建模
      SIRS
        暂时免疫
        重返易感
      空间结构
        网络传播
        元种群

```

---

## SIR模型结构

```mermaid
graph LR
    subgraph 仓室流动
        A[S<br/>易感者] -->|感染率<br/>βSI/N| B[I<br/>感染者]
        B -->|恢复率<br/>γI| C[R<br/>康复者]

    end
    
    subgraph 参数
        D[β: 传染率] --> E[接触 × 传播]
        F[γ: 恢复率] --> G[1/感染期]
    end
    
    subgraph 再生数
        H[R₀ = β/γ] --> I[R₀>1:爆发]
        H --> J[R₀<1:消退]
    end
    
    style A fill:#e3f2fd
    style B fill:#ffcdd2
    style C fill:#e8f5e9
    style H fill:#fff3e0

```

---

## 动力学分析

```mermaid
mindmap
  root((SIR动力学))
    相平面分析
      S-I平面
        轨道结构
        单调性
      不变量
        S + I + R = N
        守恒关系
    最终规模方程
      形式
        R∞ = 1 - exp(-R₀·R∞)
      含义
        最终感染比例
        超越方程
      近似
        R∞ ≈ 2(R₀-1)/R₀
        小R₀-1展开
    感染峰值
      峰值条件
        dI/dt = 0
        S* = 1/R₀
      峰值高度
        Imax与R₀关系
      峰值时间
        数值计算
        近似公式
    时间演化
      早期指数增长
        I(t) ~ exp((R₀-1)γt)
      后期指数衰减
        I(t) ~ exp(-γt)

```

---

## 模型变体对比

| 模型 | 结构 | 适用疾病 | 特征 |
|------|------|----------|------|
| SI | S → I | 无免疫(如HIV慢性期) | 所有人终将被感染 |
| SIR | S → I → R | 永久免疫(如麻疹) | 经典模型 |
| SIRS | S → I → R → S | 暂时免疫(如流感) | 周期性流行 |
| SEIR | S → E → I → R | 有潜伏期(如新冠) | 暴露期延迟 |
| SEIRS | S → E → I → R → S | 复杂传播 | 最一般形式 |

---

## 干预措施建模

```mermaid
graph TD
    subgraph 非药物干预
        A[社交距离] --> B[降低β]
        C[隔离] --> D[加速γ]
        E[戴口罩] --> F[降低传播概率]
    end
    
    subgraph 疫苗接种
        G[接种率p] --> H[直接保护]
        G --> I[群体免疫]
        H --> J[有效R = R₀(1-p)]
    end
    
    subgraph 控制目标
        K[压平曲线] --> L[降低峰值]
        M[消灭疫情] --> N[R < 1]
    end
    
    style B fill:#e3f2fd
    style I fill:#fff3e0
    style N fill:#e8f5e9

```

---

## 随机扩展

```mermaid
mindmap
  root((随机SIR))
    分支过程
      Galton-Watson
        早期爆发
        灭绝概率
      超临界
        R₀ > 1
        有限灭绝概率
      次临界
        R₀ < 1
        必然灭绝
    随机模拟
      Gillespie算法
        事件驱动
        精确模拟
      链式二项模型
        离散时间
        接触过程
    波动效应
      随机灭绝
        小种群
        波动重要性
      超扩散
        异质性传播
        超级传播者

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[SIR方程] --> B[R₀概念]
        B --> C[平衡点分析]
    end
    
    subgraph L2[动力学]
        C --> D[最终规模]
        D --> E[峰值分析]
    end
    
    subgraph L3[扩展]
        E --> F[SEIR模型]
        F --> G[SIRS模型]
        G --> H[空间扩展]
    end
    
    subgraph L4[应用]
        H --> I[干预策略]
        I --> J[数据拟合]
        J --> K[预测模型]
    end
    
    style B fill:#e3f2fd
    style I fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $\frac{dS}{dt} = -\frac{\beta SI}{N}$ | 易感者变化 |
| $\frac{dI}{dt} = \frac{\beta SI}{N} - \gamma I$ | 感染者变化 |
| $R_0 = \frac{\beta}{\gamma}$ | 基本再生数 |
| $S_c = \frac{\gamma}{\beta} = \frac{1}{R_0}$ | 临界易感比例 |
| $R_\infty = 1 - e^{-R_0 R_\infty}$ | 最终规模方程 |
| $I_{max} = 1 - \frac{1 + \ln R_0}{R_0}$ | 感染峰值近似 |
| $p_c = 1 - \frac{1}{R_0}$ | 临界接种比例 |

---

## 实际应用

- **COVID-19**: 基本再生数估计、封锁策略评估
- **流感**: 季节性预测、疫苗接种规划
- **HIV/AIDS**: 多群体传播模型、干预效果评估
- **麻疹**: 群体免疫阈值计算、疫苗覆盖率目标
- **埃博拉**: 紧急响应、隔离策略优化

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 生物数学 / 思维导图*
