---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 并行计算 - 思维导图
processed_at: '2026-04-05'
---
# 并行计算 - 思维导图

## 概述

并行计算是利用多个处理单元同时执行任务以加速计算的技术。随着单核性能提升放缓和大数据、人工智能应用的兴起，并行计算已成为现代科学计算和工程仿真的必需技术，涵盖从多核CPU到GPU、从集群到云计算的多种计算模式。

---

## 核心思维导图

```mermaid
mindmap
  root((并行计算<br/>Parallel Computing))
    并行架构
      共享内存
        多核CPU
        OpenMP
        线程级并行
      分布式内存
        集群
        MPI
        进程级并行
      异构计算
        GPU
        CUDA/OpenCL
        加速器
      云计算
        弹性资源
        容器化
    并行算法
      分解策略
        域分解
        功能分解
        任务分解
      通信模式
        点到点
        集合通信
        全局操作
      负载均衡
        静态分配
        动态调度
      可扩展性
        强可扩展
        弱可扩展
    性能分析
      加速比
        Amdahl定律
        Gustafson定律
      效率
        并行效率
        开销分析
      瓶颈
        通信
        同步
        负载不均
    数值方法并行化
      线性代数
        矩阵分解
        迭代法
      网格计算
        CFD
        FEM
      蒙特卡洛
         embarrassingly并行

```

---

## 并行架构对比

```mermaid
graph TD
    subgraph 共享内存
        A[多核处理器] --> B[OpenMP]
        B --> C[线程]<-->D[共享地址空间]
    end
    
    subgraph 分布式内存
        E[计算节点集群] --> F[MPI]
        F --> G[进程]<-->H[显式通信]
    end
    
    subgraph 异构计算
        I[CPU+GPU] --> J[CUDA/OpenCL]
        J --> K[主机+设备]
        K --> L[数据转移]
    end
    
    style B fill:#e3f2fd
    style F fill:#fff3e0
    style J fill:#e8f5e9

```

---

## 编程模型对比

| 模型 | 内存 | 编程复杂度 | 适用规模 | 典型应用 |
|------|------|------------|----------|----------|
| OpenMP | 共享 | 低 | 多核(10-100) | 循环并行 |
| MPI | 分布式 | 高 | 大规模(1K-1M) | 集群计算 |
| CUDA | 异构 | 中 | GPU加速 | 数据并行 |
| OpenACC | 异构 | 低 | GPU加速 | 指令加速 |
| PGAS | 混合 | 中 | 大规模 | 全局地址 |

---

## 并行算法设计

```mermaid
mindmap
  root((并行算法))
    分解策略
      域分解
        网格分区
        边界通信
      任务分解
        任务图
        依赖分析
      流水线
        流水级
        重叠计算
    通信模式
      集合操作
        Broadcast
        Reduce
        Allreduce
        Alltoall
      同步点
        Barrier
        全局一致性
    负载均衡
      静态
        块划分
        循环划分
      动态
        任务队列
        工作窃取
    粒度
      粗粒度
        低开销
        低并行度
      细粒度
        高并行度
        高开销

```

---

## 性能定律

```mermaid
graph TD
    subgraph Amdahl定律
        A[固定问题规模] --> B[加速比 ≤ 1/(s + p/N)]
        B --> C[s:串行比例<br/>p:并行比例]
        C --> D[极限加速: 1/s]
    end
    
    subgraph Gustafson定律
        E[可扩展问题] --> F[加速比 ≈ N - s(N-1)]
        F --> G[随N线性增长]
    end
    
    subgraph 实际因素
        H[通信开销] --> I[延迟+带宽]
        J[负载不均衡] --> K[等待时间]
        L[同步开销] --> M[Barrier等待]
    end
    
    style B fill:#e3f2fd
    style F fill:#fff3e0

```

---

## 数值算法并行化

```mermaid
mindmap
  root((数值并行))
    稠密线性代数
      矩阵乘法
        Cannon算法
        SUMMA
      分解
        并行LU
        并行QR
    稀疏矩阵
      迭代法
        稀疏MV并行
        预处理并行
      代数多重网格
        粗网格并行
    网格计算
      CFD
        域分解
        隐式求解
      FEM
        矩阵组装
        并行求解器
    粒子方法
      MD
        短程力
        近邻表
      长程力
        FMM
        快速多极子

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[并行架构] --> B[Flynn分类]
        B --> C[存储层次]
    end
    
    subgraph L2[编程]
        C --> D[OpenMP]
        D --> E[MPI]
        E --> F[GPU编程]
    end
    
    subgraph L3[算法]
        F --> G[分解策略]
        G --> H[负载均衡]
    end
    
    subgraph L4[优化]
        H --> I[性能分析]
        I --> J[可扩展性]
        J --> K[混合并行]
    end
    
    style E fill:#e3f2fd
    style G fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $S(N) = \frac{T_1}{T_N} \leq \frac{1}{s + \frac{1-s}{N}}$ | Amdahl加速比 |
| $S(N) = N - s(N-1)$ | Gustafson加速比 |
| $E(N) = \frac{S(N)}{N}$ | 并行效率 |
| $T_{total} = T_{comp} + T_{comm} + T_{sync}$ | 总时间分解 |
| $T_{comm} = \alpha + \beta \cdot M$ | 通信时间模型 |

---

## 应用领域

- **气候模拟**: 全球气候模型(GCM)
- **分子动力学**: 材料科学、药物设计
- **人工智能**: 深度学习训练
- **计算流体力学**: 飞机设计、气象预测
- **天体物理**: 宇宙学模拟
- **基因组学**: 序列比对、变异检测

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 计算数学 / 思维导图*
