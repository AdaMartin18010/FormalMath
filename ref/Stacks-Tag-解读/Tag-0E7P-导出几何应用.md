---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0E7P - 导出几何应用

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0E7P |
| **英文名称** | Applications of Derived Algebraic Geometry |
| **所属章节** | Derived Algebraic Geometry |
| **主题分类** | 高阶代数几何 - 导出应用 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 导出几何的统一视角

**导出代数几何**（Derived Algebraic Geometry, DAG）是代数几何的∞-范畴推广，通过引入**高阶同伦信息**，为经典代数几何中的许多问题提供了更自然的解决方案。

**核心哲学**：
> "经典代数几何中的奇点和障碍，在导出几何中成为光滑结构的一部分。"

### 2.2 导出模空间

**定义 2.2.1**（导出模函子）
对于分类问题 $\mathcal{M}$，其**导出版本**定义为：
$$\mathcal{M}^{\text{der}}: \text{dAff}^{\text{op}} \to \mathcal{S}$$
$$A \mapsto \{\text{族 }/\text{Spec}(A)\}$$
其中 $A$ 是导出（单纯）交换环。

**定义 2.2.2**（导出模空间）
**导出模空间**是表示导出模函子的**导出代数空间**或**导出叠**。

**定义 2.2.3**（切复形）
导出模空间 $\mathcal{M}$ 在点 $x$ 的**切复形**：
$$\mathbb{T}_x \mathcal{M} \in D(k)$$
编码了完整的高阶形变信息。

### 2.3 虚拟基本类

**定义 2.3.1**（完美阻碍理论）
对Deligne-Mumford叠 $M$，**完美阻碍理论**是：
$$\phi: \mathbb{E} \to \mathbb{L}_M$$
其中 $\mathbb{E}$ 是 perfect 复形，$\mathbb{L}_M$ 是余切复形。

**定义 2.3.2**（虚拟维数）
**虚拟维数**定义为：
$$\text{vdim}(M) := \text{rk}(\mathbb{E}^0) - \text{rk}(\mathbb{E}^1)$$

**定义 2.3.3**（虚拟基本类）
**虚拟基本类**定义为：
$$[M]^{\text{vir}} \in A_{\text{vdim}}(M)$$
通过导出几何自然构造：
$$[M]^{\text{vir}} = [t_0(\mathcal{M}^{\text{der}})]$$

### 2.4 导出交理论

**定义 2.4.1**（导出纤维积）
对于态射 $X \to Z \leftarrow Y$，**导出纤维积**：
$$X \times_Z^{\text{der}} Y$$
具有结构层：
$$\mathcal{O}_{X \times_Z^{\text{der}} Y} = \mathcal{O}_X \otimes_{\mathcal{O}_Z}^{\mathbb{L}} \mathcal{O}_Y$$

**定义 2.4.2**（导出正常交）
子概形 $X, Y \subset Z$ **导出正常交**如果：
$$\mathcal{O}_X \otimes_{\mathcal{O}_Z}^{\mathbb{L}} \mathcal{O}_Y$$
是完美的（即Tor-维数有限）。

**定义 2.4.3**（导出Serre交重数）
**Serre的Tor公式**的导出版本：
$$X \cdot Y = \sum_i (-1)^i \text{length}(\text{Tor}_i^{\mathcal{O}_Z}(\mathcal{O}_X, \mathcal{O}_Y))$$

---

## 3. 主要结果与定理

### 3.1 导出几何的统一应用

**定理 3.1.1**（Tag 0E7P - 导出几何应用）
导出代数几何提供以下问题的统一框架：

**(a) 模空间的奇点消解**
经典模空间的奇点在导出几何中成为光滑的导出结构。

**(b) 虚拟基本类的自然构造**
$$[M]^{\text{vir}} = t_0[\mathcal{M}^{\text{der}}]$$
自然出现于导出模空间的截断。

**(c) 形变问题的完整解**
导出形变理论提供**完整的**（obstruction-free）形变函子。

### 3.2 枚举几何应用

**定理 3.2.1**（Gromov-Witten理论）
导出几何为**稳定映射模空间**提供：

- 自然的完美阻碍理论
- 虚拟基本类
- 高亏格不变量

**定理 3.2.2**（Donaldson-Thomas理论）
导出Hilbert概形 $\text{dHilb}_X$ 是DT不变量的自然模空间：
$$\text{DT}_{\beta, n} = \int_{[\text{dHilb}]^{\text{vir}}} 1$$

**定理 3.2.3**（稳定对理论）
PT稳定对模空间是导出几何的变体，与DT理论通过**墙交叉**联系。

### 3.3 几何Langlands纲领

**定理 3.3.1**（Arinkin-Gaitsgory）
导出几何在几何Langlands纲领中提供：

- 正确的$Bun_G$（带导出结构）
- 奇异支撑条件
- 量子化的正确框架

**定理 3.3.2**（Rozenblyum）
导出$D$-模理论：
$$\text{IndCoh}_{\mathcal{N}}(\text{Loc}_G)$$
是几何Langlands对应的正确范畴。

### 3.4 形变量子化

**定理 3.4.1**（Kontsevich形变量子化）
导出几何为形变量子化提供自然框架：
$$\text{Def}_{\text{Quant}}(A) \cong \{\text{Shifted Poisson结构}\}$$

**定理 3.4.2**（因子化代数）
导出几何与顶点代数、因子化代数的联系：
$$\text{Chiral代数} \subset \text{导出D-模}$$

---

## 4. 证明思路

### 4.1 导出形变理论的框架

**步骤1**：导出环的模

- 单纯交换环的模范畴
- 稳定∞-范畴结构

**步骤2**：形变函子的导出化

- 保持拉回的正合∞-函子
- 自动编码高阶信息

**步骤3**：切复形的构造

- Goodwillie微积分
- 导出Hom的计算

### 4.2 虚拟基本类的构造

**核心观察**：
导出模空间的截断自然携带虚拟基本类。

**步骤**：

1. 构造导出模空间 $\mathcal{M}^{\text{der}}$
2. 识别截断 $t_0(\mathcal{M}^{\text{der}}) = M$
3. 验证虚拟基本类的性质

### 4.3 交理论的提升

**步骤1**：导出纤维积
$$X \times_Z^{\text{der}} Y$$

**步骤2**：证明Tor-公式的导出正确性

**步骤3**：与经典理论的兼容性

---

## 5. 应用与例子

### 5.1 GW/DT对应

**例子 5.1.1**（MNOP猜想）
对Calabi-Yau三维簇，导出几何证明：
$$Z_{\text{GW}}(q, Q) = Z_{\text{DT}}(q, Q)$$
通过导出Hilbert概形和稳定映射空间的对应。

### 5.2 镜像对称

**例子 5.1.2**（SYZ镜面对称）
导出几何为SYZ构造提供：

- 正确的Fukaya范畴（导出增强）
- 凝聚层的导出范畴
- 同调镜像对称的导出证明

### 5.3 有理曲线计数

**例子 5.1.3**
对 quintic threefold，导出几何计算：
$$n_d = \text{ degree } d \text{ 有理曲线数}$$
与镜像对称预测一致。

### 5.4 高亏格不变量

**应用 5.3.1**
导出几何使得以下计算成为可能：

- 高亏格Gromov-Witten不变量
- BCOV理论
- 拓扑弦配分函数

### 5.5 算术应用

**应用 5.3.2**（p进几何）
导出几何在算术中的应用：

- 导出p进Hodge理论
- 棱镜上同调
- 完美胚空间

### 5.6 物理应用

**应用 5.4.1**（弦理论）
导出几何对应于弦理论的：

- B-模型（导出范畴）
- D-膜（导出层）
- 稳定性条件（导出Bridgeland稳定性）

---

## 6. 与其他概念的关系

### 6.1 与经典代数几何的对比

```
    经典问题              导出解决方案
    ─────────            ─────────────
    模空间奇点     ──→    导出光滑化
    阻碍问题       ──→    同伦提升
    交重数计算     ──→    Tor-公式（自然）
    形变理论       ──→    完整形变函子
    计数问题       ──→    虚拟基本类
```

### 6.2 与高阶范畴理论

| 结构 | 经典 | 导出 |
|-----|------|------|
| 环 | 交换环 | 单纯交换环 |
| 模 | 阿贝尔群 | 链复形 |
| 层 | 阿贝尔层 | 复形的层 |
| 上同调 | 导出函子 | 内蕴 |
| 范畴 | 阿贝尔范畴 | 稳定∞-范畴 |

### 6.3 与拓扑的关系

**深刻联系**：

- 拓扑Hochschild同调（THH）
- 循环同调
- 代数K-理论

**公式**：
$$\text{THH}(R) \leadsto \text{导出几何}$$

### 6.4 与物理的关系

**弦理论字典**：

| 数学 | 物理 |
|-----|------|
| 导出范畴 $D^b(X)$ | B-模型 |
| 稳定条件 | 超对称真空 |
| 壁交叉 | 相变 |
| 虚拟基本类 | 瞬子测度 |

---

## 7. 参考文献

### 7.1 奠基文献

1. **Lurie, J.** (2009). *Higher Topos Theory*
   - Ann. of Math. Studies
   - ∞-范畴基础

2. **Lurie, J.** (2011-2014). *Derived Algebraic Geometry* I-X
   - 系统发展

3. **Toën, B., Vezzosi, G.** (2008). *Homotopical Algebraic Geometry II*
   - 导出叠

### 7.2 应用文献

1. **Pandharipande, R., Thomas, R.P.** (2014). *13/2 ways of counting curves*
   - 枚举几何综述

2. **Arinkin, D., Gaitsgory, D.** (2015). *Singular support of coherent sheaves*
   - 几何Langlands

3. **Toën, B.** (2014). *Derived algebraic geometry*
   - EMS Surveys

### 7.3 物理应用

1. **Costello, K.** (2011). *Renormalization and Effective Field Theory*
   - 导出几何与量子场论

2. **Kapranov, M.** (2015). *Supergeometry in mathematics and physics*
   - 导出几何的物理动机

### 7.4 综述与在线资源

1. **Stacks Project**: [Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
2. **DAG Seminar**: 导出代数几何系列讲座

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0E7N](#tag-0e7n) | 导出Hilbert概形 | 具体例子 |
| [0A9K](#tag-0a9k) | 导出形变理论 | 理论基础 |
| [0A5M](#tag-0a5m) | 稳定无穷范畴 | 基础 |

### 8.2 枚举几何

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G74](#tag-0g74) | Gromov-Witten | 应用 |
| [0G75](#tag-0g75) | Donaldson-Thomas | 应用 |
| [0G76](#tag-0g76) | 稳定对 | 应用 |

### 8.3 相关领域

| Tag | 主题 | 说明 |
|-----|------|------|
| [0G77](#tag-0g77) | 几何Langlands | 应用 |
| [0G78](#tag-0g78) | 镜像对称 | 应用 |
| [0A5N](#tag-0a5n) | 环谱 | 技术 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **21世纪代数几何的核心**：导出几何已渗透所有分支

2. **枚举几何的革命**：GW、DT、PT理论的基础

3. **物理联系**：弦理论、量子场论的数学基础

4. **活跃前沿**：几何Langlands、棱镜上同调、THH

### A.2 待解决问题

- **完全的几何Langlands对应**
- **导出几何的算术应用**
- **高维簇的完整枚举理论**
- **与K-理论的精确联系**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 单纯交换环 | 🔄 进行中 | ★★★★☆ |
| 稳定∞-范畴 | ❌ 待建设 | ★★★★★ |
| 导出概形 | ❌ 待建设 | ★★★★★ |
| 导出模空间 | ❌ 待建设 | ★★★★★ |
| 虚拟基本类 | ❌ 待建设 | ★★★★★ |
| 具体计算 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
