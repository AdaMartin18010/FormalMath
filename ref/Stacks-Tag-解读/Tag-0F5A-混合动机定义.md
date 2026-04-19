---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0F5A - 混合动机定义

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0F5A |
| **英文名称** | Definition of Mixed Motives |
| **所属章节** | Motives |
| **主题分类** | 代数几何 - 动机理论 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 动机的哲学

**动机**（Motive）是代数几何中最深刻的概念之一，源于Grothendieck的远见：存在一个「通用」的上同调理论，所有其他上同调理论都是它的实现。

> "The motif is the ultimate cohomological invariant."
> — Alexander Grothendieck

**核心问题**：

1. 是否存在一个范畴，使得代数簇的上同调信息被「纯粹」地编码？
2. 能否统一Betti、de Rham、étale等不同上同调理论？

### 2.2 纯动机

**定义 2.2.1**（光滑射影簇的对应）
设 $X, Y$ 是光滑射影簇，**代数对应**（correspondence）定义为：
$$\text{Corr}^r(X, Y) := \text{CH}^{\dim X + r}(X \times Y)$$
其中 $\text{CH}^*$ 是周环（Chow ring）。

**定义 2.2.2**（纯动机的有效范畴）
**有效纯动机**范畴 $\mathcal{M}_{\text{eff}}$ 的对象为 $(X, p, n)$，其中：

- $X$ 是光滑射影簇
- $p \in \text{Corr}^0(X, X)$ 是幂等元（投影子）
- $n \in \mathbb{Z}$ 是Tate扭动

态射：
$$\text{Hom}((X, p, n), (Y, q, m)) := q \circ \text{Corr}^{n-m}(X, Y) \circ p$$

**定义 2.2.3**（Lefschetz动机）
**Lefschetz动机** $\mathbb{L}$ 定义为：
$$\mathbb{L} := (\mathbb{P}^1, \mathbb{P}^1 - \{\infty\}, 0)$$
满足 $H^*(\mathbb{L}) = H^2(\mathbb{P}^1)$。

**定义 2.2.4**（纯动机范畴）
通过对 $\mathbb{L}$ 取逆完备化，得到**纯动机**范畴：
$$\mathcal{M} := \mathcal{M}_{\text{eff}}[\mathbb{L}^{-1}]$$

### 2.3 混合动机

**定义 2.3.1**（混合动机的哲学）
**混合动机**是纯动机的非射影推广，对应于「非纯粹」的上同调（如开簇、奇异簇）。

**定义 2.3.2**（Norí动机）
**Norí动机**通过图表（diagram）构造：
$$\mathcal{MM}_{\text{Norí}} := \text{2-colim}_{(X, Y, n)} \text{Rep}(\text{GL}(H^n(X, Y)))$$

其中 $(X, Y, n)$ 跑遍「好的」对（good pairs）。

**定义 2.3.3**（Voevodsky动机）
**Voevodsky动机**使用转移范畴：
$$\text{DM}^{\text{eff}}(k) := D(\text{PST})[\mathbb{L}^{-1}]$$
其中 PST 是预层带转移（presheaves with transfers）。

**定义 2.3.4**（混合Tate动机）
**混合Tate动机**是由 $\mathbb{Q}(n)$ 生成的子范畴：
$$\mathcal{MTM} := \langle \mathbb{Q}(n) : n \in \mathbb{Z} \rangle^\otimes \subset \mathcal{MM}$$

### 2.4 动机的实现

**定义 2.4.1**（实现函子）
**实现函子**将动机映射到具体的上同调理论：

| 实现 | 目标范畴 | 构造 |
|-----|---------|------|
| Betti | $\mathbb{Q}$-Hodge结构 | 奇异上同调 |
| de Rham | _filtered $\mathbb{Q}$-向量空间 | 代数de Rham |
| étale | $G_k$-表示 | étale上同调 |
| 晶体 | F-晶体 | 晶体上同调 |

**定义 2.4.2**（动机上同调）
代数簇 $X$ 的**动机上同调**定义为：
$$H^i_\mathcal{M}(X, \mathbb{Q}(j)) := \text{Hom}_{\mathcal{DM}}(\mathbb{Q}, M(X)(j)[i])$$

---

## 3. 主要结果与定理

### 3.1 基本定理

**定理 3.1.1**（Tag 0F5A - 混合动机定义）
混合动机范畴满足以下性质：

**(a) 半单性（纯情形）**
若假设**标准猜想**，则纯动机范畴 $\mathcal{M}$ 是半单阿贝尔范畴。

**(b) 权滤波**
混合动机 $M$ 配备**权滤波** $W_*$：
$$0 \subset W_{w_0} M \subset \cdots \subset W_{w_n} M = M$$
使得 $\text{Gr}^W_w M$ 是纯的（权 $w$）。

**(c) 六项正合序列**
对于开浸入 $j: U \hookrightarrow X$ 和闭浸入 $i: Z \hookrightarrow X$：
$$\cdots \to H^i_\mathcal{M}(X) \to H^i_\mathcal{M}(U) \to H^{i+1}_\mathcal{M}(Z) \to H^{i+1}_\mathcal{M}(X) \to \cdots$$

### 3.2 标准猜想与动机

**定理 3.2.1**（Grothendieck）
若**标准猜想**（Standard Conjectures）成立，则：

1. 动机范畴 $\mathcal{M}$ 是半单阿贝尔范畴
2. 所有实现函子是**忠实**的
3. **Tannaka对偶**适用

**定理 3.2.2**（Jannsen）
假设标准猜想，则动机范畴是**neutrale Tannaka范畴**。

### 3.3 Voevodsky理论

**定理 3.3.1**（Voevodsky, 2000）
Voevodsky动机范畴 $\text{DM}(k, \mathbb{Q})$ 满足：

- 是紧生成三角范畴
- 带有t-结构（Norít-结构）
- hearts是混合动机的候选

**定理 3.3.2**（权t-结构）
存在**权t-结构** $(\text{DM}_{w \leq 0}, \text{DM}_{w \geq 0})$ 使得：

- hearts是纯动机
- 兼容于几何构造

### 3.4 特殊值与动机

**定理 3.4.1**（Deligne, Beilinson）
L-函数在特殊点的值与**动机上同调**相关：
$$L(M, s) \text{ 在 } s=0 \leadsto \text{Ext}^1_{\mathcal{MM}}(\mathbb{Q}, M)$$

---

## 4. 证明思路

### 4.1 Norí动机构造

**步骤1**：好对的范畴
定义**好对**范畴 $\text{Pairs}$，对象为 $(X, Y, n)$，满足：

- $Y \subset X$ 是闭子簇
- $H^i(X, Y) = 0$ 对 $i \neq n$

**步骤2**：图表的表示
构造图表：
$$T: \text{Pairs}^{\text{op}} \to \text{Vect}_\mathbb{Q}$$
$$(X, Y, n) \mapsto H^n(X, Y; \mathbb{Q})$$

**步骤3**：Norí范畴
定义为图表的**万有阿贝尔范畴**：
$$\mathcal{MM}_{\text{Norí}} := \mathcal{C}(T)$$

### 4.2 Voevodsky构造

**步骤1**：Nisnevich层
考虑Nisnevich拓扑上的层。

**步骤2**：转移
定义**有限对应**（finite correspondences）：
$$c(X, Y) := \text{代数循环的自由阿贝尔群}$$

**步骤3**：导出范畴
$$\text{DM}^{\text{eff}} := D(\text{Sh}_{\text{Nis}}(\text{Cor}_k))[\mathbb{A}^1]^{-1}$$

### 4.3 标准猜想的角色

**观察**：标准猜想提供「 motivic 」结构：

1. **Lefschetz型猜想** $\Rightarrow$ hard Lefschetz在动机层面
2. **Hodge型猜想** $\Rightarrow$ 同调与代数循环的对应

---

## 5. 应用与例子

### 5.1 Artin动机

**例子 5.1.1**
**Artin动机**是由零维簇生成的子范畴：
$$\mathcal{AM} := \langle \text{Spec}(k') : k'/k \text{ 有限} \rangle$$
等价于有限 $G_k$-表示的范畴。

### 5.2 椭圆曲线的动机

**例子 5.1.2**
设 $E$ 是椭圆曲线，其动机分解为：
$$h(E) = \mathbb{1} \oplus h^1(E) \oplus \mathbb{L}$$
其中 $h^1(E)$ 对应 $H^1(E)$。

### 5.3 混合Tate动机的周期

**例子 5.1.3**
混合Tate动机的周期是**多重zeta值**（MZVs）：
$$\zeta(n_1, \ldots, n_r) = \sum_{0 < k_1 < \cdots < k_r} \frac{1}{k_1^{n_1} \cdots k_r^{n_r}}$$

### 5.4 Bloch-Kato猜想

**应用 5.3.1**
**Bloch-Kato猜想**（现为定理，Voevodsky）的动机表述：
$$H^i_\mathcal{M}(X, \mathbb{Q}(j)) \otimes \mathbb{Q}_p \cong H^i_{\text{ét}}(X, \mathbb{Q}_p(j))^{G_k}$$

### 5.5 特殊L-值

**应用 5.3.2**（Beilinson猜想）
L-函数的特殊值由动机的**调节子**（regulator）给出：
$$L(M, n) \sim \text{Reg}_n(M) \cdot \text{Period}(M)$$

---

## 6. 与其他概念的关系

### 6.1 与Hodge理论的对比

```
    Hodge理论                      动机理论
    ─────────                     ─────────
    Hodge结构 ←────────────────→  动机（理想）
         │                            │
         │ 实现                        │ 实现
         ▼                            ▼
    各种上同调 ←────────────────→ 各种上同调
         │                            │
         │ 比较同构                    │ 比较同构
         └────────────┬───────────────┘
                      │
                      ▼
               混合动机范畴
               （万有理论）
```

### 6.2 与Tannaka对偶

**关系**：动机理论是Tannaka对偶的几何实现
$$\mathcal{MM} \cong \text{Rep}(G_{\text{mot}})$$
其中 $G_{\text{mot}}$ 是**动机Galois群**。

### 6.3 与周期理论

**Kontsevich-Zagier周期**：
$$\mathcal{P} := \langle \int_\gamma \omega : X \text{ 代数}, \gamma \in H_*(X^{\text{an}}) \rangle$$

与动机的深刻联系：
$$\text{Periods} = \text{Matrix coefficients of } \mathcal{MM}$$

### 6.4 与导出几何

**现代发展**：导出动机

- 导出代数簇的动机
- 高阶循环群

---

## 7. 参考文献

### 7.1 奠基文献

1. **Grothendieck, A.** (1960s). *Standard conjectures on algebraic cycles*
   - 动机的原始想法

2. **Deligne, P.** (1974). *Théorie de Hodge III*
   - Publ. Math. IHÉS
   - 混合Hodge理论

3. **Beilinson, A.** (1985). *Higher regulators and values of L-functions*
   - 动机上同调

### 7.2 现代构造

1. **Voevodsky, V.** (2000). *Triangulated categories of motives*
   - Ann. of Math. Studies
   - Voevodsky动机

2. **Huber, A.** (1995). *Mixed motives and their realization*
   - Norí动机

3. **Levine, M.** (1998). *Mixed motives*
   - Mathematical Surveys

### 7.3 综述文献

1. **Jannsen, U.** (1994). *Motivic sheaves and filtrations on Chow groups*
   - Motives (Seattle)

2. **Deligne, P.** (2006). *The Hodge conjecture*
   - Clay Mathematics Institute

### 7.4 在线资源

1. **Stacks Project**: [Tag 0F5A](https://stacks.math.columbia.edu/tag/0F5A)
2. **motives.xyz**: 动机理论资源汇总

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0F5B](#tag-0f5b) | 标准猜想 | 基础假设 |
| [0F5C](#tag-0f5c) | 周期与动机 | 具体实现 |
| [0F5D](#tag-0f5d) | 动机Galois群 | Tannaka对偶 |

### 8.2 上同调理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1A](#tag-0f1a) | p进Hodge理论 | 实现之一 |
| [01E8](#tag-01e8) | 层上同调 | 技术 |
| [0F5E](#tag-0f5e) | 动机上同调 | 计算 |

### 8.3 特殊类型

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F5F](#tag-0f5f) | 混合Tate动机 | 子范畴 |
| [0F5G](#tag-0f5g) | Artin动机 | 零维 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **Grothendieck梦想**：动机是代数几何的「终极不变量」

2. **千禧年难题**：Hodge猜想是标准猜想的一部分

3. **现代突破**：Voevodsky的工作（2002年菲尔兹奖）

4. **持续活跃**：与特殊L-值、周期理论的深刻联系

### A.2 待解决问题

- **标准猜想**（千禧年难题级别）
- **动机t-结构的存在性**
- **Beilinson猜想的完全证明**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 纯动机范畴 | ❌ 待建设 | ★★★★★ |
| 代数对应 | ❌ 待建设 | ★★★★☆ |
| Norí动机 | ❌ 待建设 | ★★★★★ |
| Voevodsky动机 | ❌ 待建设 | ★★★★★ |
| 权t-结构 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
