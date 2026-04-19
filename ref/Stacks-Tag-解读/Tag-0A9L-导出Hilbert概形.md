---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0A9L - 导出Hilbert概形

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0A9L |
| **英文名称** | Derived Hilbert Schemes |
| **所属章节** | Quot and Hilbert Schemes |
| **主题分类** | 导出代数几何 - 模空间 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 Hilbert概形概述

**Hilbert概形**（Hilbert Scheme）是代数几何中最重要的模空间之一，参数化给定射影空间中具有固定Hilbert多项式的闭子概形。**导出Hilbert概形**是其在导出代数几何中的自然推广。

### 2.2 关键定义

**定义 2.2.1**（经典Hilbert函子）
设 $X \to S$ 是射影态射，$\mathcal{F}$ 是 $X$ 上的凝聚层。**Hilbert函子**定义为：

$$\text{Hilb}_{\mathcal{F}/X/S}: (\text{Sch}/S)^{\text{op}} \to \text{Sets}$$

$$T \mapsto \{\text{商层 } \mathcal{F}_T \twoheadrightarrow \mathcal{Q} \text{ 在 } X_T \text{ 上，平坦}/T\}/\cong$$

**定义 2.2.2**（导出Hilbert函子）
设 $X \to S$ 是**导出射影**态射。**导出Hilbert函子**是∞-函子：

$$\text{Hilb}^{\text{der}}_{\mathcal{F}/X/S}: \text{dSch}_{/S}^{\text{op}} \to \mathcal{S}$$

$$T \mapsto \{\text{导出商 } \mathcal{F}_T \twoheadrightarrow \mathcal{Q} \text{ 在 } X_T \text{ 上，平坦}/T\}$$

其中 $\mathcal{Q}$ 是**完美复形**（perfect complex）。

**定义 2.2.3**（导出Hilbert概形）
**导出Hilbert概形**是导出Hilbert函子的可表对象（在导出概形的∞-范畴中）：

$$\text{Hilb}^{\text{der}}_{\mathcal{F}/X/S} \cong \text{Map}_S(-, \mathcal{H}^{\text{der}}_{\mathcal{F}/X/S})$$

### 2.3 完美复形

**定义 2.3.1**（完美复形）
在导出概形 $X$ 上，**完美复形**是局部拟同构于有界复形的复形，且每一项都是有限秩局部自由层。

等价地，$\mathcal{E}^\bullet \in \text{Perf}(X)$ 当且仅当它在局部具有形式：

$$[\mathcal{E}^{-n} \to \cdots \to \mathcal{E}^0 \to \cdots \to \mathcal{E}^m]$$

其中每个 $\mathcal{E}^i$ 是局部自由的。

---

## 3. 主要结果与定理

### 3.1 导出Hilbert概形的存在性

**定理 3.1.1**（Tag 0A9L）
设 $X \to S$ 是射影导出概形的态射，$\mathcal{F}$ 是 $X$ 上的完美复形，$P$ 是有理多项式（假想的Hilbert多项式）。

则导出Hilbert函子 $\text{Hilb}^{\text{der}}_{P, \mathcal{F}/X/S}$ 由**导出射影概形**表示：

$$\mathcal{H}^{\text{der}}_{P, \mathcal{F}/X/S} \to S$$

此外，其**截断**（truncation）是经典的Hilbert概形：

$$t_0(\mathcal{H}^{\text{der}}_{P, \mathcal{F}/X/S}) = \text{Hilb}_{P, \mathcal{F}/X/S}$$

### 3.2 切复形

**定理 3.2.1**（切复形计算）
对于点 $[Z] \in \mathcal{H}^{\text{der}}$ 对应于商 $\mathcal{F} \twoheadrightarrow \mathcal{O}_Z$，其切复形为：

$$\mathbb{T}_{[Z]}\mathcal{H}^{\text{der}} \cong R\text{Hom}(I_Z, \mathcal{O}_Z)[1]$$

其中 $I_Z = \ker(\mathcal{F} \twoheadrightarrow \mathcal{O}_Z)$ 是理想层复形。

**推论 3.2.2**
切复形的上同调给出经典的形变理论数据：

| $H^i$ | 含义 |
|-------|------|
| $H^{-1}$ | 自同构群（无穷小） |
| $H^0$ | 切空间 |
| $H^1$ | 阻碍空间 |
| $H^{>1}$ | 高阶同伦（导出新信息） |

### 3.3 虚基本类

**定理 3.3.1**（Behrend-Fantechi）
导出Hilbert概形 $\mathcal{H}^{\text{der}}$ 带有自然的**虚基本类**：

$$[\mathcal{H}^{\text{der}}]^{\text{vir}} \in A_d(t_0(\mathcal{H}^{\text{der}}))$$

其中 $d = \text{rk}(\mathbb{T}^{\text{vir}})$ 是虚维数。

这允许在奇异模空间上进行枚举几何的计算。

---

## 4. 证明思路

### 4.1 可表性的证明

**步骤1**：嵌入到Grassmannian
- 对于射影空间 $\mathbb{P}^n$，使用Plücker嵌入
- 导出Quot概形嵌入到导出Grassmannian

**步骤2**：导出Grassmannian的构造
- 经典Grassmannian是光滑的
- 导出Grassmannian是平凡的导出化：$G^{\text{der}} = G$（离散）

**步骤3**：正合性条件
- 平坦性条件在导出范畴中更微妙
- 使用Tor-振幅（Tor-amplitude）控制

### 4.2 切复形的计算

**核心观察**：
对于商 $\mathcal{F} \twoheadrightarrow \mathcal{Q}$，形变由扩张控制：

$$0 \to \mathcal{Q} \to \tilde{\mathcal{Q}} \to \mathcal{Q} \to 0$$

在导出范畴中，这对应于：

$$\text{Def} \cong \text{Ext}^1(\mathcal{Q}, \mathcal{Q}) \leadsto R\text{Hom}(\mathcal{Q}, \mathcal{Q})[1]$$

### 4.3 虚基本类的构造

**技术步骤**：
1. 构造**完美阻碍理论**（Perfect Obstruction Theory）：
   $$\phi: \mathbb{E}^\bullet \to \mathbb{L}_{\mathcal{M}}$$
2. 导出Hilbert概形自动提供：
   $$\mathbb{E}^\bullet = (\mathbb{T}^{\text{der}})^\vee$$
3. 应用Behrend-Fantechi构造

---

## 5. 应用与例子

### 5.1 曲线在三维fold中的计数

**例子 5.1.1**（局部Pandharipande-Thomas理论）
对于三维光滑射影簇 $X$，PT不变量计数**稳定对**：

$$(\mathcal{O}_X \xrightarrow{s} \mathcal{F})$$

其中 $\mathcal{F}$ 是纯1维的，$\text{coker}(s)$ 是0维的。

导出Hilbert概形（PT模空间）带有自然的**对称阻碍理论**。

### 5.2 Donaldson-Thomas理论

**应用 5.2.1**（DT不变量）
对于Calabi-Yau 3-fold，理想层的Hilbert概形：

$$\text{Hilb}_n(X) = \{I_Z \subseteq \mathcal{O}_X : \chi(\mathcal{O}_Z) = n\}$$

带有**-1-shifted辛结构**（由Pantev-Toën-Vaquié-Vezzosi）。

DT不变量定义为：

$$DT_n = \int_{[\text{Hilb}_n(X)]^{\text{vir}}} 1 = \chi^{\text{vir}}(\text{Hilb}_n(X))$$

### 5.3 导出形变与经典形变的比较

**例子 5.3.1**（完全交）
设 $X \subseteq \mathbb{P}^n$ 是超曲面的完全交。

| 经典Hilbert概形 | 导出Hilbert概形 |
|----------------|----------------|
| 可能奇异 | 总是光滑（在导出意义下） |
| 可能有错误维数 | 有明确的虚维数 |
| 需要人工obstruction theory | 自然携带切复形 |

### 5.4 模空间的完备化

**应用 5.4.1**（稳定对的紧致化）
导出Hilbert概形提供了自然紧致化：

$$\text{PT}(X) \subseteq \mathcal{H}^{\text{der}}_{P, \mathcal{O}_X/X}$$

这允许研究模空间的边界行为。

---

## 6. 与其他概念的关系

### 6.1 模空间理论的谱系

```
        经典Hilbert概形
              │
              │ 导出化
              ▼
        导出Hilbert概形
              │
      ┌───────┴───────┐
      │               │
      ▼               ▼
  虚基本类理论    shifted辛结构
      │               │
      └───────┬───────┘
              ▼
        枚举几何不变量
              │
      ┌───────┴───────┐
      ▼               ▼
   DT/PT理论      Gromov-Witten
```

### 6.2 与完美阻碍理论的关系

**Li-Tian** 与 **Behrend-Fantechi** 的obstruction theory通过导出几何统一：

| 经典 | 导出 |
|------|------|
| Obstruction sheaf | 切复形的 $H^1$ |
| Virtual dimension | 切复形的Euler特征 |
| 局部方程 | Koszul复形 |

### 6.3 与稳定条件的关系

**Bridgeland稳定性**与导出Hilbert概形的联系：

- 稳定对象的模空间是导出Hilbert概形的开子集
- 墙交叉公式对应于导出几何的变换

---

## 7. 参考文献

### 7.1 奠基文献

1. **Grothendieck, A.** (1962). *Techniques de construction et théorèmes d'existence en géométrie algébrique IV*
   - Hilbert概形的原始构造

2. **Lurie, J.** (2011). *Derived Algebraic Geometry VIII: Quasi-Coherent Sheaves*
   - 导出Hilbert概形的理论

3. **Ciocan-Fontanine, I. & Kapranov, M.** (2001). *Derived Quot schemes*
   - Ann. Sci. Éc. Norm. Sup.
   - 导出Quot概形的具体构造

### 7.2 虚基本类理论

4. **Behrend, K. & Fantechi, B.** (1997). *The intrinsic normal cone*
   - Invent. Math.
   - 虚基本类的构造

5. **Li, J. & Tian, G.** (1998). *Virtual moduli cycles and Gromov-Witten invariants*
   - 代数GW理论

### 7.3 枚举几何应用

6. **Thomas, R.P.** (2000). *A holomorphic Casson invariant for Calabi-Yau 3-folds*
   - DT不变量的原始定义

7. **Pandharipande, R. & Thomas, R.P.** (2009). *Curve counting via stable pairs*
   - PT理论

8. **Pantev, T., Toën, B., Vaquié, M., Vezzosi, G.** (2013). *Shifted symplectic structures*
   - Publ. Math. IHÉS
   - 导出辛几何的框架

### 7.4 在线资源

9. **Stacks Project**: [Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
10. **Stacks Project**: [Quot and Hilbert Schemes](https://stacks.math.columbia.edu/chapter/0D4C)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0A9K](#tag-0a9k) | 导出形变理论 | 理论基础 |
| [0D4C](#tag-0d4c) | Quot概形 | 一般构造 |
| [0D4D](#tag-0d4d) | Hilbert概形 | 经典版本 |

### 8.2 导出几何

| Tag | 主题 | 说明 |
|-----|------|------|
| [0D4E](#tag-0d4e) | 导出模空间 | 一般理论 |
| [0D4F](#tag-0d4f) | 完美复形 | 技术基础 |
| [0D4G](#tag-0d4g) | 虚基本类 | 应用工具 |

### 8.3 枚举应用

| Tag | 主题 | 说明 |
|-----|------|------|
| [0D4H](#tag-0d4h) | Donaldson-Thomas不变量 | 主要应用 |
| [0D4I](#tag-0d4i) | Pandharipande-Thomas理论 | 相关理论 |
| [0D4J](#tag-0d4j) | Gromov-Witten理论 | 比较理论 |

---

## 附录：计算示例

### Hilbert概形的维数公式

对于 $\mathbb{P}^n$ 中d次、维数r的子簇：

$$\dim \text{Hilb} = (d+1)(n-r) + r(n-r)$$

导出版本的虚维数相同，但切复形提供了更精细的信息。

### 切复形的分解

对于光滑嵌入 $Z \subseteq X$：

$$\mathbb{T}_{[Z]} = \Gamma(Z, N_{Z/X})[0] \oplus H^1(Z, N_{Z/X})[-1] \oplus \cdots$$

这直接读出形变理论的数据。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
