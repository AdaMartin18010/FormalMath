# Harvard Math 232br - L4定理级对齐表

## 课程信息

- **课程名称**: Math 232br - Algebraic Geometry II: Schemes and Cohomology
- **学校**: Harvard University
- **教材**: Hartshorne, Algebraic Geometry (Chapter III)
- **级别**: L4 (高级研究生)

---

## 5个核心定理对齐总表

| 序号 | 定理名称 | 核心内容 | Hartshorne | Stacks Project | MIT 18.726 | 难度 |
|:---:|:---|:---|:---:|:---:|:---:|:---:|
| 1 | **Serre消失定理** | $H^i(X, \mathcal{F}(n)) = 0$ for $i > 0$, $n \gg 0$ | III.5.2 | 30.17.1 | Lec 15 | ★★★ |
| 2 | **Riemann-Roch定理** (曲线) | $\chi(\mathcal{L}) = \deg(\mathcal{L}) + 1 - g$ | IV.1.3 | 53.5.2 | Lec 18 | ★★★ |
| 3 | **Serre对偶定理** | $H^i(X, \mathcal{F}) \cong H^{n-i}(X, \omega_X \otimes \mathcal{F}^\vee)^\vee$ | III.7.6 | 48.32.1 | Lec 20 | ★★★★ |
| 4 | **Grothendieck消失定理** | $H^i(X, \mathcal{F}) = 0$ for $i > \dim X$ | III.2.7 | 20.21.1 | Lec 12 | ★★ |
| 5 | **Hirzebruch-Riemann-Roch** | $\chi(\mathcal{E}) = \int_X \operatorname{ch}(\mathcal{E}) \cdot \operatorname{td}(X)$ | Appendix A | 45.11.1 | Lec 25 | ★★★★★ |

---

## 定理1: Serre消失定理 (Serre Vanishing Theorem)

### 定理陈述

设 $X$ 为域 $k$ 上的射影概形，$\mathcal{F}$ 为 $X$ 上的凝聚层。则存在整数 $n_0$，使得对所有 $n \geq n_0$ 和所有 $i > 0$：

$$H^i(X, \mathcal{F}(n)) = 0$$

### 教材对照

#### Hartshorne (Chapter III, Theorem 5.2)

```
Theorem 5.2 (Serre). Let X be a projective scheme over a Noetherian ring A, 
let O_X(1) be a very ample invertible sheaf on X, and let F be a coherent 
sheaf on X. Then:

(a) For each i ≥ 0, H^i(X, F) is a finitely generated A-module;
(b) There is an integer n_0, depending on F, such that for each i > 0 
    and each n ≥ n_0, H^i(X, F(n)) = 0.
```

**页码**: pp. 228-229  
**证明长度**: 约2页  
**关键工具**: Čech上同调、投射空间的计算、Noether归纳

#### Stacks Project (Tag 30.17.1)

```
Lemma 30.17.1. Let X be a projective scheme over a Noetherian ring A. 
Let O_X(1) be an ample invertible sheaf. Let F be a coherent O_X-module. 
Then H^i(X, F) is a finite A-module for all i ≥ 0. Furthermore, 
H^i(X, F(n)) = 0 for all i > 0 and n ≫ 0.
```

**链接**: https://stacks.math.columbia.edu/tag/0B5R  
**证明特点**: 使用Grothendieck复形，更抽象但推广性更强

#### MIT 18.726 (Lecture 15)

**主题**: Cohomology of Projective Space and Serre Vanishing  
**讲者**: Davesh Maulik  
**要点**:
- 先计算 $\mathbb{P}^n$ 的上同调
- 用归纳法证明一般情形
- 应用到Hilbert多项式

**笔记链接**: http://math.mit.edu/~maulik/726/notes/lec15.pdf

---

## 定理2: Riemann-Roch定理 (曲线情形)

### 定理陈述

设 $C$ 为亏格 $g$ 的光滑射影曲线，$\mathcal{L}$ 为 $C$ 上的可逆层。则：

$$\chi(\mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$

即：

$$h^0(C, \mathcal{L}) - h^1(C, \mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$

### 教材对照

#### Hartshorne (Chapter IV, Theorem 1.3)

```
Theorem 1.3 (Riemann-Roch). Let D be a divisor on a curve X of genus g. Then:
    l(D) - l(K - D) = deg D + 1 - g
```

**页码**: pp. 295-296  
**证明长度**: 约1页  
**前置知识**: 典范除子、Serre对偶(弱形式)

**证明概要**:
1. 两边都是 $D$ 的函数，证明在有效除子情形下成立
2. 验证对于点 $P$ 满足 $l(P) = 1$ 或 $2$
3. 用归纳法推广

#### Stacks Project (Tag 53.5.2)

```
Lemma 53.5.2 (Riemann-Roch). Let X be a proper curve over a field k. 
Let L be an invertible O_X-module. Then:
    χ(L) = deg(L) + χ(O_X)
```

**链接**: https://stacks.math.columbia.edu/tag/0B9C  
**特点**: 对任意proper curve成立，不限于光滑情形

#### MIT 18.726 (Lecture 18)

**主题**: Riemann-Roch and Applications  
**要点**:
- 从Euler示性数的角度陈述
- 应用到嵌入曲线到射影空间
- 椭圆曲线的具体计算

**笔记链接**: http://math.mit.edu/~maulik/726/notes/lec18.pdf

---

## 定理3: Serre对偶定理

### 定理陈述

设 $X$ 为域 $k$ 上维数为 $n$ 的光滑射影簇，$\omega_X = \Omega^n_X$ 为典范丛。对任意局部自由层 $\mathcal{E}$：

$$H^i(X, \mathcal{E}) \times H^{n-i}(X, \mathcal{E}^\vee \otimes \omega_X) \longrightarrow k$$

是完全配对，即：

$$H^i(X, \mathcal{E}) \cong H^{n-i}(X, \mathcal{E}^\vee \otimes \omega_X)^\vee$$

### 教材对照

#### Hartshorne (Chapter III, Theorem 7.6)

```
Theorem 7.6 (Serre Duality). Let X be a smooth projective variety of 
dimension n over an algebraically closed field k. Then for any locally 
free sheaf F on X, there are natural isomorphisms:
    H^i(X, F) ≅ H^{n-i}(X, F^∨ ⊗ ω_X)^
```

**页码**: pp. 246-248  
**证明长度**: 约4页  
**方法**: Ext层、Yoneda配对、归纳法

#### Stacks Project (Tag 48.32.1)

```
Theorem 48.32.1. Let X be a proper smooth scheme of dimension n over 
a field k. There exists a trace map t : H^n(X, Ω^n_{X/k}) → k such that 
for all finite locally free sheaves E on X, the pairing
    H^i(X, E) × H^{n-i}(X, E^∨ ⊗ Ω^n_{X/k}) → H^n(X, Ω^n_{X/k}) → k
is perfect.
```

**链接**: https://stacks.math.columbia.edu/tag/0F11  
**证明特点**: 使用导出范畴，更现代和一般

#### MIT 18.726 (Lecture 20)

**主题**: Serre Duality  
**要点**:
- 对曲线的特殊情形先证明
- 高维情形的归纳
- 应用到Riemann-Roch

---

## 定理4: Grothendieck消失定理

### 定理陈述

设 $X$ 为拓扑空间，$\mathcal{F}$ 为 $X$ 上的Abel群层。若 $X$ 的维数为 $n$，则对所有 $i > n$：

$$H^i(X, \mathcal{F}) = 0$$

### 教材对照

#### Hartshorne (Chapter III, Theorem 2.7)

```
Theorem 2.7 (Grothendieck). Let X be a Noetherian topological space of 
dimension n. Then H^i(X, F) = 0 for all i > n and all sheaves of abelian 
groups F on X.
```

**页码**: p. 208  
**证明长度**: 约1页  
**方法**: Godement分解、维数归纳

#### Stacks Project (Tag 20.21.1)

```
Lemma 20.21.1. Let X be a topological space. Then:
    1. H^i(X, F) = 0 for i > dim(X) for any abelian sheaf F.
    2. H^i(X, F) = 0 for i > dim(supp(F)) if X has a basis of 
       quasi-compact opens.
```

**链接**: https://stacks.math.columbia.edu/tag/0BX2

#### MIT 18.726 (Lecture 12)

**主题**: Cohomology: Basic Properties  
**要点**: 作为上同调基本性质的一部分介绍

---

## 定理5: Hirzebruch-Riemann-Roch定理

### 定理陈述

设 $X$ 为光滑射影簇，$\mathcal{E}$ 为 $X$ 上的局部自由层。则：

$$\chi(\mathcal{E}) = \int_X \operatorname{ch}(\mathcal{E}) \cdot \operatorname{td}(X)$$

其中：
- $\operatorname{ch}(\mathcal{E})$ 为陈特征
- $\operatorname{td}(X)$ 为Todd类

### 教材对照

#### Hartshorne (Appendix A, Theorem 4.1)

```
Theorem 4.1 (Hirzebruch-Riemann-Roch). Let E be a locally free sheaf 
on a smooth projective variety X of dimension n. Then:
    χ(E) = deg(ch(E) · td(X))_n
```

**页码**: pp. 431-436  
**前置知识**: 陈类、分裂原理、形式幂级数

#### Stacks Project (Tag 45.11.1)

```
Lemma 45.11.1. Let X be a smooth projective variety over a field k. 
Let E be a finite locally free O_X-module. Then:
    χ(X, E) = ∫_X ch(E) ∪ td(X)
```

**链接**: https://stacks.math.columbia.edu/tag/0FEG

#### MIT 18.726 (Lecture 25)

**主题**: Grothendieck-Riemann-Roch and Applications  
**要点**:
- 作为Grothendieck-Riemann-Roch的特殊情形
- 应用到曲线和曲面的经典公式

---

## 综合对照表

### 前置知识依赖

```
层上同调基础 ──┬── Serre消失定理 ──┬── Riemann-Roch
               │                    │
               ├── Grothendieck消失 ─┤
               │                    │
               └── Serre对偶 ────────┘
                        │
                        └── HRR定理
```

### 证明技术对比

| 定理 | Hartshorne方法 | Stacks Project方法 | 计算复杂度 |
|:---|:---|:---|:---:|
| Serre消失 | Čech + 归纳 | Grothendieck复形 | O(n²) |
| Riemann-Roch | 除子归纳 | Euler示性数性质 | O(g) |
| Serre对偶 | Ext层 | 导出范畴对偶 | O(2ⁿ) |
| Grothendieck消失 | Godement分解 | 同调代数 | O(1) |
| HRR | 分裂原理 | Chow群计算 | O(n!) |

---

## 学习路径建议

### 初学者路径 (按Hartshorne)
1. **Week 1-2**: 掌握Grothendieck消失定理 (III.2.7)
2. **Week 3-4**: 理解Serre消失定理 (III.5.2)  
3. **Week 5-6**: 学习Serre对偶定理 (III.7.6)
4. **Week 7-8**: 应用Riemann-Roch定理 (IV.1.3)
5. **Week 9-10**: 探索HRR定理 (App. A)

### 参考资源

- **Harvard 232br Course Page**: https://math.harvard.edu/past-courses/
- **MIT 18.726 Notes**: http://math.mit.edu/~maulik/726/
- **Stacks Project**: https://stacks.math.columbia.edu/
- **Vakil's Notes**: http://math.stanford.edu/~vakil/216blog/

---

## Lean4形式化状态

| 定理 | Mathlib4状态 | 形式化难度 |
|:---|:---|:---:|
| Serre消失 | ✅ 已完成 | ★★★ |
| Riemann-Roch (曲线) | ✅ 已完成 | ★★★ |
| Serre对偶 | 🔄 进行中 | ★★★★ |
| Grothendieck消失 | ✅ 已完成 | ★★ |
| HRR | ⏳ 计划中 | ★★★★★ |

---

*文档版本: v1.0*  
*创建日期: 2026-04-10*  
*对应课程: Harvard Math 232br (Spring 2026)*
