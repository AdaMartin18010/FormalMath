# Stacks Project Tag 0A1B - 刚性几何与形式几何

## 1. 基本概念与定义

### 1.1 核心对应关系

**Raynaud定理的核心洞察：** 刚性解析几何与形式几何是同一事物的两个视角。

| 视角 | 对象 | 研究重点 |
|------|------|----------|
| 刚性解析 | Generic fiber | 分析性质 |
| 形式几何 | 整模型 | 退化行为、约化 |

### 1.2 形式概形的Generic Fiber

**设置：** 设 $K$ 为完备非阿基米德域，$K^\circ$ 为整数环，$k = K^\circ/\varpi$ 为剩余域。

**定义：** 对于 $K^\circ$-形式概形 $\mathcal{X}$（$\varpi$-adic完备），其 **generic fiber** $\mathcal{X}_\eta$ 是一个刚性解析空间。

**构造方法：** $\mathcal{X}_\eta = \bigcup_i Sp(A_i[1/\varpi])$，其中 $\mathcal{X} = \bigcup_i Spf(A_i)$。

---

## 2. 数学背景与动机

### 2.1 Raynaud的突破（1974）

**问题：** Tate的刚性解析几何定义依赖于特定的 $G$-拓扑，缺乏概形的代数几何直觉。

**Raynaud的解决方案：**

1. 将刚性解析空间视为形式概形的 generic fiber
2. 这提供了"整结构"，使得模 $p$ 约化有意义
3. 统一了 $p$-adic分析和代数几何

### 2.2 为什么这种对应重要？

**(1) 模约化：** 通过形式模型研究刚性空间的约化

**(2) 周期映射：** $p$-adic Hodge理论中的比较同构

**(3) 模空间：** 许多模空间先有形式存在，再取generic fiber

---

## 3. 形式化性质与定理

### 3.1 Raynaud对应的形式表述

**定理（Raynaud的generic fiber函子）：** 函子：$$(-\ )_\eta: \{\text{拟紧平坦形式概形}\} \to \{\text{拟紧刚性解析空间}\}$$

是 essentially surjective 的。

**定理（态射的提升）：** 设 $\mathcal{X}, \mathcal{Y}$ 为平坦形式概形，则：$$\text{Hom}(\mathcal{X}_\eta, \mathcal{Y}_\eta) = \varinjlim_{\mathcal{X}'} \text{Hom}(\mathcal{X}', \mathcal{Y})$$

其中极限取遍 $\mathcal{X}$ 的所有admissible blow-ups。

### 3.2 刚性GAGA

**定理（Kiehl的GAGA）：** 设 $X$ 为射影刚性解析空间，则：

1. 凝聚层范畴等价：$$\text{Coh}(X^{alg}) \xrightarrow{\sim} \text{Coh}(X)$$

2. 上同调同构：$$H^i(X^{alg}, \mathcal{F}) \cong H^i(X, \mathcal{F}^{an})$$

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Formal Deformation Theory, Rigid Analytic Geometry
- **前置Tags：**
  - Tag 0A1A (刚性解析空间)
  - Tag 07RB (形式概形)

### 4.2 依赖关系

```
Tag 0A1B (刚性与形式几何)
├── Tag 0A1A (刚性解析)
├── Tag 07RB (形式概形)
├── Tag 07RI (形式GAGA)
└── Tag 0A1C (刚性上同调)
```

---

## 5. 应用与例子

### 5.1 经典对应

**例1：射影空间**

$$\mathbb{P}^{n,rig} = (\widehat{\mathbb{P}}^n_{K^\circ})_\eta$$

其中 $\widehat{\mathbb{P}}^n$ 是形式完备化。

**例2：Tate曲线的形式模型**

Tate曲线 $E_q^{rig}$ 有形式模型：

$$\mathcal{E}_q = \mathbb{G}_{m,K^\circ}^{for}/q^\mathbb{Z}$$

其特殊纤维是分裂的多重性约化的Néron polygon。

**例3：Drinfeld上半平面**

$$\Omega^d = \mathbb{P}^d \setminus \bigcup_{H \in \mathcal{H}} H$$

其中 $\mathcal{H}$ 是所有 $K$-有理超平面。它有丰富的形式模型理论。

### 5.2 在数学中的应用

**(1) $p$-adic Hodge理论**

通过形式模型研究刚性空间的上同调，建立比较同构。

**(2) 遍历$p$-adic对称域**

Drinfeld对称域的形式模型与Shimura簇的关系。

**(3) 完美胚空间**

完美胚空间的理论深化了刚性-形式对应：tilting等价将特征$p$和特征0联系起来。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
刚性 ↔ 形式对应 (0A1B)
│
├── 模约化 ──→ 韦伊猜想
├── 周期映射 ──→ $p$-adic Hodge
├── 模形式 ──→ $p$-adic模形式
├── 完美化 ──→ 完美胚空间
└── 凝聚数学 ──→ Clausen-Scholze
```

### 6.2 现代发展

| 理论 | 核心思想 | 创新点 |
|------|----------|--------|
| 完美胚空间 | 完美化形式模型 | tilting |
| 钻石 | 完美胚的商 | pro-étale拓扑 |
| 凝聚局部化 | 点集自由 | condensed sets |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0A1B
- **章节：** Formal Geometry, Rigid Analytic Spaces

### 7.2 核心文献

1. **Raynaud, M.** "Géométrie analytique rigide d'après Tate, Kiehl,..."
   - Raynaud对应的原始论文

2. **Bosch & Lütkebohmert** "Stable reduction and uniformization of abelian varieties I"
   - 稳定约化的形式模型理论

3. **Abbes, A.** *Éléments de Géométrie Rigide*

### 7.3 现代参考

- **Scholze, P.** "p-adic Hodge theory for rigid-analytic varieties"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现

```lean
-- Generic fiber函子
def genericFiber {K : Type} [NonArchimedeanField K]
    (X : FormalScheme K.𝒪) [Flat X] :
    RigidAnalyticSpace K :=
  ⟨X.localPatches.map (λ A ↦ Sp(A ⊗ K)), by sorry⟩

-- Raynaud对应的满射性
theorem raynaud_essentially_surjective
    (X : RigidAnalyticSpace K) (hc : QuasiCompact X) :
    ∃ 𝒳 : FormalScheme K.𝒪, Flat 𝒳 ∧ 𝒳.genericFiber ≅ X :=
  sorry

-- Admissible blow-up
structure AdmissibleBlowUp {X : FormalScheme R} where
  target : FormalScheme R
  morphism : Morphism X target
  [isIsomorphism_on_genericFiber : IsIso morphism.genericFiber]
```

### 8.2 形式化优先级

1. **形式概形范畴：** 基础的代数几何形式化
2. **Generic fiber构造：** 局部构造与粘合
3. **GAGA定理：** 凝聚层范畴的等价

---

## 总结

Tag 0A1B (刚性几何与形式几何) 揭示了 $p$-adic几何的深刻对偶性：刚性解析空间的几何直观与形式概形的代数结构相互补充。Raynaud的对应不仅是技术工具，更是现代算术几何（包括完美胚空间和钻石理论）的范式。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第88个*
