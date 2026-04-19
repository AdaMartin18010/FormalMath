---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 01YG 解读：Serre消失定理

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YG |
| **章节** | Schemes, Section 30.16: Higher direct images of coherent sheaves |
| **类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐⭐ (核心定理) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01YG |

---

## 2. 定理原文与翻译

### 英文原文

**Lemma 30.16.1 (Serre vanishing).** Let $X$ be a proper scheme over a Noetherian ring $A$. Let $\mathcal{L}$ be an ample invertible sheaf on $X$. Let $\mathcal{F}$ be a coherent $\mathcal{O}_X$-module. Then $H^i(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n}) = 0$ for all $i > 0$ and all sufficiently large $n$.

### 中文翻译

**引理 30.16.1 (Serre消失定理).** 设 $X$ 是诺特环 $A$ 上的真概形，$\mathcal{L}$ 是 $X$ 上的丰富可逆层，$\mathcal{F}$ 是凝聚 $\mathcal{O}_X$-模。则对所有 $i > 0$ 和所有充分大的 $n$，有：

$$H^i(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n}) = 0$$

---

## 3. 概念依赖图

```
Tag 01YG: Serre消失定理
│
├── 前置概念
│   ├── 真概形 (Proper Scheme)
│   │   ├── 分离、泛闭、有限型
│   │   └── 紧性在代数几何中的类比
│   ├── 丰富层 (Ample Invertible Sheaf)
│   │   ├── 丰沛层的定义
│   │   └── 射影嵌入
│   ├── 凝聚层 (Coherent Sheaf)
│   │   └── Tag 01LC
│   ├── 层上同调 (Sheaf Cohomology)
│   │   └── Tag 01E8
│   └── 射影空间上同调 (Tag 02O3)
│       └── 扭曲层的计算
│
├── 核心定理
│   └── Serre消失定理
│       └── 真概形 + 丰富层 ⟹ 上同调消失
│
├── 证明技术
│   ├── 化归到射影空间
│   ├── 有限覆盖论证
│   ├── 谱序列技术
│   └── 诺特归纳法
│
├── 相关定理
│   ├── Serre有限生成定理
│   ├── 投影公式的应用
│   └── 维数消失的强化
│
└── 相关Tags
    ├── Tag 01LC: 凝聚层
    ├── Tag 02O3: 射影空间上同调
    ├── Tag 01X8: 仿射上同调消失
    └── Tag 0B5L: 丰富层的上同调判别
```

---

## 4. 详细证明

### 4.1 定理陈述分析

Serre消失定理是代数几何中最重要、最常用的定理之一，它表明：

**核心信息**：在真概形上，"扭得足够多"的凝聚层的高阶上同调消失。

这类似于复几何中：紧致复流形上全纯向量丛的扭曲上同调消失。

### 4.2 证明策略

**步骤1: 化归到射影空间**

由 $\mathcal{L}$ 丰富，存在 $n_0$ 使得 $\mathcal{L}^{\otimes n_0}$ 是非常丰沛的，诱导闭浸入：

$$i: X \hookrightarrow \mathbb{P}^N_A$$

使得 $\mathcal{L}^{\otimes n_0} \cong i^*\mathcal{O}_{\mathbb{P}^N}(1)$。

**步骤2: 推动到射影空间**

设 $\mathcal{G} = i_*(\mathcal{F} \otimes \mathcal{L}^{\otimes k})$ 是 $\mathbb{P}^N$ 上的凝聚层（$0 \leq k < n_0$）。

由投影公式：

$$i_*(\mathcal{F} \otimes \mathcal{L}^{\otimes (mn_0 + k)}) \cong \mathcal{G} \otimes \mathcal{O}_{\mathbb{P}^N}(m)$$

**步骤3: 射影空间的情形**

对 $\mathbb{P}^N$ 上的凝聚层 $\mathcal{G}$，由射影空间上同调的显式计算 (Tag 02O3) 及其推广：

$$H^i(\mathbb{P}^N, \mathcal{G} \otimes \mathcal{O}(m)) = 0 \quad \text{对 } i > 0, m \gg 0$$

**步骤4: 回到原概形**

由 Leray 谱序列或直接像的高阶上同调消失（真概形性质）：

$$H^i(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n}) \cong H^i(\mathbb{P}^N, i_*(\mathcal{F} \otimes \mathcal{L}^{\otimes n}))$$

综合上述即得结论。

### 4.3 关键引理

**引理 (射影空间上的消失)**：设 $\mathcal{G}$ 是 $\mathbb{P}^N_A$ 上的凝聚层，则：

$$H^i(\mathbb{P}^N, \mathcal{G}(m)) = 0 \quad \forall i > 0, m \gg 0$$

**证明思路**：

1. 任何凝聚层有形式 $\widetilde{M}$，$M$ 为有限生成分次模
2. 取分次模的有限表现：$0 \to K \to \bigoplus \mathcal{O}(-a_i) \to \mathcal{G} \to 0$
3. 利用长正合列和 $H^i(\mathbb{P}^N, \mathcal{O}(m))$ 的已知消失性
4. 诺特归纳于支撑集

### 4.4 有限生成性推论

**定理 (Serre)**: 在相同假设下，$\bigoplus_{n \geq 0} H^0(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n})$ 是有限生成分次 $A$-模。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 真概形 | 紧性类比 | `concept/代数几何/真态射.md` |
| 丰富层 | Ample sheaf | `concept/代数几何/丰富层.md` |
| 凝聚层 | Coherent sheaf | `concept/代数几何/凝聚层.md` |
| 层上同调 | Sheaf cohomology | `concept/层论/层上同调.md` |
| 射影空间 | Projective space | `concept/代数几何/射影概形.md` |

### 学习路径

```
FormalMath: 代数几何进阶
├── 前置
│   ├── 凝聚层 (Tag 01LC)
│   ├── 层上同调 (Tag 01E8)
│   ├── 射影空间上同调 (Tag 02O3)
│   └── 丰富层理论
├── 当前 ← Tag 01YG
│   ├── Serre消失定理
│   └── 有限生成定理
└── 后续
    ├── Hilbert多项式
    ├── Riemann-Roch定理
    ├── Kodaira消失定理
    └── 对偶性理论
```

---

## 6. 应用与重要性

### 6.1 核心应用

| 应用 | 说明 |
|------|------|
| Hilbert多项式 | 定义并研究欧拉示性数的渐近行为 |
| Riemann-Roch定理 | 曲线情形下消去高阶项 |
| 到射影空间的态射 | 证明丰富层的丰沛性判别 |
| 线性系统理论 | 研究完整线性系统的基点 |
| 渐近性质 | 扭曲层的上同调维数 |

### 6.2 重要推论

**推论1 (投影公式)**：对真态射 $f: X \to Y$ 和 $Y$ 上的丰富层 $\mathcal{L}$：

$$R^if_*(\mathcal{F} \otimes f^*\mathcal{L}^{\otimes n}) = 0 \quad i > 0, n \gg 0$$

**推论2 (相对版本)**：真态射 $f: X \to S$ 的相对上同调消失。

**推论3 (半连续性)**：上同调维数的上半连续性。

### 6.3 与其他消失定理的比较

| 定理 | 假设 | 结论 |
|------|------|------|
| Serre消失 | 真 + 丰富层 | $H^i = 0$ ($i>0$) |
| Kodaira消失 | 光滑射影 + 丰富典则 | $H^{n,q} = 0$ ($q>0$) |
| Kawamata-Viehweg | 对数典范 | 推广版本 |
| Grauert-Riemenschneider | 双有理几何 | 直接像消失 |
| Nakano消失 | 向量丛版本 | $H^{p,q}(E) = 0$ |

### 6.4 历史意义

这是Serre在FAC (1955) 中的核心结果之一，奠定了：
- 射影概形的上同调理论
- 代数几何的整体方法
- 现代模空间理论的基础

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Hartshorne | III.5 | The cohomology of projective space |
| Liu Qing | 5.3 | Cohomology of projective schemes |
| Görtz-Wedhorn | 12.6 | Higher direct images under projective morphisms |
| Vakil FOAG | 18.6 | Serre vanishing and applications |
| EGA III | §2 | Cohomologie des faisceaux cohérents |

### 7.2 原始文献

```bibtex
@article{serre1955faisceaux,
  title     = {Faisceaux algébriques cohérents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  pages     = {197--278},
  year      = {1955}
}
```

### 7.3 nLab条目

- [Serre vanishing theorem](https://ncatlab.org/nlab/show/Serre+vanishing+theorem)
- [ample line bundle](https://ncatlab.org/nlab/show/ample+line+bundle)
- [coherent sheaf](https://ncatlab.org/nlab/show/coherent+sheaf)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 01LC | 凝聚层 | 对象定义 |
| 02O3 | 射影空间上同调 | 核心工具 |
| 01YH | 上同调类射 | 应用 |
| 0B5L | 丰富层判别 | 理论基础 |
| 0B5Y | Hilbert多项式 | 推论 |

---

## 8. Lean4形式化展望

### 8.1 形式化挑战

这是代数几何形式化的**高难度目标**：

1. **依赖链条长**：需要凝聚层、真概形、丰富层、射影嵌入等全套理论
2. **复杂论证**：化归到射影空间、诺特归纳、谱序列等
3. **具体计算**：需要射影空间上同调的完整形式化

### 8.2 Mathlib4现状

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Ample

-- 丰富层定义
#check AlgebraicGeometry.IsAmple

-- 真态射
#check AlgebraicGeometry.Proper

-- 层上同调（基础）
#check AlgebraicGeometry.sheafCohomology
```

### 8.3 形式化路线图

| 阶段 | 目标 | 依赖 | 难度 |
|------|------|------|------|
| 1 | 射影空间上同调完整化 | Tag 02O3 | 高 |
| 2 | 凝聚层的高阶直接像 | 直接像理论 | 高 |
| 3 | 真概形的上同调性质 | Leray谱序列 | 高 |
| 4 | 丰富层的射影嵌入 | 丰沛层理论 | 高 |
| 5 | Serre消失定理 | 以上全部 | 极高 |

### 8.4 形式化代码框架

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Proper

namespace AlgebraicGeometry

variable {A : Type*} [CommRing A] [IsNoetherian A]
variable {X : Scheme} [IsProper (structureMorphism X)]
variable (L : InvertibleSheaf X) [IsAmple L]
variable (F : CoherentSheaf X)

-- Serre消失定理
theorem serre_vanishing (i : ℕ) (hi : i > 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      cohomology X (F ⊗ L.pow n) i = 0 := by
  -- 步骤1: 化归到射影空间
  obtain ⟨N, φ, hφ⟩ := exists_projective_embedding L
  -- 步骤2: 推动凝聚层
  let G : CoherentSheaf (ProjectiveSpace N A) := φ.pushForward F
  -- 步骤3: 使用射影空间的消失
  have vanishing : ∃ M, ∀ m ≥ M,
      cohomology (ProjectiveSpace N A) (G ⊗ O(m)) i = 0 :=
    projective_vanishing G i hi
  -- 步骤4: 回到原概形
  sorry

-- 有限生成性推论
theorem sections_finite_generated :
    Module.Finite A (DirectSum ℕ fun n ↦
      sections X (F ⊗ L.pow n)) := by
  -- 使用Serre消失和诺特性
  sorry

end AlgebraicGeometry
```

### 8.5 与其他消失定理的形式化

```lean
-- Kodaira消失定理（复几何）
theorem kodaira_vanishing {X : ComplexManifold} [CompactSpace X]
    {L : HolomorphicLineBundle X} [Positive L] (q : ℕ) (hq : q > 0) :
    DolbeaultCohomology X L (dim X, q) = 0 := by
  sorry

-- Grauert-Riemenschneider
theorem grauert_riemenschneider {X Y : Scheme} (f : X ⟶ Y)
    [IsProper f] [IsBirational f] (i : ℕ) (hi : i > 0) :
    higherDirectImage f i (canonicalSheaf X) = 0 := by
  sorry
```

### 8.6 发展建议

**近期目标**：
- 完成射影空间上同调的形式化
- 建立真概形的基本性质
- 实现丰富层的判别准则

**远期愿景**：
- 完整形式化Serre消失定理
- 发展复代数几何的消失定理
- 建立对偶性理论的代数基础

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 01YG}
}

@article{serre1955faisceaux,
  title     = {Faisceaux algébriques cohérents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  pages     = {197--278},
  year      = {1955}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
