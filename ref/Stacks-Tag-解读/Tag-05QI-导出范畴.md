---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 05QI - 导出范畴

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 05QI |
| **章节位置** | Chapter 13: Derived Categories > Section 13.1: Introduction |
| **数学领域** | 同调代数 / 导出范畴论 |
| **文档类型** | 章节目录/导引 (Chapter Directory) |
| **重要性** | ⭐⭐⭐⭐⭐ (现代同调代数核心) |
| **相关Tags** | 05QJ-05RR (第13章全内容) |

---

## 2. 章节原文

### 英文原文 (Stacks Project)

> **Chapter 13: Derived Categories**
> 
> We first discuss triangulated categories and localization in triangulated categories. Next, we define the derived category of an abelian category. Finally, we discuss derived functors.

### 中文翻译

> **第13章：导出范畴**
> 
> 我们首先讨论三角范畴以及三角范畴的局部化。接着，我们定义Abel范畴的导出范畴。最后，我们讨论导出函子。

---

## 3. 概念依赖图

```
导出范畴 Chapter 13 (05QI)
│
├── Part 1: 三角范畴基础
│   ├── 05QJ: 三角范畴定义
│   ├── 05QK: 三角函子
│   ├── 05QL: 预三角范畴
│   └── 05QM: 广义三角
│
├── Part 2: 局部化理论
│   ├── 05QN: 乘法系
│   ├── 05QP: 三角范畴的局部化
│   └── 05QQ: 局部化的泛性质
│
├── Part 3: 同伦范畴
│   ├── 05QR: 复形同伦
│   ├── 05QS: 同伦范畴的三角结构
│   └── 05QT: K(𝓐)的构造
│
├── Part 4: 导出范畴构造
│   ├── 05QU: D(𝓐)的定义
│   ├── 05QV: 拟同构的局部化
│   ├── 05QW: D(𝓐)是三角范畴
│   └── 05QX: 典范t-结构
│
└── Part 5: 导出函子
    ├── 05QY: 右导出函子 RF
    ├── 05QZ: 左导出函子 LF
    ├── 05R0: 适应类
    └── 05R1: 复合函子的导出
```

### 依赖关系详解

| 前置概念 | 说明 | 在FormalMath中的位置 |
|----------|------|---------------------|
| Abel范畴 | 导出范畴的"原材料" | `concept/范畴论/Abel范畴.md` |
| 复形理论 | 链复形与上链复形 | `concept/同调代数/链复形.md` |
| 同调代数基础 | 长正合列、连接同态 | `docs/同调代数基础.md` |
| 范畴局部化 | 泛性质视角 | `concept/范畴论/范畴局部化.md` |
| Verdier商 | 三角范畴的商构造 | (待创建) |

---

## 4. 核心理论内容

### 4.1 三角范畴 (Triangulated Category)

#### 定义要素

三角范畴是一个加性范畴 𝒯 配备：

1. **平移自同构** [1]: 𝒯 → 𝒯
2. **杰出三角形** (distinguished triangles) 的类：X → Y → Z → X[1]

满足Verdier公理 (TR1-TR4)。

#### 核心公理

| 公理 | 名称 | 内容概述 |
|------|------|----------|
| TR1 | 存在性 | 每个态射可嵌入三角形；同构封闭；X → X → 0 → X[1] 杰出 |
| TR2 | 旋转 | X → Y → Z → X[1] 杰出 ⟺ Y → Z → X[1] → Y[1] 杰出 |
| TR3 | 态射 | 三角形的部分态射可扩展 |
| TR4 | 八面体 | 两个三角形的"粘合"性质 |

### 4.2 导出范畴 D(𝒜) 的构造

#### 构造步骤

```
Abel范畴 𝓐
    ↓
复形范畴 C(𝓐)      ← 对象：微分复形，态射：链映射
    ↓ 同伦等价
同伦范畴 K(𝓐)      ← 态射：链映射的同伦类
    ↓ 拟同构局部化
导出范畴 D(𝓐)      ← 态射： roofs / 分数形式
```

#### 拟同构 (Quasi-isomorphism)

链映射 f: X^• → Y^• 若在所有上同调度数诱导同构：

H^n(f): H^n(X^•) ≅ H^n(Y^•), ∀n

则称为**拟同构**。

#### 关键性质

| 性质 | 说明 |
|------|------|
| 上同调函子 | H^n: D(𝒜) → 𝒜 是良定义的 |
| 泛性质 | D(𝒜) 是使拟同构可逆的泛范畴 |
| t-结构 | 典范t-结构给出 hearts 与 𝒜 等价 |
| 有界性 | D^b(𝒜)、D^+(𝒜)、D^-(𝒜) |

### 4.3 导出函子

#### 动机

经典同调代数中，左/右正合函子 F: 𝒜 → ℬ 需要"导出"以得到长正合列。

#### 现代定义

对于左正合函子 F: 𝒜 → ℬ：

RF: D^+(𝒜) → D^+(ℬ)

是 K^+(F): K^+(𝒜) → K^+(ℬ) 的"右 Kan 扩展"。

#### 适应类 (Adapted Class)

ℛ ⊂ Ob(𝒜) 对左正合函子 F 是**适应的**，若：

1. 对任意 X ∈ Ob(𝒜)，存在单射 X ↪ R，R ∈ ℛ
2. 若 0 → R' → R → R'' → 0 正合且 R', R'' ∈ ℛ，则 R ∈ ℛ
3. F 保持 ℛ 中对象的短正合列

---

## 5. 与FormalMath的对应关系

### FormalMath相关文档

| 文档路径 | 内容对应 | 完成状态 |
|----------|----------|----------|
| `concept/同调代数/导出范畴.md` | 核心概念 | 🚧 部分完成 |
| `concept/同调代数/三角范畴.md` | 理论基础 | 🚧 部分完成 |
| `concept/范畴论/Abel范畴.md` | 基础范畴 | ✅ 已完成 |
| `concept/同调代数/链复形.md` | 构造原材料 | ✅ 已完成 |

### 概念映射

```yaml
Stacks Project Chapter 13:
  FormalMath对应:
    - concept: "三角范畴"
      path: "concept/同调代数/三角范畴.md"
      status: planned
    
    - concept: "导出范畴"
      path: "concept/同调代数/导出范畴.md"
      status: draft
      sections:
        - "同伦范畴"
        - "拟同构局部化"
        - "典范t-结构"
    
    - concept: "导出函子"
      path: "concept/同调代数/导出函子.md"
      status: planned
```

---

## 6. 应用与重要性

### 核心应用领域

#### 1. 代数几何

| 应用 | 说明 |
|------|------|
| 凝聚层的导出范畴 D^b_{coh}(X) | 研究代数簇的不变量 |
| Fourier-Mukai变换 | 导出范畴之间的等价 |
| 相交上同调 | 奇异簇的上同调理论 |
| Grothendieck对偶 | 相对对偶理论 |

#### 2. 代数拓扑

- **谱序列的导出解释：** Leray-Serre谱序列作为导出函子的复合
- **局部系数的导出：** 上同调的导出函子视角

#### 3. 表示论

- **导出有限维代数表示：** 倾斜理论 (Tilting Theory)
- **Koszul对偶：** 导出范畴等价

#### 4. D-模理论

Riemann-Hilbert对应：正则全纯D-模的导出范畴 ↔  perverse sheaves 的导出范畴

### 重要性评估

导出范畴理论被誉为**20世纪同调代数最重要的发展之一**：

1. **统一框架：** 统一Ext/Tor等传统导出函子理论
2. **几何革命：** 引发代数几何中"导出代数几何"的发展
3. **物理联系：** 弦理论中的镜像对称、D-膜
4. **表示论突破：** 导出等价比Morita等价更精细

---

## 7. 与其他资源的关联

### nLab 对应条目

| nLab页面 | URL | 特色 |
|----------|-----|------|
| derived category | https://ncatlab.org/nlab/show/derived+category | 高阶范畴视角 |
| triangulated category | https://ncatlab.org/nlab/show/triangulated+category | ∞-范畴联系 |
| localization | https://ncatlab.org/nlab/show/localization | 泛性质处理 |

**nLab特色：** 强调导出范畴作为 (∞,1)-范畴的截断，与稳定∞-范畴的联系。

### 经典教材与综述

| 文献 | 作者 | 特色 |
|------|------|------|
| Categories Derivees (原始论文) | Verdier (1963) | 奠基之作 |
| Triangulated Categories | Neeman | 现代标准参考 |
| Methods of Homological Algebra | Gelfand-Manin | 教材，详细证明 |
| Derived Categories | Huybrechts | 代数几何视角 |
| Fourier-Mukai Transforms | Huybrechts | 应用导向 |

### MathWorld / Wikipedia

- **Wikipedia:** Derived category - 基础介绍
- **MathWorld:** 无独立条目

### 历史背景

- **1963年:** Jean-Louis Verdier 在Grothendieck指导下完成博士论文，创立导出范畴理论
- **初衷：** 为Grothendieck对偶理论提供坚实基础
- **发展：** 1990年代后随镜像对称研究爆发式应用

---

## 8. Lean4形式化展望

### 当前形式化状态

| 项目 | 状态 | 说明 |
|------|------|------|
| mathlib4 | 🚧 进行中 | 部分同调代数基础 |
| Lean-Agda对比 | 研究阶段 | 已有Agda实现可参考 |

### mathlib4现状

mathlib4目前主要关注：
- 链复形 (Mathlib.Algebra.Homology.Homotopy)
- 同伦范畴的基础 (Mathlib.Algebra.Homology.HomotopyCategory)
- **导出范畴完整实现：** 尚未完成

### 形式化挑战

导出范畴的形式化面临以下挑战：

| 挑战 | 难度 | 可能的解决方案 |
|------|------|--------------|
| 集合论问题 | ⭐⭐⭐ | 使用Grothendieck宇宙或Type层次 |
| 局部化的泛性质 | ⭐⭐⭐⭐ | 依赖高阶范畴论框架 |
| 三角公理的验证 | ⭐⭐⭐ | 结构化证明，利用tactic自动化 |
| roofs计算 | ⭐⭐⭐⭐⭐ | 定义合适的等价关系 |

### 推荐形式化路线图

#### 阶段1：基础准备 (优先级：高)
- [ ] 完善链复形理论
- [ ] 完成同伦范畴的三角结构
- [ ] 定义乘法系的范畴论

#### 阶段2：三角范畴 (优先级：高)
- [ ] 三角范畴的公理系统
- [ ] 三角函子与精确函子
- [ ] Octahedral公理的验证

#### 阶段3：局部化 (优先级：高)
- [ ] Gabriel-Zisman局部化
- [ ] Verdier商构造
- [ ] 拟同构的乘法系验证

#### 阶段4：导出范畴 (优先级：中)
- [ ] D(𝒜) 的定义
- [ ] t-结构理论
- [ ]  hearts 等价于 𝒜

#### 阶段5：导出函子 (优先级：中)
- [ ] 适应类理论
- [ ] RF 和 LF 的构造
- [ ] 谱序列的联系

### Lean4代码框架建议

```lean4
-- 三角范畴的基础定义
class TriangulatedCategory (C : Type u) [Category.{v} C] [Preadditive C] where
  shift : C ⥤ C
  shiftEquiv : shift ⋙ shift ≅ 𝟭 C
  distinguishedTriangles : Set (Triangle C)
  -- TR1-TR4 公理
  mk_distinguished : ∀ {X Y : C} (f : X ⟶ Y), 
    ∃ Z g h, distinguishedTriangles ⟨X, Y, Z, f, g, h⟩
  -- ... 其他公理

-- 导出范畴定义为同伦范畴关于拟同构的局部化
structure DerivedCategory (A : Type u) [Category.{v} A] [Abelian A] where
  homotopyCategory : Type u := HomotopyCategory A
  quasiIsomorphisms : MorphismProperty (homotopyCategory)
  localization : homotopyCategory ⥤ DerivedCategory A
  isLocalization : IsLocalization quasiIsomorphisms localization
```

### 参考实现

- **UniMath (Coq):** 有导出范畴的完整实现
- **agda-unimath:** 同伦类型论视角的尝试
- ** Isabelle/HOL:** 部分同调代数形式化

---

## 参考链接

- **Stacks Project Chapter 13:** https://stacks.math.columbia.edu/chapter/13
- **Tag 05QI:** https://stacks.math.columbia.edu/tag/05QI
- **nLab - Derived Category:** https://ncatlab.org/nlab/show/derived+category
- **mathlib4 Homology:** https://leanprover-community.github.io/api/latest/Mathlib-Algebra-Homology.html

---

*文档创建日期：2026年4月*  
*FormalMath Stacks Project Tag解读系列*
