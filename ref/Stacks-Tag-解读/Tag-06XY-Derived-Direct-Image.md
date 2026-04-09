# Stacks Project Tag 06XY - 导出范畴中的Rf_*（直接像函子）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 06XY |
| **章节** | Chapter 20: Cohomology of Sheaves, Section 20.3 |
| **类型** | 定义 (Definition) + 引理 (Lemma) |
| **重要性** | ★★★★★ (核心工具) |
| **位置** | Cohomology, Section 20.3 |

## 2. 定理/定义原文

### 英文原文

**Definition 20.3.0.4.** Let $f : X \to Y$ be a morphism of ringed spaces. Then we have the left exact functor

$$f_* : \textit{Mod}(\mathcal{O}_X) \longrightarrow \textit{Mod}(\mathcal{O}_Y)$$

which gives rise to the **derived pushforward**

$$Rf_* : D^{+}(X) \longrightarrow D^{+}(Y)$$

The $i$th cohomology sheaf of $Rf_*\mathcal{F}^\bullet$ is denoted $R^if_*\mathcal{F}^\bullet$ and called the $i$th **higher direct image**.

**Lemma 06XY.** If $\mathcal{E}, \mathcal{F}$ are objects in $D^b_{coh}(X)$, if one of them consists of flat modules over $\mathcal{O}_X$, then

$$\mathcal{E} \otimes^{\mathbf{L}}_{\mathcal{O}_X} \mathcal{F} = \mathcal{E} \otimes_{\mathcal{O}_X} \mathcal{F}$$

### 中文翻译

**定义 20.3.0.4.** 设 $f : X \to Y$ 是环化空间的态射。则我们有左正合函子

$$f_* : \textit{Mod}(\mathcal{O}_X) \longrightarrow \textit{Mod}(\mathcal{O}_Y)$$

它导出**导出直接像**

$$Rf_* : D^{+}(X) \longrightarrow D^{+}(Y)$$

$Rf_*\mathcal{F}^\bullet$ 的第 $i$ 次上同调层记为 $R^if_*\mathcal{F}^\bullet$，称为第 $i$ 次**高阶直接像**。

**引理 06XY.** 若 $\mathcal{E}, \mathcal{F}$ 是 $D^b_{coh}(X)$ 中的对象，若其中之一由 $\mathcal{O}_X$ 上的平坦模组成，则

$$\mathcal{E} \otimes^{\mathbf{L}}_{\mathcal{O}_X} \mathcal{F} = \mathcal{E} \otimes_{\mathcal{O}_X} \mathcal{F}$$

## 3. 概念依赖图

```
                    导出直接像 Rf_*
                   (Derived Pushforward)
                           |
          +----------------+----------------+
          |                |                |
    层直接像 f_*      导出范畴 D^+       内射分解
    (Sheaf Direct    (Derived          (Injective
     Image)          Category)          Resolution)
          |                |                |
          +----------------+----------------+
                           |
                高阶直接像 R^i f_*
                           |
       +-------------------+-------------------+
       |                   |                   |
   直接像层            Leray谱序列        投影公式
   (Direct Image      (Leray Spec.     (Projection
    Sheaf)            Seq.)            Formula)
```

**前置概念：**
- 环化空间与层（Ringed Spaces and Sheaves）
- 导出范畴（Derived Categories）
- 内射分解（Injective Resolutions）
- 导出函子（Derived Functors）

**依赖此概念：**
- 凝聚层上同调
- 对偶理论（Duality Theory）
- 相交上同调
- Perverse sheaves

## 4. 证明概要

### 4.1 导出直接像的构造

**步骤1：** 验证 $f_*$ 是左正合的

对于短正合序列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，应用 $f_*$：

$$0 \to f_*\mathcal{F}' \to f_*\mathcal{F} \to f_*\mathcal{F}''$$

右边一般不满射，因此需要导出函子。

**步骤2：** 验证 $\textit{Mod}(\mathcal{O}_X)$ 有足够内射对象

- 这是Grothendieck范畴的标准性质
- 每个层都可以嵌入内射层

**步骤3：** 构造导出函子

对于复形 $\mathcal{F}^\bullet$，选择拟同构 $\mathcal{F}^\bullet \to \mathcal{I}^\bullet$，其中 $\mathcal{I}^\bullet$ 是有界 below 的内射复形。

定义：$Rf_*\mathcal{F}^\bullet = f_*\mathcal{I}^\bullet$

### 4.2 高阶直接像的几何意义

**引理：** 若 $\mathcal{F}$ 是 $X$ 上的层，则

$$(R^if_*\mathcal{F})_y = H^i(f^{-1}(y), \mathcal{F}|_{f^{-1}(y)})$$

**解释：** 高阶直接像描述纤维上的上同调如何"变化"。

### 4.3 平坦性条件

**Tag 06XY的引理**说明：当涉及平坦模时，导出张量积退化为普通张量积。

**证明思路：**
- 若 $\mathcal{E}$ 由平坦模组成，则 $-\otimes_{\mathcal{O}_X}\mathcal{E}$ 是正合的
- 因此不需要导出
- 导出张量积 $\otimes^{\mathbf{L}}$ 与普通张量积相同

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `RingedSpace` | 环化空间 $X, Y$ | `RingedSpace` |
| `Sheaf` | 层 $\mathcal{F}$ | `SheafOfModules` |
| `DerivedCategory` | $D^+(X)$ | `DerivedCategory` |
| `DerivedFunctor` | $Rf_*$ | `DerivedFunctor` |
| `InjectiveResolution` | 内射分解 | `InjectiveResolution` |

**mathlib4对应代码（计划中）：**
```lean
-- 导出直接像函子
def Rf_star {X Y : RingedSpace} (f : X ⟶ Y) : 
    DerivedCategory (SheafOfModules X.𝒪) ⥤ 
    DerivedCategory (SheafOfModules Y.𝒪) :=
  derivedFunctor f.star

-- 高阶直接像
def higherDirectImage {X Y : RingedSpace} (f : X ⟶ Y) (i : ℕ)
    (F : SheafOfModules X.𝒪) : SheafOfModules Y.𝒪 :=
  (Rf_star f (single 0 F)).homology i

-- 投影公式（重要性质）
theorem projection_formula {X Y : RingedSpace} (f : X ⟶ Y)
    (F : DerivedCategory (SheafOfModules X.𝒪))
    (G : DerivedCategory (SheafOfModules Y.𝒪)) :
    Rf_star f (F ⊗ᴸ f.starᴰ G) ≅ (Rf_star f F) ⊗ᴸ G := by
  sorry
```

## 6. 应用与重要性

### 6.1 Leray谱序列

**定理：** 对于态射复合 $X \xrightarrow{f} Y \xrightarrow{g} Z$，有谱序列：

$$E_2^{p,q} = R^pg_*(R^qf_*\mathcal{F}) \Rightarrow R^{p+q}(g \circ f)_*\mathcal{F}$$

这是计算复合态射上同调的强大工具。

### 6.2 凝聚性定理

**Grothendieck定理：** 设 $f : X \to Y$ 是固有态射，$\mathcal{F}$ 是凝聚层，则：
1. $R^if_*\mathcal{F}$ 是凝聚层
2. 若 $Y$ 是仿射的，$H^i(X, \mathcal{F})$ 是有限 $\mathcal{O}_Y(Y)$-模

这是代数几何中最重要的定理之一。

### 6.3 对偶理论

**Grothendieck对偶：** 对于固有态射 $f : X \to Y$，存在右伴随 $f^!$：

$$Rf_* : D^b_{coh}(X) \rightleftarrows D^b_{coh}(Y) : f^!$$

这推广了Serre对偶和Poincaré对偶。

### 6.4 应用实例

**例1：曲线上的线丛**

设 $f : X \to \text{Spec}(k)$，$\mathcal{L}$ 是线丛。则：
- $R^0f_*\mathcal{L} = H^0(X, \mathcal{L})$（整体截面）
- $R^1f_*\mathcal{L} = H^1(X, \mathcal{L})$（Riemann-Roch定理相关）

**例2：族的上同调**

对于平坦族 $f : X \to S$，$R^if_*\mathcal{O}_X$ 描述了上同调沿纤维的"变化"。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | III.8 | 高阶直接像 |
| Hartshorne | III.11 | 形式函数定理 |
| Grothendieck | EGA III | 完整理论 |
| Kashiwara-Schapira | Sheaves on Manifolds | 导出范畴观点 |
| Stacks | Tag 01F3 | 导出范畴基础 |
| Stacks | Tag 071J | 导出函子 |

**Stacks Project交叉引用：**
- Tag 01F3: 导出范畴
- Tag 0716: 导出函子构造
- Tag 071J: 环化空间的导出函子
- Tag 0B7C: Grothendieck谱序列

## 8. Lean4形式化展望

### 8.1 形式化挑战

1. **导出范畴的构造**
   - 同伦范畴的形式化
   - 拟同构的局部化

2. **内射对象的存在性**
   - Grothendieck范畴的性质
   - Godement构造

3. **谱序列的形式化**
   - 谱序列的范畴论
   - 收敛性理论

### 8.2 建议路线图

```lean
-- 阶段1: 导出范畴基础 (进行中)
class DerivedCategory (C : Type*) [Category C] [Abelian C]

-- 阶段2: 导出函子 (计划中)
class DerivedFunctor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Abelian C] [Abelian D] [EnoughInjectives C]

def derivedFunctor {C D : Type*} (F : C ⥤ D) [Abelian C] [Abelian D]
    [EnoughInjectives C] : DerivedCategory C ⥤ DerivedCategory D

-- 阶段3: 直接像函子 (计划中)
def directImageFunctor {X Y : RingedSpace} (f : X ⟶ Y) :
    SheafOfModules X.𝒪 ⥤ SheafOfModules Y.𝒪 := f.star

def Rf_star {X Y : RingedSpace} (f : X ⟶ Y) :
    DerivedCategory (SheafOfModules X.𝒪) ⥤ 
    DerivedCategory (SheafOfModules Y.𝒪) :=
  derivedFunctor (directImageFunctor f)

-- 阶段4: 应用定理 (远期)
theorem higherDirectImage_coherent {X Y : Scheme} (f : X ⟶ Y)
    [IsProper f] (F : SheafOfModules X.𝒪) [IsCoherent F] (i : ℕ) :
    IsCoherent (higherDirectImage f i F) := sorry
```

### 8.3 优先级建议

1. **高优先级：** 导出范畴的基本理论
2. **中优先级：** 导出直接像的定义
3. **长期目标：** 凝聚性定理、对偶理论

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
