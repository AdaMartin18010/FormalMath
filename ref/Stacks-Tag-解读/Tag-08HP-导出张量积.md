# Stacks Project Tag 08HP - 导出张量积

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 08HP |
| **定义名称** | 导出张量积 ⊗^L (Derived Tensor Product) |
| **所属章节** | Section 15.58 - Derived Tensor Product (More on Algebra) |
| **数学领域** | 同调代数、导出范畴、代数几何 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/08HP |

## 2. 定理/定义原文

**定义 (Tag 08HP):**

设 $(\mathcal{C}, \mathcal{O})$ 是环化空间，$K^\bullet, L^\bullet$ 是 $\mathcal{O}$-模的复形。定义**导出张量积**：

$$K^\bullet \otimes^L_{\mathcal{O}} L^\bullet$$

为复形 $K^\bullet \otimes_{\mathcal{O}} P^\bullet$，其中 $P^\bullet \to L^\bullet$ 是K-平坦消解（即 $P^\bullet$ K-平坦且是拟同构）。

**等价定义:**

若 $Q^\bullet \to K^\bullet$ 是K-平坦消解，则：

$$K^\bullet \otimes^L_{\mathcal{O}} L^\bullet \;\cong\; Q^\bullet \otimes_{\mathcal{O}} L^\bullet$$

在导出范畴 $D(\mathcal{O})$ 中良定（即不依赖于K-平坦消解的选取）。

**Tor函子:**

对 $n \in \mathbb{Z}$，定义**超Tor函子**：

$$\text{Tor}^n_{\mathcal{O}}(K^\bullet, L^\bullet) := H^n(K^\bullet \otimes^L_{\mathcal{O}} L^\bullet)$$

**计算方式:**
- 若 $K^\bullet$ 或 $L^\bullet$ 由平坦模组成，则：
$$\text{Tor}^n(K^\bullet, L^\bullet) = H^n(K^\bullet \otimes L^\bullet)$$

## 3. 概念依赖图

```
导出张量积 (Tag 08HP)
│
├── 核心前置概念
│   ├── 环化空间 (Tag 006N)
│   ├── 导出范畴 D(𝒪) (Tag 08FR)
│   ├── K-平坦复形 (Tag 0641)
│   ├── 张量积复形 (Tag 0A99)
│   └── 拟同构 (Tag 05QR)
│
├── 经典Tor理论
│   ├── Tor函子 Tor_n (Tag 00LX)
│   ├── 平坦消解 (Tag 00MB)
│   ├── 投射消解 (Tag 00E1)
│   └── 平衡性 (Tag 00M6)
│
├── 导出函子技术
│   ├── 左导出函子 LF (Tag 05R1)
│   ├── 导出Hom RHom (Tag 08H4)
│   └── 伴随对 ⊗ ⊣ Hom (Tag 003L)
│
└── 后继应用
    ├── 完美复形 (Tag 08FT)
    ├── 投影公式 (Tag 01XY)
    └── 对偶复形
```

## 4. 证明概要

**存在性与良定性证明:**

**Step 1: K-平坦消解的存在性**
- 假设：有足够多平坦对象
- 利用Cartan-Eilenberg消解或类似技术构造K-平坦消解

**Step 2: 导出范畴的良定性**

**引理:** 若 $P^\bullet \to L^\bullet$ 和 $P'^\bullet \to L^\bullet$ 都是K-平坦消解，则：
$$K^\bullet \otimes P^\bullet \cong K^\bullet \otimes P'^\bullet \quad \text{在} \; D(\mathcal{O})$$

**证明要点:**
- 存在比较拟同构 $P^\bullet \to P'^\bullet$（或反之）
- 利用K-平坦性：$K^\bullet \otimes -$ 保持拟同构

**Step 3: 对称性**

**定理:** $K^\bullet \otimes^L L^\bullet \cong L^\bullet \otimes^L K^\bullet$（在导出范畴中）

**证明:**
- 取双K-平坦消解
- 利用张量积的交换性

**重要性质证明:**

**结合性:**
$$(K^\bullet \otimes^L L^\bullet) \otimes^L M^\bullet \cong K^\bullet \otimes^L (L^\bullet \otimes^L M^\bullet)$$

**与RHom的伴随:**
$$R\text{Hom}(K^\bullet \otimes^L L^\bullet, M^\bullet) \cong R\text{Hom}(K^\bullet, R\text{Hom}(L^\bullet, M^\bullet))$$

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 导出张量积 ⊗^L | 同调代数/导出张量积 | `concept/homological_algebra/derived_tensor_product.md` |
| Tor函子 | 同调代数/Tor | `concept/homological_algebra/tor_functor.md` |
| K-平坦复形 | 同调代数/K-平坦复形 | `concept/homological_algebra/kflat.md` |
| 平坦模 | 同调代数/平坦模 | `concept/homological_algebra/flat_module.md` |

**当前对齐状态:**
- ⚠️ **概念对齐** - 核心概念在文档中有描述，完整形式化待补充

**建议补充内容:**
```markdown
## 导出张量积详解

### 定义
设 $(X, \mathcal{O})$ 环化空间，$K^\bullet, L^\bullet$ 复形：
$$K^\bullet \otimes^L_{\mathcal{O}} L^\bullet := K^\bullet \otimes_{\mathcal{O}} P^\bullet$$
其中 $P^\bullet \to L^\bullet$ 是K-平坦消解。

### 良定性
导出范畴中不依赖于K-平坦消解的选取。

### Tor函子
$$\text{Tor}^n(K^\bullet, L^\bullet) = H^n(K^\bullet \otimes^L L^\bullet)$$

### 重要性质
1. **对称性:** $K^\bullet \otimes^L L^\bullet \cong L^\bullet \otimes^L K^\bullet$
2. **结合性:** $(K \otimes^L L) \otimes^L M \cong K \otimes^L (L \otimes^L M)$
3. **与RHom的伴随:** $R\text{Hom}(K \otimes^L L, M) \cong R\text{Hom}(K, R\text{Hom}(L, M))$

### 计算
若 $K^\bullet$ 由平坦模组成，则：
$$K^\bullet \otimes^L L^\bullet = K^\bullet \otimes L^\bullet$$
（无需导出）

### 应用
- 投影公式
- 完美复形的运算
- 对偶复形的构造
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 投影公式 (Tag 01XY)
- **定理:** 对态射 $f: X \to Y$，
$$Rf_*(K \otimes^L Lf^*M) \cong Rf_*K \otimes^L M$$
- 是导出张量积与 $Rf_*$ 交换性的表现

### 2. 完美复形 (Tag 08FT)
- 完美复形在 $\otimes^L$ 下封闭
- 判别：$K$ 完美 $\Leftrightarrow$ $K \otimes^L -$ 保持直和

### 3. 对偶复形
- Grothendieck对偶中的对偶化复形通过 $\otimes^L$ 作用
- $K_X = f^!\mathcal{O}_Y$ 满足 $R\text{Hom}(K, K_X) \cong R\text{Hom}(Rf_*K, \mathcal{O}_Y)$

### 4. 相交理论
- 用Tor计算子概形交的Tor项
- Serre的相交重数公式

### 5. 导出Morita理论
- 导出等价的构造
- 倾斜对象、生成元

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

导出张量积是同调代数的核心运算，是导出几何、表示论、数学物理的基本工具。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 08H4 | 导出Hom（伴随对） |
| Tag 0641 | K-平坦复形 |
| Tag 08FT | 完美复形 |
| Tag 01XY | 投影公式 |
| Tag 00LX | 经典Tor函子 |

### 外部资源

**经典文献:**
1. **Cartan & Eilenberg** "Homological Algebra"
   - 第VI章: 张量积的导出函子

2. **Verdier, J.-L.** "Des catégories dérivées..."
   - 导出范畴的奠基论文

**现代教材:**
1. **Gelfand & Manin** "Methods of Homological Algebra"
   - 第3章: 导出函子

2. **Kashiwara & Schapira** "Sheaves on Manifolds"
   - 第2章: 导出运算

3. **Lurie, J.** "Higher Algebra"
   - ∞-范畴中的导出张量积

### 相关理论
- **Derived algebraic geometry**: 导出代数几何
- **Fourier-Mukai transforms**: 用核的导出张量积定义
- **K-theory**: 导出范畴的K理论

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐☆ (4/5)

**主要挑战:**
1. **K-平坦消解** - 存在性构造
2. **良定性验证** - 不依赖于消解选取
3. **对称性证明** - 双K-平坦消解的选取
4. **与RHom的伴随** - 导出伴随的证明

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 导出张量积
section DerivedTensorProduct

variable {X : Type*} [TopologicalSpace X] (𝒪 : SheafOfRings X)

-- 导出张量积
def derivedTensorProduct
    (K : CochainComplex (Sheaf.Ab 𝒪))
    (L : CochainComplex (Sheaf.Ab 𝒪)) :
    DerivedCategory (Sheaf.Ab 𝒪) :=
  -- 取K-平坦消解后张量积
  let P := KFlatResolution L
  (K ⊗ P.1)  -- 在导出范畴中

-- 张量积符号
infixr:70 " ⊗^L " => derivedTensorProduct

-- Tor函子
def Tor (n : ℤ) (K L : CochainComplex (Sheaf.Ab 𝒪)) : Ab :=
  (K ⊗^L L).homology n

-- 对称性
theorem derivedTensor_symmetry (K L : CochainComplex (Sheaf.Ab 𝒪)) :
    K ⊗^L L ≅ L ⊗^L K := by
  sorry
  -- 需要双K-平坦消解

-- 结合性
theorem derivedTensor_associativity (K L M : CochainComplex (Sheaf.Ab 𝒪)) :
    (K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M) := by
  sorry

-- 与RHom的伴随
theorem tensor_hom_adjunction (K L M : DerivedCategory (Sheaf.Ab 𝒪)) :
    (K ⊗^L L) ⟶ M ≅ K ⟶ RHom L M := by
  sorry

end DerivedTensorProduct

-- 投影公式的陈述
theorem projection_formula {X Y : Scheme} (f : X ⟶ Y)
    (K : DerivedCategory (QCohSheaf X))
    (M : DerivedCategory (QCohSheaf Y)) :
    Rf_*(K ⊗^L Lf^* M) ≅ (Rf_* K) ⊗^L M := by
  sorry
```

**Mathlib现状:**
- `DerivedCategory` 在发展中
- 张量积的同调代数基础存在
- K-平坦消解需要新实现
- 导出张量积尚无现成API

**形式化优先级:** MEDIUM-HIGH
- 是同调代数的核心运算
- 依赖导出范畴的基础
- 建议在K-平坦理论完成后实现

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
