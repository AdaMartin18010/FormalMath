import os

def write_md(path, title, lean, background, intuition, formal, proof, examples, apps, concepts, refs):
    lines = [
        "---",
        "msc_primary: 00A99",
        "processed_at: '2026-04-15'",
        f"title: {title}",
        "---",
        f"# {title}",
        "",
        "## Mathlib4 引用",
        "",
        "```lean",
        lean,
        "```",
        "",
        "## 数学背景",
        "",
        background,
        "",
        "## 直观解释",
        "",
        intuition,
        "",
        "## 形式化表述",
        "",
        formal,
        "",
        "## 证明思路",
        "",
        proof,
        "",
        "## 示例",
        "",
        examples,
        "",
        "## 应用",
        "",
        apps,
        "",
        "## 相关概念",
        "",
        concepts,
        "",
        "## 参考",
        "",
        refs,
        "",
        "---",
        "",
        "*最后更新：2026-04-15 | 版本：v1.0.0*",
    ]
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f'Created {path}')

theorems = []

theorems.append((
    "LinearAlgebra/gram-schmidt-orthogonalization.md",
    "Gram-Schmidt 正交化 (Gram-Schmidt Orthogonalization)",
    "import Mathlib.LinearAlgebra.GramSchmidt\n\nnamespace GramSchmidtOrtho\n\nvariable {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]\n\n/-- Gram-Schmidt 正交化：将线性无关向量组转化为正交向量组 -/\nthegramSchmidt (f : ℕ → E) (n : ℕ) : E :=\n  f n - ∑ i in Finset.range n, orthogonalProjection (𝕜 ∙ gramSchmidt f i) (f n)\n\n/-- 正交性：不同下标的 Gram-Schmidt 向量两两正交 -/\ntheorem gramSchmidt_orthogonal (f : ℕ → E) {a b : ℕ} (h : a ≠ b) :\n    ⟪gramSchmidt f a, gramSchmidt f b⟫_𝕜 = 0 := by\n  -- 对 n 进行归纳证明\n  sorry\n\nend GramSchmidtOrtho",
    "Gram-Schmidt 正交化过程是线性代数和泛函分析中的经典算法，由丹麦数学家 Jørgen Pedersen Gram 和德国数学家 Erhard Schmidt 在19世纪末和20世纪初分别独立提出。该过程能够将内积空间中任意一组线性无关的向量转化为一组两两正交的向量组，进而通过单位化得到标准正交基。Gram-Schmidt 过程是量子力学、信号处理、数值分析和统计学中无数方法的基础。",
    "Gram-Schmidt 正交化的核心思想可以比喻为建筑中的'去相关性'过程。想象一组互相倾斜的支柱，它们虽然能支撑结构，但力的分析非常复杂。Gram-Schmidt 过程就像是一步一步地将每根支柱调整方向，使其与之前调整好的所有支柱都保持垂直。第一根支柱保持不变，第二根支柱减去它在第一根方向上的投影，第三根支柱减去它在第一、二根方向上的投影，依此类推。最终得到一组完全相互垂直的支柱，使得空间中的任何问题都可以在每个独立方向上一一解决。",
    "设 $V$ 是一个内积空间，$\\{v_1, v_2, \\dots, v_n\\}$ 是 $V$ 中线性无关的向量组。Gram-Schmidt 正交化过程定义正交向量组 $\\{u_1, u_2, \\dots, u_n\\}$ 如下：\n\n$$u_1 = v_1$$\n\n$$u_k = v_k - \\sum_{{j=1}}^{{k-1}} \\frac{{\\langle v_k, u_j \\rangle}}{{\\langle u_j, u_j \\rangle}} u_j, \\quad k = 2, 3, \\dots, n$$\n\n再令 $e_k = \\frac{{u_k}}{{||u_k||}}$，则 $\\{e_1, e_2, \\dots, e_n\\}$ 是一组标准正交基。\n\n其中：\n\n- $\\langle \\cdot, \\cdot \\rangle$ 表示内积\n- $||u_k|| = \\sqrt{{\\langle u_k, u_k \\rangle}}$ 是向量的范数\n- $\\frac{{\\langle v_k, u_j \\rangle}}{{\\langle u_j, u_j \\rangle}} u_j$ 是 $v_k$ 在 $u_j$ 方向上的正交投影",
    "1. **归纳构造**：从 $u_1 = v_1$ 开始，逐次构造 $u_2, u_3, \\dots$\n2. **正交投影**：对每个 $v_k$，减去它在已构造正交向量 $\\{u_1, \\dots, u_{{k-1}}\\}$ 张成子空间上的正交投影\n3. **正交性验证**：直接计算 $\\langle u_k, u_j \\rangle$ 可得零（对 $j < k$）\n4. **等价子空间**：证明 $\\text{span}\\{v_1, \\dots, v_k\\} = \\text{span}\\{u_1, \\dots, u_k\\}$ 对所有 $k$ 成立\n\n核心洞察在于从当前向量中系统性地移除所有已处理方向上的分量。",
    "### 示例 1：$\\mathbb{{R}}^2$ 中的正交化\n\n设 $v_1 = (1, 1)$, $v_2 = (1, 0)$。则 $u_1 = (1, 1)$，$u_2 = (1, 0) - \\frac{{1}}{{2}}(1, 1) = (\\frac{{1}}{{2}}, -\\frac{{1}}{{2}})$。验证：$u_1 \\cdot u_2 = \\frac{{1}}{{2}} - \\frac{{1}}{{2}} = 0$。单位化得 $e_1 = (\\frac{{1}}{{\\sqrt{2}}}, \\frac{{1}}{{\\sqrt{2}}})$，$e_2 = (\\frac{{1}}{{\\sqrt{2}}}, -\\frac{{1}}{{\\sqrt{2}}})$。\n\n### 示例 2：多项式空间的正交基\n\n在 $L^2([-1,1])$ 中对单项式 $1, x, x^2, \\dots$ 应用 Gram-Schmidt 过程，得到的是 Legendre 多项式（差一个归一化常数）。这是正交多项式理论的经典实例。\n\n### 示例 3：QR 分解\n\nGram-Schmidt 过程等价于矩阵的 QR 分解：对可逆矩阵 $A$，存在正交矩阵 $Q$ 和上三角矩阵 $R$ 使得 $A = QR$。$Q$ 的列就是经 Gram-Schmidt 过程得到的标准正交基。",
    "- **QR 分解**：数值线性代数中最重要的矩阵分解之一\n- **信号处理**：正交变换、滤波器组和小波分析\n- **量子力学**：态矢量的正交化和测量基的选择\n- **最小二乘法**：通过正交投影求解超定线性方程组\n- **数值积分**：高斯求积公式中 Legendre 多项式的构造",
    "- 内积空间 (Inner Product Space)：配备内积结构的向量空间\n- 正交基 (Orthogonal Basis)：两两正交的向量组构成的基\n- 标准正交基 (Orthonormal Basis)：范数均为 1 的正交基\n- 正交投影 (Orthogonal Projection)：向量在子空间上的最佳逼近\n- QR 分解 (QR Decomposition)：矩阵分解为正交矩阵与上三角矩阵的乘积",
    "### 教材\n\n- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 4.4]\n- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 6]\n\n### 在线资源\n\n- [Mathlib4 - GramSchmidt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/GramSchmidt.html)"
))

theorems.append((
    "LinearAlgebra/determinant-product.md",
    "行列式乘积公式 (Determinant Product Formula)",
    "import Mathlib.LinearAlgebra.Matrix.Determinant\n\nnamespace Matrix\n\nvariable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- 行列式乘积公式：det(AB) = det(A) det(B) -/\ntheorem det_mul (A B : Matrix n n R) :\n    det (A * B) = det A * det B := by\n  -- 利用行列式的多线性和交错性，或 Laplace 展开证明\n  sorry\n\nend Matrix",
    "行列式乘积公式是线性代数中的核心结果之一，它建立了矩阵乘法与行列式之间的基本联系：两个方阵乘积的行列式等于它们各自行列式的乘积。这一定理不仅在理论上深刻揭示了行列式作为群同态的性质（从一般线性群到乘法群），也是计算高阶行列式、研究特征多项式和矩阵相似不变量的基本工具。",
    "行列式乘积公式有一个非常直观的几何解释。行列式表示线性变换对体积的缩放比例。如果把矩阵 $A$ 看作是对空间的一次线性变换，矩阵 $B$ 看作是对同空间的另一次线性变换，那么先做 $B$ 再做 $A$（即 $AB$）的复合变换，对体积的总缩放比例显然应该等于两次变换各自缩放比例的乘积。就像先按 2 倍比例放大，再按 3 倍比例放大，总体效果就是 6 倍放大。这个公式正是这种直觉的严格数学表述。",
    "设 $A$ 和 $B$ 是域 $\\mathbb{{F}}$（或交换环 $R$）上的 $n \\times n$ 方阵，则：\n\n$$\\det(AB) = \\det(A) \\det(B)$$\n\n推论：\n\n1. $\\det(A^k) = (\\det A)^k$（对任意非负整数 $k$）\n2. 若 $A$ 可逆，则 $\\det(A^{{-1}}) = (\\det A)^{{-1}}$\n3. 若 $A$ 和 $B$ 相似，则 $\\det(A) = \\det(B)$\n\n其中：\n\n- $\\det(A)$ 表示方阵 $A$ 的行列式\n- $A, B \\in \\mathbb{{F}}^{{n \\times n}}$（或 $R^{{n \\times n}}$）\n- 该公式说明行列式映射 $\\det: GL_n(\\mathbb{{F}}) \\to \\mathbb{{F}}^\\times$ 是一个群同态",
    "1. **Binet-Cauchy 公式**：将 $\\det(AB)$ 展开为多重线性和交错形式\n2. **初等矩阵分解**：利用任何矩阵都可以分解为初等矩阵的乘积，而初等矩阵的行列式容易直接验证\n3. **归纳法**：对矩阵维数进行归纳，利用分块矩阵或 Laplace 展开\n4. **Leibniz 公式**：直接从行列式的置换定义出发计算 $\\det(AB)$\n\n核心洞察在于行列式是矩阵群到乘法群的同态映射。",
    "### 示例 1：2x2 矩阵验证\n\n设 $A = \\begin{{pmatrix}} 1 & 2 \\\\ 3 & 4 \\end{{pmatrix}}$, $B = \\begin{{pmatrix}} 0 & 1 \\\\ 2 & 3 \\end{{pmatrix}}$。\\n$\\det(A) = -2$, $\\det(B) = -2$, $\\det(A)\\det(B) = 4$。\\n$AB = \\begin{{pmatrix}} 4 & 7 \\\\ 8 & 15 \\end{{pmatrix}}$, $\\det(AB) = 60 - 56 = 4$。验证成立。\n\n### 示例 2：可逆矩阵的逆\n\n设 $A$ 可逆且 $\\det(A) = 5$。由 $AA^{{-1}} = I$ 得 $\\det(A)\\det(A^{{-1}}) = \\det(I) = 1$，因此 $\\det(A^{{-1}}) = 1/5$。\n\n### 示例 3：正交矩阵\n\n正交矩阵 $Q$ 满足 $Q^T Q = I$，因此 $\\det(Q)^2 = 1$，即 $\\det(Q) = \\pm 1$。这对应于正交变换保持体积（允许反射）的几何事实。",
    "- **特征多项式**：$\\det(AB - \\lambda I)$ 与 $\\det(A)\\det(B - \\lambda A^{{-1}})$ 的关系\n- **几何变换**：复合线性变换的体积缩放因子的计算\n- **微分方程**：Liouville 公式中基本解矩阵行列式的演化\n- **代数拓扑**：映射度（mapping degree）的计算和映射的复合\n- **编码理论**：某些线性码的校验矩阵行列式分析",
    "- 行列式 (Determinant)：方阵的反对称多重线性形式\n- 初等矩阵 (Elementary Matrix)：对应行/列初等变换的矩阵\n- 一般线性群 (General Linear Group)：可逆 $n \\times n$ 矩阵构成的群 $GL_n$\n- 特征多项式 (Characteristic Polynomial)：$p_A(\\lambda) = \\det(A - \\lambda I)$\n- Binet-Cauchy 公式：行列式乘积公式的更一般形式",
    "### 教材\n\n- [S. Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Section 10D]\n- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 5.2]\n\n### 在线资源\n\n- [Mathlib4 - Matrix Determinant](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html)"
))

theorems.append((
    "LinearAlgebra/cramers-rule.md",
    "Cramer 法则 (Cramer's Rule)",
    "import Mathlib.LinearAlgebra.Matrix.Adjugate\n\nnamespace Matrix\n\nvariable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- Cramer 法则：当 A 可逆时，线性方程组 Ax = b 的解为 x_i = det(A_i) / det(A) -/\ntheorem cramerRule (A : Matrix n n R) (b : n → R) (hA : IsUnit (det A)) (x : n → R)\n    (hx : A *ᵥ x = b) (i : n) :\n    x i = det (updateCol A i b) / det A := by\n  -- 利用伴随矩阵与逆矩阵的关系 A⁻¹ = adj(A) / det(A) 推导\n  sorry\n\nend Matrix",
    "Cramer 法则是线性代数中关于线性方程组求解的经典定理，由瑞士数学家 Gabriel Cramer 于1750年系统发表。该法则给出了当系数矩阵可逆时，$n$ 元线性方程组解的显式公式。虽然从计算复杂度角度看，Cramer 法则对于大规模方程组远不如高斯消元法高效，但它在理论分析、符号计算、微分几何和经济学中具有不可替代的价值，是理解线性方程组结构的重要工具。",
    "Cramer 法则提供了一个优雅但计算代价高昂的求解方法。想象一个由 $n$ 个方程和 $n$ 个未知数组成的线性系统，就像一个有 $n$ 个入口和 $n$ 个出口的复杂水管网络。Cramer 法则告诉我们：每个未知数的解，等于将网络中对应入口替换为输出流量后，新网络的'体积缩放因子'（行列式）与原网络体积缩放因子的比值。虽然这个公式非常优美，但当网络很大时，计算行列式的代价是惊人的——对于 $n$ 个变量，需要计算 $n+1$ 个 $n \\times n$ 行列式，其复杂度随 $n$ 阶乘增长。",
    "设 $A$ 是域 $\\mathbb{{F}}$ 上的 $n \\times n$ 可逆矩阵，$b \\in \\mathbb{{F}}^n$。则线性方程组 $Ax = b$ 的唯一解 $x = (x_1, x_2, \\dots, x_n)^T$ 满足：\n\n$$x_i = \\frac{{\\det(A_i)}}{{\\det(A)}}, \\quad i = 1, 2, \\dots, n$$\n\n其中 $A_i$ 是将矩阵 $A$ 的第 $i$ 列替换为向量 $b$ 后得到的矩阵：\n\n$$A_i = \\begin{{pmatrix}} a_{{11}} & \\cdots & b_1 & \\cdots & a_{{1n}} \\\\ \\vdots & \\ddots & \\vdots & \\ddots & \\vdots \\\\ a_{{n1}} & \\cdots & b_n & \\cdots & a_{{nn}} \\end{{pmatrix}}$$\n\n条件：$\\det(A) \\neq 0$（即 $A$ 可逆）。",
    "1. **逆矩阵公式**：利用 $x = A^{{-1}}b$ 和伴随矩阵公式 $A^{{-1}} = \\frac{{1}}{{\\det(A)}} \\text{adj}(A)$\n2. **伴随矩阵展开**：$\\text{adj}(A)_{{ji}} = (-1)^{{i+j}}M_{{ij}}$，其中 $M_{{ij}}$ 是余子式\n3. **Laplace 展开**：将 $\\det(A_i)$ 按第 $i$ 列展开，恰好等于 $(\\text{adj}(A) \\cdot b)_i$\n4. **整理得结论**：$x_i = \\frac{{(\\text{adj}(A) \\cdot b)_i}}{{\\det(A)}} = \\frac{{\\det(A_i)}}{{\\det(A)}}$\n\n核心洞察在于伴随矩阵的列恰好编码了对应列被替换后的行列式变化。",
    "### 示例 1：2x2 方程组\n\n设 $A = \\begin{{pmatrix}} 2 & 1 \\\\ 1 & 3 \\end{{pmatrix}}$, $b = \\begin{{pmatrix}} 5 \\\\ 8 \\end{{pmatrix}}$。\\n$\\det(A) = 5$。\\n$A_1 = \\begin{{pmatrix}} 5 & 1 \\\\ 8 & 3 \\end{{pmatrix}}$, $\\det(A_1) = 7$。\\n$A_2 = \\begin{{pmatrix}} 2 & 5 \\\\ 1 & 8 \\end{{pmatrix}}$, $\\det(A_2) = 11$。\\n因此 $x_1 = 7/5$, $x_2 = 11/5$。\\n验证：$2(7/5) + 11/5 = 25/5 = 5$ ✓。\n\n### 示例 2：经济模型\n\n在投入产出分析中，Leontief 模型 $x = Ax + d$ 可化为 $(I-A)x = d$。Cramer 法则理论上可以给出各行业产出的显式表达式，尽管实际计算中通常使用数值方法。\n\n### 示例 3：几何应用\n\n求过三点 $(x_1,y_1), (x_2,y_2), (x_3,y_3)$ 的圆的方程可以通过将圆的一般方程系数视为未知数，建立线性方程组后用 Cramer 法则求解。",
    "- **符号计算**：计算机代数系统中精确求解小型线性方程组\n- **微分几何**：曲线和曲面理论中的参数计算\n- **经济学**：投入产出分析和均衡价格的显式表示\n- **控制理论**：传递函数和状态空间方程的解析求解\n- **插值理论**：多项式插值和样条曲线的系数确定",
    "- 行列式 (Determinant)：方阵的体积缩放因子和可逆性判别\n- 伴随矩阵 (Adjugate Matrix)：由余子式转置构成的矩阵\n- 逆矩阵 (Inverse Matrix)：满足 $AA^{{-1}} = I$ 的唯一矩阵\n- 线性方程组 (System of Linear Equations)：$Ax = b$ 形式的方程组\n- 高斯消元法 (Gaussian Elimination)：大规模线性方程组的高效数值解法",
    "### 教材\n\n- [G. Strang. Introduction to Linear Algebra. Wellesley-Cambridge, 5th edition, 2016. Section 5.3]\n- [S. Axler. Linear Algebra Done Right. Springer, 3rd edition, 2015. Section 10C]\n\n### 在线资源\n\n- [Mathlib4 - Matrix Adjugate](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html)"
))

theorems.append((
    "LinearAlgebra/fredholm-alternative.md",
    "Fredholm 择一性 (Fredholm Alternative)",
    "import Mathlib.LinearAlgebra.Matrix.NonsingularInverse\n\nnamespace LinearMap\n\nvariable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]\n  [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]\n\n/-- Fredholm 择一性：对有限维空间上的线性映射 T，\n    方程 Tx = y 有解当且仅当 y 与 T 的伴随核正交 -/\ntheorem fredholm_alternative {T : E →ₗ[𝕜] F} {y : F} :\n    (∃ x : E, T x = y) ↔ (∀ z : F, (adjoint T) z = 0 → ⟪z, y⟫_𝕜 = 0) := by\n  -- 利用值域与核的正交补关系证明\n  sorry\n\nend LinearMap",
    "Fredholm 择一性是泛函分析和线性代数中的基本定理，由瑞典数学家 Erik Ivar Fredholm 在研究积分方程时于1900年左右建立。该定理在有限维情形下表述为：对于线性映射 $T: E \\to F$，方程 $Tx = y$ 要么有解，要么存在 $z \\in F^*$ 使得 $T^* z = 0$ 但 $\\langle z, y \\rangle \\neq 0$（两种情况恰好居其一）。这一定理将存在性问题转化为正交性条件，是偏微分方程、数值分析和量子力学中的重要工具。",
    "Fredholm 择一性可以形象地理解为：如果一个线性系统 $Tx = y$ 没有解，那么一定是 $y$ 中包含了某些 $T$ 的\"盲向\"——即那些 $T$ 完全无法\"看到\"或生成的方向。定理告诉我们，只要将 $y$ 中与这些盲向相关的分量去除（即 $y$ 与 $T$ 的伴随核正交），解就必然存在。这种\"非此即彼\"的二元性是线性问题的核心特征之一。在工程应用中，这意味着如果一个结构在某种载荷下无法达到平衡，那么必然存在一个与该载荷\"共振\"的虚位移模式。",
    "设 $T: E \\to F$ 是有限维内积空间之间的线性映射，$T^*: F \\to E$ 是其伴随映射。则以下两个命题有且仅有一个成立：\n\n1. 对给定的 $y \\in F$，方程 $Tx = y$ 有解 $x \\in E$\n2. 存在 $z \\in F$ 满足 $T^* z = 0$ 但 $\\langle z, y \\rangle \\neq 0$\n\n等价表述：$Tx = y$ 有解当且仅当 $y \\perp \\ker(T^*)$。\n\n在矩阵形式下，设 $A \\in \\mathbb{{R}}^{{m \\times n}}$，则：\n\n$$Ax = b \\text{ 有解 } \\iff b \\perp \\ker(A^T)$$\n\n其中：\n\n- $\\ker(T^*) = \\{z \\in F : T^* z = 0\\}$ 是伴随映射的核空间\n- $\\perp$ 表示在内积意义下的正交",
    "1. **正交补分解**：在有限维内积空间中，$F = \\text{Im}(T) \\oplus \\ker(T^*)$\n2. **必要性**：若 $Tx = y$，则对任意 $z \\in \\ker(T^*)$ 有 $\\langle z, y \\rangle = \\langle z, Tx \\rangle = \\langle T^* z, x \\rangle = 0$\n3. **充分性**：若 $y \\perp \\ker(T^*)$，则 $y \\in \\ker(T^*)^\\perp = \\text{Im}(T)$，故存在 $x$ 使 $Tx = y$\n4. **互斥性**：若两者同时成立会导致 $\\langle z, y \\rangle = 0$ 的矛盾\n\n核心洞察在于值域与伴随核构成空间的正交直和分解。",
    "### 示例 1：超定方程组\n\n设 $A = \\begin{{pmatrix}} 1 & 1 \\\\ 1 & -1 \\\\ 2 & 0 \\end{{pmatrix}}$, $b = \\begin{{pmatrix}} 3 \\\\ 1 \\\\ 4 \\end{{pmatrix}}$。$A^T$ 的核由 $(1, 1, -1)^T$ 张成。验证 $b \\cdot (1, 1, -1) = 0$，故 $Ax = b$ 有解（实际上 $x = (2, 1)^T$）。\n\n### 示例 2：微分方程中的 Green 函数\n\n在边值问题 $Lu = f$ 中，Fredholm 择一性说明解存在的充要条件是 $f$ 与齐次伴随问题 $L^* v = 0$ 的所有解正交。这是构造 Green 函数和求解非齐次边值问题的基础。\n\n### 示例 3：弹性力学\n\n在结构力学中，如果外力做功在任意刚体位移上为零，则平衡方程有解。这对应于 Fredholm 择一性中 $b \\perp \\ker(A^T)$ 的物理意义。",
    "- **偏微分方程**：椭圆型方程边值问题的可解性理论\n- **数值分析**：有限元方法中离散方程组的可解性分析\n- **量子力学**：本征值问题和微扰理论中的能级分裂\n- **积分方程**：第二类 Fredholm 积分方程的解理论\n- **结构力学**：弹性体平衡方程和相容性条件的研究",
    "- 伴随算子 (Adjoint Operator)：在内积空间中对偶的线性映射\n- 核空间 (Kernel/Null Space)：映射为零向量的原像集合\n- 值域 (Range/Image)：映射所有像的集合\n- 正交补 (Orthogonal Complement)：与给定子空间正交的所有向量\n- Green 函数 (Green's Function)：非齐次微分方程的积分核表示",
    "### 教材\n\n- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 19]\n- [E. Kreyszig. Introductory Functional Analysis with Applications. Wiley, 1978. Chapter 8]\n\n### 在线资源\n\n- [Mathlib4 - LinearMap](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra.html)"
))

theorems.append((
    "LinearAlgebra/gershgorin-disc-theorem.md",
    "Gershgorin 圆盘定理 (Gershgorin Disc Theorem)",
    "import Mathlib.LinearAlgebra.Eigenspace.Basic\n\nnamespace Matrix\n\nvariable {𝕜 : Type*} [Field 𝕜] [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- Gershgorin 圆盘定理：矩阵的每个特征值至少落在某一个 Gershgorin 圆盘内 -/\ntheorem gershgorin_disc {A : Matrix n n 𝕜} {λ : 𝕜} (hλ : ∃ v, v ≠ 0 ∧ A *ᵥ v = λ • v) :\n    ∃ i : n, |λ - A i i| ≤ ∑ j in (Finset.univ.erase i), |A i j| := by\n  -- 从特征向量的最大分量出发，利用特征方程推导\n  sorry\n\nend Matrix",
    "Gershgorin 圆盘定理由俄罗斯/苏联数学家 Semyon Aronovich Gershgorin 于1931年提出，是矩阵特征值定位理论中最优美且实用的结果之一。该定理无需实际计算特征值，仅凭矩阵元素的绝对值就能给出特征值所在区域的一个简单估计。这一定理在数值线性代数、控制理论、电路分析和量子化学中具有广泛应用，是特征值扰动分析和迭代法收敛性判定的基本工具。",
    "Gershgorin 圆盘定理提供了一种非常直观的特征值定位方法。想象一个城市的地图，每个十字路口对应矩阵的一个对角元，而通向其他路口的道路宽度对应非对角元的绝对值。Gershgorin 定理说：城市的所有\"热点\"（特征值）必定位于以某个十字路口为中心、以该路口所有 outgoing 道路总宽度为半径的某个圆盘内。这是一个极其强大的定性结论——即使我们不知道精确的热点位置，也能迅速圈定它们可能出现的区域。",
    "设 $A = (a_{{ij}})$ 是一个 $n \\times n$ 复方阵。定义第 $i$ 个 Gershgorin 圆盘为：\n\n$$D_i = \\left\\{ z \\in \\mathbb{{C}} : |z - a_{{ii}}| \\leq \\sum_{{j \\neq i}} |a_{{ij}}| \\right\\}, \\quad i = 1, 2, \\dots, n$$\n\nGershgorin 圆盘定理断言：矩阵 $A$ 的每一个特征值 $\\lambda$ 都至少落在某一个圆盘 $D_i$ 中。\n\n若 $k$ 个圆盘构成一个连通区域，且与其他圆盘不相交，则该区域恰好包含 $k$ 个特征值（计重数）。\n\n其中：\n\n- $a_{{ii}}$ 是圆盘中心（第 $i$ 个对角元）\n- $R_i = \\sum_{{j \\neq i}} |a_{{ij}}|$ 是第 $i$ 个圆盘的半径（第 $i$ 行非对角元绝对值之和）",
    "1. **取特征向量**：设 $v$ 是特征值 $\\lambda$ 对应的特征向量，取 $|v_i| = \\max_j |v_j|$\n2. **特征方程**：由 $(Av)_i = \\lambda v_i$ 得 $\\sum_j a_{{ij}} v_j = \\lambda v_i$\n3. **整理**：$(\\lambda - a_{{ii}}) v_i = \\sum_{{j \\neq i}} a_{{ij}} v_j$\n4. **取模与放缩**：$|\\lambda - a_{{ii}}| \\cdot |v_i| \\leq \\sum_{{j \\neq i}} |a_{{ij}}| \\cdot |v_j| \\leq \\sum_{{j \\neq i}} |a_{{ij}}| \\cdot |v_i|$\n5. **约去 $|v_i|$**：因 $v_i \\neq 0$，得 $|\\lambda - a_{{ii}}| \\leq R_i$\n\n核心洞察在于特征向量的最大分量对应的行天然提供了特征值的位置约束。",
    "### 示例 1：2x2 矩阵\n\n设 $A = \\begin{{pmatrix}} 4 & 1 \\\\ 2 & 3 \\end{{pmatrix}}$。\\n$D_1$：中心 4，半径 1。$D_2$：中心 3，半径 2。\\n两个圆盘相交，特征值在 $D_1 \\cup D_2$ 中。实际特征值为 5 和 2，分别落在两个圆盘中。\n\n### 示例 2：严格对角占优矩阵\n\n若 $|a_{{ii}}| > \\sum_{{j \\neq i}} |a_{{ij}}|$ 对所有 $i$ 成立，则所有 Gershgorin 圆盘都不包含原点，因此矩阵可逆。这是判断矩阵非奇异的快速充分条件。\n\n### 示例 3：摄动分析\n\n设 $A$ 是某物理系统的哈密顿量矩阵。Gershgorin 圆盘可以给出系统能级（特征值）在给定参数摄动下的变化范围，而无需重新对角化。",
    "- **数值线性代数**：迭代法收敛性分析和预处理技术设计\n- **控制理论**：系统稳定性判据和极点配置\n- **电路分析**：振荡电路和滤波器的特征频率范围估计\n- **量子化学**：Hückel 理论和分子轨道能量的定性分析\n- **振动分析**：机械系统固有频率的范围估计和模态分析",
    "- 特征值 (Eigenvalue)：矩阵变换下的不变方向上的缩放因子\n- 特征向量 (Eigenvector)：对应特征值的非零不变方向\n- 严格对角占优 (Strictly Diagonally Dominant)：$|a_{{ii}}| > \\sum_{{j \\neq i}} |a_{{ij}}|$\n- 谱半径 (Spectral Radius)：特征值模的最大值\n- 圆盘定理 (Disc Theorem)：Brauer 卵形等更精细的特征值定位结果",
    "### 教材\n\n- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 6]\n- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Section 7.1]\n\n### 在线资源\n\n- [Mathlib4 - Eigenspace](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Basic.html)"
))

theorems.append((
    "LinearAlgebra/qr-decomposition.md",
    "QR 分解 (QR Decomposition)",
    "import Mathlib.LinearAlgebra.Matrix.QR\n\nnamespace Matrix\n\nvariable {𝕜 : Type*} [IsROrC 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]\n\n/-- QR 分解：列满秩矩阵可分解为正交矩阵 Q 和上三角矩阵 R 的乘积 -/\ntheorem qr_decomposition (A : Matrix m n 𝕜) (hrank : A.rank = n) :\n    ∃ (Q : Matrix m m 𝕜) (R : Matrix m n 𝕜),\n      Q.orthonormalColumns ∧ R.upperTriangular ∧ A = Q * R := by\n  -- 利用 Gram-Schmidt 正交化过程构造 Q 和 R\n  sorry\n\nend Matrix",
    "QR 分解是数值线性代数中最重要、应用最广泛的矩阵分解之一。它将一个列满秩矩阵分解为一个正交（或酉）矩阵 $Q$ 和一个上三角矩阵 $R$ 的乘积。QR 分解最早由 Schmidt 和 Gram 在研究正交化过程中奠基，后由 Francis 和 Kublanovskaya 在1960年代发展为求解特征值问题的 QR 算法。如今，QR 分解是求解最小二乘问题、特征值计算、信号处理和数值优化的核心工具。",
    "QR 分解可以直观地理解为将一组倾斜的坐标轴转化为标准正交坐标轴的过程。想象一个由矩阵列向量张成的平行多面体，它的体积可能扭曲变形。QR 分解将这个变换分解为两步：第一步 $R$ 是在原有倾斜坐标轴内的伸缩和剪切（上三角矩阵保持了坐标的层次结构），第二步 $Q$ 是一个刚体旋转或反射（正交变换保持长度和角度），将倾斜轴对齐到标准正交轴。这种分解使得很多原本复杂的问题（如求解线性方程组、计算投影）变得异常简单。",
    "设 $A$ 是一个 $m \\times n$（$m \\geq n$）的列满秩实（或复）矩阵，则存在分解：\n\n$$A = QR$$\n\n其中：\n\n- $Q$ 是 $m \\times m$ 正交矩阵（实情形）或酉矩阵（复情形），满足 $Q^T Q = I$（或 $Q^* Q = I$）\n- $R$ 是 $m \\times n$ 上三角矩阵（当 $m > n$ 时，下半部分为零）\n\n经济型 QR 分解：$A = Q_1 R_1$，其中 $Q_1$ 是 $m \\times n$ 列正交矩阵，$R_1$ 是 $n \\times n$ 上三角矩阵。\n\n若 $A$ 的列向量为 $a_1, a_2, \\dots, a_n$，则 QR 分解等价于对这组向量应用 Gram-Schmidt 正交化：$Q$ 的列是标准正交化后的向量，$R$ 记录了原向量在新基下的坐标。",
    "1. **Gram-Schmidt 正交化**：对 $A$ 的列向量逐列进行正交化，得到标准正交列向量组 $q_1, \\dots, q_n$\n2. **构造 Q**：将 $q_1, \\dots, q_n$ 扩充为 $\\mathbb{{R}}^m$ 的标准正交基，组成矩阵 $Q$\n3. **构造 R**：令 $R_{{ij}} = \\langle q_i, a_j \\rangle$（当 $i \\leq j$），$R_{{ij}} = 0$（当 $i > j$）\n4. **验证**：直接计算 $(QR)_j = \\sum_i R_{{ij}} q_i = a_j$\n\n数值计算中通常使用 Householder 反射或 Givens 旋转来避免 Gram-Schmidt 的数值不稳定性。",
    "### 示例 1：最小二乘问题\n\n求 $\\min_x ||Ax - b||_2$。利用 QR 分解 $A = QR$，问题化为 $\\min_x ||Rx - Q^T b||_2$。由于 $R$ 是上三角矩阵，可以通过回代法快速求解。\n\n### 示例 2：2x2 矩阵的 QR 分解\n\n设 $A = \\begin{{pmatrix}} 3 & 1 \\\\ 4 & 2 \\end{{pmatrix}}$。通过 Gram-Schmidt 过程：$q_1 = (3/5, 4/5)^T$，$q_2 = (-4/5, 3/5)^T$。\\n$Q = \\begin{{pmatrix}} 3/5 & -4/5 \\\\ 4/5 & 3/5 \\end{{pmatrix}}$, $R = \\begin{{pmatrix}} 5 & 11/5 \\\\ 0 & 2/5 \\end{{pmatrix}}$。验证 $QR = A$。\n\n### 示例 3：特征值计算\n\nQR 算法通过反复计算 $A_k = Q_k R_k$，然后令 $A_{{k+1}} = R_k Q_k$，在正交相似变换下收敛到上三角（或拟上三角）矩阵，其对角元即为特征值。这是现代数值软件计算矩阵特征值的标准方法。",
    "- **最小二乘法**：超定线性方程组的最优解计算\n- **特征值算法**：QR 算法——计算矩阵全部特征值的标准方法\n- **信号处理**：自适应滤波、波束形成和子空间方法\n- **数值优化**：非线性最小二乘问题（如 Levenberg-Marquardt 算法）\n- **机器学习**：主成分分析（PCA）和正交回归",
    "- 正交矩阵 (Orthogonal Matrix)：列向量构成标准正交基的方阵\n- 酉矩阵 (Unitary Matrix)：复数域上的正交矩阵\n- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方元素全为零的矩阵\n- Gram-Schmidt 正交化 (Gram-Schmidt Process)：构造正交基的标准算法\n- Householder 变换 (Householder Reflection)：数值稳定的 QR 分解实现方法",
    "### 教材\n\n- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 5]\n- [L. N. Trefethen, D. Bau. Numerical Linear Algebra. SIAM, 1997. Lectures 7-10]\n\n### 在线资源\n\n- [Mathlib4 - Matrix QR](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/QR.html)"
))

theorems.append((
    "LinearAlgebra/lu-decomposition.md",
    "LU 分解 (LU Decomposition)",
    "import Mathlib.LinearAlgebra.Matrix.Block\n\nnamespace Matrix\n\nvariable {R : Type*} [Field R] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- LU 分解：可逆矩阵在某些条件下可分解为下三角矩阵 L 和上三角矩阵 U 的乘积 -/\ntheorem lu_decomposition (A : Matrix n n R)\n    (h : ∀ k, IsUnit (A.submatrix (fun i => i.1) (fun j => j.1) : Matrix (Fin k) (Fin k) R)) :\n    ∃ (L : Matrix n n R) (U : Matrix n n R),\n      L.lowerTriangular ∧ L.diag = 1 ∧ U.upperTriangular ∧ A = L * U := by\n  -- 利用高斯消元法，将消元矩阵的乘积记录为 L\n  sorry\n\nend Matrix",
    "LU 分解是数值线性代数中最基础且高效的矩阵分解方法之一，由英国数学家 Alan Turing 和德国数学家 John von Neumann 等人在20世纪上半叶系统发展。该分解将方阵表示为一个下三角矩阵 $L$ 和一个上三角矩阵 $U$ 的乘积（有时还包括置换矩阵 $P$ 以处理主元为零的情况）。LU 分解是高斯消元法的矩阵形式，是求解线性方程组、计算行列式和矩阵求逆的核心算法，也是工程计算和科学模拟中不可或缺的工具。",
    "LU 分解的本质是将复杂的线性变换分解为两个更简单的步骤。想象解一个复杂的拼图：下三角矩阵 $L$ 代表了\"逐步揭示\"的过程——就像从上到下、从左到右依次确定拼图块的位置；上三角矩阵 $U$ 则代表了\"最终形状\"——一旦前面的块确定，后面的块就可以直接放置。在实际求解线性方程组 $Ax = b$ 时，LU 分解将问题转化为两个简单的三角方程组：先用前向替换解 $Ly = b$，再用回代解 $Ux = y$。这比每次都对 $A$ 做完整消元要高效得多，特别是当有多个右端项 $b$ 时。",
    "设 $A$ 是一个 $n \\times n$ 方阵。若 $A$ 的所有顺序主子式均非零，则存在唯一的 LU 分解：\n\n$$A = LU$$\n\n其中：\n\n- $L$ 是 $n \\times n$ 单位下三角矩阵（对角线元素全为 1，上三角部分全为 0）\n- $U$ 是 $n \\times n$ 上三角矩阵（下三角部分全为 0）\n\n更一般地，对任意可逆矩阵 $A$，存在带置换的 LU 分解（PLU 分解）：\n\n$$PA = LU$$\n\n其中 $P$ 是置换矩阵，用于行交换以确保数值稳定性。\n\n求解 $Ax = b$ 的步骤：\n1. 解 $Ly = Pb$（前向替换）\n2. 解 $Ux = y$（回代）",
    "1. **高斯消元**：对 $A$ 进行高斯消元，将其化为上三角矩阵 $U$\n2. **记录乘子**：每次消元时用行 $i$ 消去行 $j$ 的元素，乘子 $l_{{ji}} = a_{{ji}}^{{(i)}} / a_{{ii}}^{{(i)}}$ 记录在 $L$ 的 $(j, i)$ 位置\n3. **构造 L**：$L$ 的对角线为 1，下三角部分为相应的消元乘子\n4. **唯一性**：在顺序主子式非零的条件下，单位下三角的 $L$ 和 Upper 的 $U$ 唯一确定\n\n核心洞察在于高斯消元的每一步都可以用一个初等下三角矩阵表示，其逆矩阵的乘积即为 $L$。",
    "### 示例 1：3x3 矩阵的 LU 分解\n\n设 $A = \\begin{{pmatrix}} 2 & 1 & 1 \\\\ 4 & 3 & 3 \\\\ 8 & 7 & 9 \\end{{pmatrix}}$。\\n经高斯消元得 $U = \\begin{{pmatrix}} 2 & 1 & 1 \\\\ 0 & 1 & 1 \\\\ 0 & 0 & 2 \\end{{pmatrix}}$，消元乘子构成 $L = \\begin{{pmatrix}} 1 & 0 & 0 \\\\ 2 & 1 & 0 \\\\ 4 & 3 & 1 \\end{{pmatrix}}$。验证 $LU = A$。\n\n### 示例 2：多重右端项\n\n在结构分析中，刚度矩阵 $K$ 固定，但需要计算多种载荷 $f_1, f_2, \\dots, f_m$ 下的位移。先对 $K$ 做 LU 分解（一次性成本 $O(n^3)$），然后对每个 $f_i$ 用前向/回代求解（成本 $O(n^2)$），总成本远低于每次重新消元。\n\n### 示例 3：行列式计算\n\n$\\det(A) = \\det(L) \\det(U) = 1 \\cdot \\prod_{{i=1}}^n u_{{ii}} = \\prod_{{i=1}}^n u_{{ii}}$。LU 分解将行列式计算简化为上三角对角元的乘积。",
    "- **科学计算**：大规模线性方程组的数值求解\n- **工程仿真**：有限元分析和计算流体力学中的系统求解\n- **电路仿真**：SPICE 等电路分析程序的核心求解器\n- **优化算法**：内点法和序列二次规划中的 KKT 系统求解\n- **统计计算**：线性回归和方差分析中的正规方程求解",
    "- 高斯消元法 (Gaussian Elimination)：将矩阵化为三角形的标准算法\n- 下三角矩阵 (Lower Triangular Matrix)：主对角线上方元素全为零的矩阵\n- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方元素全为零的矩阵\n- 置换矩阵 (Permutation Matrix)：表示行/列交换的矩阵\n- 顺序主子式 (Leading Principal Minor)：矩阵左上角子矩阵的行列式",
    "### 教材\n\n- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 3]\n- [L. N. Trefethen, D. Bau. Numerical Linear Algebra. SIAM, 1997. Lectures 20-22]\n\n### 在线资源\n\n- [Mathlib4 - Matrix Block](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html)"
))

theorems.append((
    "LinearAlgebra/polar-decomposition.md",
    "极分解 (Polar Decomposition)",
    "import Mathlib.LinearAlgebra.Matrix.PolarDecomposition\n\nnamespace Matrix\n\nvariable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- 极分解：任意复方阵可唯一分解为酉矩阵与正定Hermite矩阵的乘积 -/\ntheorem polar_decomposition (A : Matrix n n 𝕜) :\n    ∃! (U : Matrix n n 𝕜) (P : Matrix n n 𝕜),\n      U.unitary ∧ P.positiveSemidefiniteHermitian ∧ A = U * P := by\n  -- 利用 A*A 的谱分解构造 P = sqrt(A*A)，再定义 U = A P^{-1}\n  sorry\n\nend Matrix",
    "极分解是矩阵理论和泛函分析中的基本定理，它将任意复方阵唯一分解为一个酉矩阵（或正交矩阵）和一个半正定 Hermite 矩阵（或对称半正定矩阵）的乘积。这一定理可以看作复数极坐标形式 $z = re^{{i\\theta}}$ 在矩阵上的推广：酉矩阵对应于旋转/反射（相位），半正定矩阵对应于伸缩（幅度）。极分解在量子力学、弹性力学、信号处理和数值分析中有广泛应用。",
    "极分解提供了一个优雅的几何视角来理解任意线性变换。任何一个线性变换都可以看作是先在一个"标准"方向上对各轴进行非负伸缩（半正定矩阵 $P$），然后再进行一个保持长度和角度的刚体旋转或反射（酉矩阵 $U$）。这与复数的极坐标 $z = re^{{i\\theta}}$ 完全类似：$P$ 就像半径 $r$（在各个方向上可能有不同的伸缩系数），$U$ 就像单位复数 $e^{{i\\theta}}$（旋转）。这种分解揭示了线性变换的深层结构——任何变换都是"伸缩后旋转"，或者等价地，"旋转后伸缩"。",
    "设 $A$ 是一个 $n \\times n$ 复方阵，则存在唯一的极分解：\n\n$$A = UP$$\n\n其中：\n\n- $U$ 是 $n \\times n$ 酉矩阵，满足 $U^* U = I$\n- $P$ 是 $n \\times n$ 半正定 Hermite 矩阵，$P = \\sqrt{{A^* A}}$\n\n若 $A$ 可逆，则 $U = A P^{{-1}}$ 也是唯一的。\n\n对称地，也存在右极分解 $A = P' U$，其中 $P' = \\sqrt{{A A^*}}$。\n\n在实数情形下，$U$ 是正交矩阵，$P$ 是对称半正定矩阵。\n\n其中：\n\n- $A^*$ 表示 $A$ 的共轭转置\n- $\\sqrt{{A^* A}}$ 表示矩阵 $A^* A$ 的唯一半正定平方根",
    "1. **构造 P**：定义 $P = \\sqrt{{A^* A}}$，其中 $A^* A$ 是半正定 Hermite 矩阵，存在唯一的半正定平方根\n2. **验证范数**：$||Pv|| = ||Av||$ 对所有 $v$ 成立，说明 $P$ 和 $A$ 有相同的零空间结构\n3. **定义 U**：在 $\\text{Im}(P)$ 上定义 $U(Pv) = Av$，在 $\\ker(P)$ 上任意延拓为酉映射\n4. **唯一性**：若 $A = U_1 P_1 = U_2 P_2$，则 $P_1^2 = A^* A = P_2^2$，由半正定平方根的唯一性得 $P_1 = P_2$，进而 $U_1 = U_2$\n\n核心洞察在于 $A^* A$ 的谱分解提供了变换的\"伸缩幅度\"信息。",
    "### 示例 1：2x2 实矩阵\n\n设 $A = \\begin{{pmatrix}} 1 & 2 \\\\ 3 & 4 \\end{{pmatrix}}$。\\n$A^T A = \\begin{{pmatrix}} 10 & 14 \\\\ 14 & 20 \\end{{pmatrix}}$，特征值为 $15 \\pm \\sqrt{221}$。\\n$P = \\sqrt{{A^T A}}$ 是正定的，$U = A P^{{-1}}$ 是正交矩阵。验证 $UP = A$。\n\n### 示例 2：量子力学中的密度矩阵\n\n在量子态的算符表示中，任意算符可以分解为酉演化（$U$）和测量/衰减（$P$）的乘积。极分解在研究开放量子系统和量子信道时具有基本重要性。\n\n### 示例 3：弹性力学\n\n在连续介质力学中，变形梯度张量 $F$ 的极分解 $F = RU = VR$ 将变形分解为纯旋转 $R$ 和纯拉伸 $U, V$。这是分析材料应力-应变关系的基础。",
    "- **量子力学**：量子态变换的酉部分和衰减部分的分解\n- **弹性力学**：变形梯度张量的旋转-拉伸分解\n- **信号处理**：协方差矩阵和滤波器设计的结构分析\n- **数值分析**：矩阵条件和摄动分析\n- **算子理论**：Hilbert 空间上有界算子的标准分解",
    "- 酉矩阵 (Unitary Matrix)：保持内积不变的复方阵\n- Hermite 矩阵 (Hermitian Matrix)：满足 $A = A^*$ 的复方阵\n- 半正定矩阵 (Positive Semidefinite Matrix)：所有特征值非负的 Hermite 矩阵\n- 谱定理 (Spectral Theorem)：Hermite 矩阵可对角化的基本定理\n- 奇异值分解 (SVD)：与极分解密切相关的矩阵分解",
    "### 教材\n\n- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 7]\n- [P. Lax. Functional Analysis. Wiley, 2002. Chapter 30]\n\n### 在线资源\n\n- [Mathlib4 - Matrix Polar Decomposition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PolarDecomposition.html)"
))

theorems.append((
    "LinearAlgebra/schur-decomposition.md",
    "Schur 分解 (Schur Decomposition)",
    "import Mathlib.LinearAlgebra.Matrix.Schur\n\nnamespace Matrix\n\nvariable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- Schur 分解：任意复方阵可酉相似于上三角矩阵 -/\ntheorem schur_decomposition (A : Matrix n n 𝕜) :\n    ∃ (U : Matrix n n 𝕜) (T : Matrix n n 𝕜),\n      U.unitary ∧ T.upperTriangular ∧ A = U * T * Uᴴ := by\n  -- 对维数 n 进行归纳，利用特征向量的存在性和酉扩充\n  sorry\n\nend Matrix",
    "Schur 分解是线性代数中的经典结果，由德国数学家 Issai Schur 于1909年证明。该定理断言：任意复方阵都可以通过酉相似变换化为上三角矩阵。这一定理是矩阵标准型理论的重要里程碑，为谱分析、矩阵函数计算和数值算法提供了强有力的工具。与 Jordan 标准型相比，Schur 分解在数值计算中更加稳定，因为它是通过酉变换（保持范数）实现的，而 Jordan 标准型中的相似矩阵可能是高度病态的。",
    "Schur 分解告诉我们：虽然一般的复方阵不一定能对角化，但它总可以"近似对角化"为一个上三角矩阵。想象一个复杂的线性变换，它可能在某些方向上存在"耦合"——即变换一个向量时，它会沿着其他方向也产生分量。Schur 分解通过巧妙地选择一个酉坐标系（保持几何结构的旋转/反射），将这些耦合全部压缩到上三角部分。在这个坐标系中，矩阵的对角线元素仍然是特征值，而所有非对角元素代表了特征方向之间的相互作用。这使得很多理论分析和数值计算变得可行。",
    "设 $A$ 是一个 $n \\times n$ 复方阵，则存在酉矩阵 $U$ 和上三角矩阵 $T$，使得：\n\n$$A = U T U^*$$\n\n其中：\n\n- $U$ 是 $n \\times n$ 酉矩阵，满足 $U^* U = U U^* = I$\n- $T$ 是 $n \\times n$ 上三角矩阵\n- $U^*$ 表示 $U$ 的共轭转置\n- $T$ 的对角线元素 $t_{{ii}}$ 就是 $A$ 的特征值（可任意排列）\n\n若 $A$ 是实矩阵且所有特征值都是实数，则 $U$ 可取为正交矩阵。\n\n对于一般实矩阵，存在拟 Schur 分解（实 Schur 形式），其中 $T$ 是拟上三角矩阵（对角块为 $1 \\times 1$ 或 $2 \\times 2$ 块，后者对应一对共轭复特征值）。",
    "1. **归纳基础**：$1 \\times 1$ 矩阵本身就是上三角的\n2. **特征向量**：由代数基本定理，$A$ 至少有一个特征值 $\\lambda$ 和对应的单位特征向量 $v$\n3. **酉扩充**：将 $v$ 扩充为 $\\mathbb{{C}}^n$ 的标准正交基，构成酉矩阵 $U_1$\n4. **分块化**：$U_1^* A U_1 = \\begin{{pmatrix}} \\lambda & * \\\\ 0 & A_1 \\end{{pmatrix}}$，其中 $A_1$ 是 $(n-1) \\times (n-1)$ 矩阵\n5. **归纳步骤**：对 $A_1$ 应用归纳假设，得到其 Schur 分解，然后组合得到 $A$ 的 Schur 分解\n\n核心洞察在于通过特征向量逐步"剥离"特征值，同时保持变换的酉等价性。",
    "### 示例 1：不可对角化矩阵的 Schur 分解\n\n设 $A = \\begin{{pmatrix}} 1 & 1 \\\\ 0 & 1 \\end{{pmatrix}}$。这是 Jordan 块，本身已是上三角矩阵。取 $U = I$，则 $T = A$ 就是 Schur 分解。\n\n### 示例 2：正规矩阵的特殊性\n\n若 $A$ 是正规矩阵（$A^* A = A A^*$），则 Schur 分解中的上三角矩阵 $T$ 实际上是对角矩阵。这说明正规矩阵必可对角化，且特征向量构成标准正交基。\n\n### 示例 3：实 Schur 形式\n\n设 $A = \\begin{{pmatrix}} 0 & 1 \\\\ -1 & 0 \\end{{pmatrix}}$，特征值为 $\\pm i$。其拟 Schur 分解为 $A = Q R Q^T$，其中 $Q$ 是正交矩阵，$R = A$ 本身就是 $2 \\times 2$ 的拟上三角块。",
    "- **数值线性代数**：QR 算法和特征值计算的理论基础\n- **矩阵函数**：通过上三角化计算矩阵指数、对数和幂次\n- **控制理论**：Riccati 方程和 Lyapunov 方程的数值求解\n- **信号处理**：协方差矩阵的特征结构和谱估计\n- **量子计算**：量子门的分解和量子电路设计",
    "- 酉相似 (Unitary Similarity)：通过酉矩阵进行的相似变换\n- 上三角矩阵 (Upper Triangular Matrix)：主对角线下方全为零的矩阵\n- 正规矩阵 (Normal Matrix)：满足 $A^* A = A A^*$ 的矩阵\n- 拟上三角矩阵 (Quasi-Upper Triangular Matrix)：允许 $2 \\times 2$ 对角块的实上三角形式\n- QR 算法 (QR Algorithm)：基于 Schur 分解计算特征值的迭代算法",
    "### 教材\n\n- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Chapter 7]\n- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 2]\n\n### 在线资源\n\n- [Mathlib4 - Matrix Schur](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Schur.html)"
))

theorems.append((
    "LinearAlgebra/matrix-exponential-theorem.md",
    "矩阵指数定理 (Matrix Exponential)",
    "import Mathlib.Analysis.NormedSpace.Exponential\n\nnamespace Matrix\n\nvariable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]\n\n/-- 矩阵指数：exp(A) = Σ_{k=0}^∞ A^k / k! -/\nnoncomputable def exp (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=\n  ∑' k : ℕ, (1 / k.factorial) • A^k\n\n/-- 矩阵指数的微分性质：d/dt exp(tA) = A exp(tA) -/\ntheorem deriv_matrix_exponential (A : Matrix n n 𝕜) (t : 𝕜) :\n    deriv (fun s => exp (s • A)) t = A * exp (t • A) := by\n  -- 利用幂级数在收敛圆盘内的逐项可微性证明\n  sorry\n\nend Matrix",
    "矩阵指数是数学分析、线性代数和微分方程理论中的核心概念，它将标量指数函数 $e^x$ 自然地推广到方阵情形。矩阵指数最早由意大利数学家 Giuseppe Peano 和法国数学家 Marie Ennemond Camille Jordan 在19世纪末系统研究。矩阵指数是求解线性常微分方程组、李群李代数理论、控制理论和量子力学的基本工具。矩阵指数的微分性质 $\\frac{{d}}{{dt}}e^{{tA}} = A e^{{tA}}$ 与标量情形完全类似，是连接离散代数结构与连续动力系统的重要桥梁。",
    "矩阵指数可以看作是"连续复合线性变换"的数学表达。想象矩阵 $A$ 描述了一个微小的瞬时变化（如速度场），那么 $e^{{tA}}$ 就表示经过时间 $t$ 后的累积效应。这与银行存款的复利计算完全类似：标量指数 $e^{{rt}}$ 表示连续复利增长，而矩阵指数 $e^{{tA}}$ 则表示多个相互耦合的方向上的连续线性演化。例如，在弹簧-质点系统中，矩阵指数可以给出系统从任意初始状态出发，经过任意时间后的精确位置。",
    "设 $A$ 是一个 $n \\times n$ 复方阵，其指数定义为幂级数：\n\n$$e^A = \\sum_{{k=0}}^\\infty \\frac{{A^k}}{{k!}} = I + A + \\frac{{A^2}}{{2!}} + \\frac{{A^3}}{{3!}} + \\cdots$$\n\n该级数对任意方阵 $A$ 绝对收敛。\n\n基本性质：\n\n1. $e^0 = I$\n2. $\\frac{{d}}{{dt}} e^{{tA}} = A e^{{tA}} = e^{{tA}} A$\n3. 若 $AB = BA$，则 $e^{{A+B}} = e^A e^B$\n4. $(e^A)^{{-1}} = e^{{-A}}$\n5. $\\det(e^A) = e^{{\\text{tr}(A)}}$（Liouville 公式）\n\n线性微分方程组 $\\frac{{dx}}{{dt}} = Ax$，$x(0) = x_0$ 的唯一解为 $x(t) = e^{{tA}} x_0$。\n\n其中：\n\n- $A^k$ 表示矩阵 $A$ 的 $k$ 次幂\n- 级数收敛性由矩阵范数的比较判别法保证",
    "1. **级数收敛**：利用矩阵范数的次乘性 $||A^k|| \\leq ||A||^k$，与标量指数级数比较得绝对收敛\n2. **逐项微分**：在收敛域内对幂级数逐项求导，得到 $\\frac{{d}}{{dt}} e^{{tA}} = A e^{{tA}}$\n3. **交换性条件**：若 $AB = BA$，通过二项式定理展开 $(A+B)^k$ 证明 $e^{{A+B}} = e^A e^B$\n4. **Liouville 公式**：对 $X(t) = e^{{tA}}$ 应用行列式导数公式，结合 $\\det(e^A) = e^{{\\text{tr}(A)}}$\n\n核心洞察在于矩阵指数的解析性质与标量指数高度平行。",
    "### 示例 1：对角矩阵\n\n若 $A = \\text{diag}(\\lambda_1, \\dots, \\lambda_n)$，则 $e^A = \\text{diag}(e^{{\\lambda_1}}, \\dots, e^{{\\lambda_n}})$。这直接验证了矩阵指数是对角元素分别取指数的自然推广。\n\n### 示例 2：Jordan 块\n\n对 $J = \\begin{{pmatrix}} \\lambda & 1 \\\\ 0 & \\lambda \\end{{pmatrix}}$，有 $e^J = e^\\lambda \\begin{{pmatrix}} 1 & 1 \\\\ 0 & 1 \\end{{pmatrix}}$。这说明非对角化矩阵的矩阵指数会出现多项式项。\n\n### 示例 3：旋转矩阵\n\n设 $A = \\begin{{pmatrix}} 0 & -\\theta \\\\ \\theta & 0 \\end{{pmatrix}}$，则 $e^A = \\begin{{pmatrix}} \\cos\\theta & -\\sin\\theta \\\\ \\sin\\theta & \\cos\\theta \\end{{pmatrix}}$。这对应于平面上的角度为 $\\theta$ 的旋转。",
    "- **线性微分方程**：常系数线性 ODE 系统解的显式表示\n- **李群与李代数**：矩阵李群（如 $SO(n)$、$SU(n)$）的指数映射\n- **控制理论**：线性时不变系统的状态转移矩阵\n- **量子力学**：时间演化算符 $U(t) = e^{{-iHt/\\hbar}}$\n- **图网络分析**：图上热核和随机游走的连续时间推广",
    "- 幂级数 (Power Series)：矩阵指数的级数定义基础\n- Jordan 标准型 (Jordan Normal Form)：计算矩阵指数的标准方法\n- 状态转移矩阵 (State Transition Matrix)：控制系统中的 $\\Phi(t) = e^{{At}}$\n- Liouville 公式：$\\det(e^A) = e^{{\\text{tr}(A)}}$\n- Lie 指数公式 (Lie Product Formula)：$e^{{A+B}} = \\lim_{{n \\to \\infty}} (e^{{A/n}} e^{{B/n}})^n$",
    "### 教材\n\n- [R. A. Horn, C. R. Johnson. Topics in Matrix Analysis. Cambridge, 1991. Chapter 6]\n- [L. Perko. Differential Equations and Dynamical Systems. Springer, 3rd edition, 2001. Section 1.3]\n\n### 在线资源\n\n- [Mathlib4 - Exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Exponential.html)"
))

for args in theorems:
    write_md(*args)
