## Agent 任务指令：MIT 18.06 Lean4 代码补充（8篇核心文档）

**背景**: `E:\_src\FormalMath`
**目标**: 为 MIT 18.06 前8章核心文档嵌入可编译的 Lean4 代码框架
**已有**: 15篇银层文档已完成，但均无Lean4嵌入
**输出**: 直接修改现有文档，在对应位置插入Lean4代码块

**要求**:
1. 每篇文档至少嵌入 2–3 个 Lean4 代码块
2. 代码块必须与自然语言证明/定义逐段对应
3. 使用 ````lean4` 标记
4. 证明可用 `sorry` 占位，但需附注释说明完成计划
5. 优先使用 Mathlib4 已有定义

**文档清单**:
1. Ch01-线性方程组的几何.md — `LinearSystem`、解存在性
2. Ch02-矩阵消元法.md — `RowOperation`、RREF
3. Ch03-矩阵运算与逆矩阵.md — `Matrix.mul`、逆矩阵判定
4. Ch05-向量空间与子空间.md — `VectorSpace`、`Subspace`
5. Ch06-列空间与零空间.md — `colSpace`、`nullSpace`、`rank`
6. Ch08-线性无关基与维数.md — `LinearIndependent`、`Basis`
7. Ch12-行列式.md — `Matrix.det` 性质
8. Ch13-特征值与特征向量.md — `eigenvalues`、`eigenvectors`

**注意事项**:
- 不要删除或修改现有内容，只在适当位置插入代码块
- 保持文档整体风格一致
- 完成后汇报修改了多少篇、插入多少个代码块
