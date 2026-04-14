import gen

gen.write_md(
    "LogicFoundation/godel-incompleteness-theorem.md",
    "Godel 不完备性定理 (Gödel's Incompleteness Theorem)",
    r"""import Mathlib.Logic.Godel.Incompleteness\n\nnamespace Logic\n\nvariable {T : Theory} [DecidablePred T] [Consistent T]\n  (hT : T ⊢₀ Arithmetic)\n\n/-- Godel 第一不完备性定理：任何包含算术的一致可公理化理论都不完备 -/\ntheorem godel_first_incompleteness :\n    ∃ φ : Sentence, ¬(T ⊢ φ) ∧ ¬(T ⊢ ¬φ) := by\n  -- 利用自指语句（Godel 语句）和可表示性定理构造不可判定命题\n  sorry\n\nend Logic""",
    r"""Gödel 不完备性定理是20世纪数学和逻辑学中最深刻、最具影响力的结果之一，由奥地利数学家库尔特·哥德尔（Kurt Gödel）于1931年发表。第一不完备性定理断言：任何包含基本算术的、一致的、可递归公理化的形式系统，都存在在该系统中既不能被证明也不能被否定的命题（即系统是不完备的）。第二不完备性定理进一步断言：这样的系统无法证明自身的一致性。Gödel 定理彻底粉碎了希尔伯特计划（试图将所有数学归结为有限、完备的形式系统）的梦想，深刻揭示了形式系统能力的根本局限。这一定理不仅在数学和逻辑学中具有核心地位，也对哲学、计算机科学和认知科学产生了深远影响。""",
    r"""Gödel 不完备性定理揭示了一个令人震惊的事实：任何足够强大且一致的形式数学系统都存在着"盲点"——有些命题在该系统内部永远无法被判定真假。想象你有一个非常复杂的计算机程序，它的任务是根据一套固定的规则来证明所有数学真理。Gödel 定理告诉我们：无论你如何精心设计这套规则（只要它能表达基本算术），总存在某个特殊的命题，你的程序永远无法证明它，也无法反驳它。这个特殊命题本质上是在说"我在这个系统内不可证"——一个巧妙的自指语句。这就像一幅画中画了一个画框，而画框里写着"这幅画不能被框住"。这种自我参照的悖论式结构是哥德尔证明的核心。""",
    r"""设 $T$ 是一个一阶理论，满足以下条件：

1. **包含算术**：$T$ 能表达 Peano 算术（或至少 Robinson 算术 $Q$）
2. **一致性**：$T$ 不能同时证明某个命题及其否定（$T$ 不会推出矛盾）
3. **可递归公理化**：$T$ 的公理集合是递归可枚举的（可以用计算机程序列出）

则：

**第一不完备性定理**：存在 $T$ 的语言中的一个语句 $G_T$（Gödel 语句），使得：

$$T \not\vdash G_T \quad \text{且} \quad T \not\vdash \neg G_T$$

即 $G_T$ 在 $T$ 中不可判定。$G_T$ 的直观含义是"我在 $T$ 中不可证"。

**第二不完备性定理**：$T$ 不能证明自身的一致性，即：

$$T \not\vdash \text{Con}(T)$$

其中 $\text{Con}(T)$ 是表示"$T$ 是一致的"的形式化语句。

推论：

- 没有足够强的、一致的数学形式系统能证明自己的一致性
- 任何试图将所有数学真理纳入一个有限公理系统的计划注定失败
- 但这并不意味着数学真理不可知，只是某些真理超出了特定形式系统的范围""",
    r"""1. **Gödel 编码**：将形式系统中的符号、公式和证明序列唯一地编码为自然数（Gödel 数），从而将元数学概念（如"是公式"、"是证明"）转化为算术谓词
2. **可表示性定理**：证明所有递归函数和递归关系都可以在算术系统中表示
3. **对角线引理（自指定理）**：对任何一元公式 $\psi(x)$，存在语句 $G$ 使得 $T \vdash G \leftrightarrow \psi(\ulcorner G \urcorner)$。取 $\psi(x)$ 为 "$x$ 在 $T$ 中不可证"，得到 Gödel 语句 $G_T$
4. **一致性假设的应用**：若 $T \vdash G_T$，则由 $G_T$ 的定义，$T$ 也证明 $G_T$ 不可证，矛盾。若 $T \vdash \neg G_T$，同样导出矛盾（在一致的前提下）
5. **第二定理**：利用可表示性，将"$T$ 证明 $G_T$"与"$T$ 证明 $\neg \text{Con}(T)$"联系起来

核心洞察在于通过数论编码将元数学的自我指涉转化为算术语言中的合法语句。""",
    r"""### 示例 1：Peano 算术

Peano 算术（PA）是一个满足 Gödel 定理条件的系统。存在 PA 语句 $G_{PA}$ 在 PA 中不可判定。然而，在更强的系统（如 ZFC 集合论）中，$G_{PA}$ 可以被证明为真。

### 示例 2：ZFC 集合论

ZFC（Zermelo-Fraenkel 带选择公理的集合论）若一致，则也是不完备的。而且 ZFC 不能证明自身的一致性。这意味着数学家永远无法在一个固定的形式系统内穷尽所有数学真理。

### 示例 3：停机问题

Gödel 不完备性定理与图灵的停机问题密切相关。停机问题的不可判定性可以看作是哥德尔定理在可计算性理论中的对应物：没有一个通用的算法能判定所有程序是否会停机。""",
    r"""- **数理逻辑**：形式系统局限性的深入研究
- **集合论**：大基数公理和独立性结果（如连续统假设）
- **计算机科学**：可计算性理论、停机问题和复杂度理论
- **人工智能**：机器是否能拥有真正创造力的哲学辩论
- **哲学**：人类心智与形式系统关系、数学实在论的讨论""",
    r"""- 形式系统 (Formal System)：由公理和推理规则构成的数学系统
- Gödel 编码 (Gödel Numbering)：将语法对象映射为自然数
- 自指 (Self-Reference)：语句涉及自身的可证性
- 可表示性定理 (Representability Theorem)：递归关系在算术中的可定义性
- 停机问题 (Halting Problem)：图灵证明的不可判定问题""",
    r"""### 教材

- [P. Smith. An Introduction to Gödel's Theorems. Cambridge, 2007]
- [S. C. Kleene. Introduction to Metamathematics. North-Holland, 1952. Chapter XIV]

### 在线资源

- [Stanford Encyclopedia of Philosophy - Gödel's Incompleteness Theorems](https://plato.stanford.edu/entries/goedel-incompleteness/)"""
)

gen.write_md(
    "LogicFoundation/compactness-theorem.md",
    "紧致性定理 (Compactness Theorem)",
    r"""import Mathlib.ModelTheory.Satisfiability\n\nnamespace ModelTheory\n\nvariable {L : Language} {T : Theory L}\n\n/-- 紧致性定理：理论可满足当且仅当每个有限子集可满足 -/\ntheorem compactness :\n    Satisfiable T ↔ ∀ (T' : Finset (Sentence L)), (T' ⊆ T) → Satisfiable T' := by\n  -- 利用完备性定理和证明的有限性，或超积/拓扑方法证明\n  sorry\n\nend ModelTheory""",
    r"""紧致性定理是数理逻辑和模型论中的核心结果之一，由挪威逻辑学家托拉尔夫·斯科伦（Thoralf Skolem）在20世纪20年代首次证明，后由库尔特·哥德尔（Kurt Gödel）和安纳托利·马尔采夫（Anatoly Maltsev）以不同方式重新证明和推广。该定理断言：一阶逻辑中的理论 $T$ 有模型（是可满足的）当且仅当它的每个有限子集都有模型。换句话说，无限理论的语义可满足性完全由其有限子集决定。紧致性定理是 Gödel 完备性定理的直接推论（因为形式证明只涉及有限多个前提），也可以利用超积、拓扑学（紧致性）或图着色等组合方法独立证明。这一定理是模型论、非标准分析和组合数学的基石。""",
    r"""紧致性定理提供了一个强大的工具来判断复杂理论是否有模型。想象你有一本无限厚的规则书（一个无限理论），你想知道是否存在一个世界能同时满足书中的所有规则。直接检查无限规则似乎不可能，但紧致性定理告诉我们：你不需要一次性检查所有规则！只要你能证明书中的任何有限页（有限子理论）都不会自相矛盾（都有模型），那么整本书就一定有一个模型。这就像在玩一个无限拼图游戏：如果你总能拼好任何有限块的组合，那么整个无限拼图也一定可以被完成。这个定理在数学中开辟了一个新世界——它允许我们通过局部一致性来推断全局存在性。""",
    r"""设 $L$ 是一阶语言，$T$ 是 $L$ 中的理论（可能是无限语句集）。紧致性定理断言：

$$T \text{ 有模型} \quad \Longleftrightarrow \quad T \text{ 的每个有限子集都有模型}$$

等价表述：

1. $T$ 是一致的（不推出矛盾）当且仅当每个有限子集是一致的
2. 若 $T \models \varphi$（$T$ 语义蕴涵 $\varphi$），则存在 $T$ 的有限子集 $T_0$ 使得 $T_0 \models \varphi$

其中：

- "有模型"意味着存在一个 $L$-结构 $M$ 使得 $M \models T$
- 该定理仅对一阶逻辑成立。对二阶逻辑不成立
- 从拓扑角度看，一阶语句的模型空间在某种自然拓扑下是紧致的，这解释了定理的名称

重要推论：

- **Löwenheim-Skolem 定理**：若一个理论有无限模型，则它有任意大的无限模型和可数模型
- **非标准模型**：存在包含无穷小和无穷大元素的非标准算术和实数模型""",
    r"""1. **通过完备性定理证明**：若 $T$ 的每个有限子集都可满足，则每个有限子集都一致。由于证明只使用有限个前提，$T$ 本身也一致。由完备性定理，$T$ 可满足
2. **超积证明（代数方法）**：利用 Łoś 定理，构造一个由 $T$ 的所有有限子集的模型组成的超积。该超积自动满足 $T$ 中的所有语句
3. **拓扑证明（Stone 空间）**：考虑所有极大一致理论构成的 Stone 空间。该空间在特定拓扑下是紧致的，而紧致性定理正是这个拓扑紧致性的代数翻译
4. **图论/组合证明（De Bruijn-Erdős）**：对无限图，若每个有限子图都是 $k$-可着色的，则整个图也是 $k$-可着色的。这是紧致性定理在图论中的具体体现

核心洞察在于一阶语句的局部性和有限性：任何一阶语句的真假只依赖于有限多个元素和有限深度的量化。""",
    r"""### 示例 1：非标准算术

考虑 Peano 算术 PA 加上无限多个新常数符号 $c$ 和语句 $c > n$（对所有标准自然数 $n$）。任何有限子集只涉及有限多个这样的不等式，因此可以在标准自然数模型中解释 $c$ 为一个足够大的数。由紧致性定理，整个理论有模型——这就是非标准算术模型，其中包含比所有标准自然数都大的无穷大自然数。

### 示例 2：非标准实数（非标准分析）

类似地，在实数理论中加入一个常数 $\varepsilon$ 和语句 $0 < \varepsilon < 1/n$（对所有 $n \geq 1$）。任何有限子集都可满足，因此由紧致性定理，存在包含真正无穷小量的非标准实数模型 $^*\mathbb{R}$。

### 示例 3：四色定理的推广

De Bruijn-Erdős 定理断言：若一个无限平面图的每个有限子图都是 4-可着色的，则整个无限平面图也是 4-可着色的。这是紧致性定理在图论中的一个优美应用。""",
    r"""- **模型论**：非标准模型、饱和模型和超结构理论的基础
- **非标准分析**：无穷小、无穷大数和标准部分的严格数学理论
- **组合数学**：无限图、超图和Ramsey理论的扩展
- **代数**：代数闭域、实闭域和赋值理论的模型存在性
- **经济学**：Arrow 不可能定理和社会选择理论中的紧致性论证""",
    r"""- 可满足性 (Satisfiability)：存在模型使所有语句为真
- 完备性定理 (Completeness Theorem)：紧致性定理的等价形式基础
- 超积 (Ultraproduct)：构造非标准模型的代数工具
- Stone 空间 (Stone Space)：命题逻辑模型的紧致拓扑空间
- Löwenheim-Skolem 定理：紧致性定理的重要推论""",
    r"""### 教材

- [H. B. Enderton. A Mathematical Introduction to Logic. Academic Press, 2nd edition, 2001. Chapter 2]
- [W. Hodges. A Shorter Model Theory. Cambridge, 1997. Chapter 6]

### 在线资源

- [Mathlib4 - Satisfiability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Satisfiability.html)"""
)

gen.write_md(
    "LogicFoundation/loewenheim-skolem-theorem.md",
    "Löwenheim-Skolem 定理 (Löwenheim-Skolem Theorem)",
    r"""import Mathlib.ModelTheory.Skolem\n\nnamespace ModelTheory\n\nvariable {L : Language} {T : Theory L}\n\n/-- 向下 Löwenheim-Skolem 定理：若理论有无限模型，则有任意大基数的模型 -/\ntheorem downward_loewenheim_skolem {M : Type*} [Structure L M] [Infinite M] (hM : M ⊨ T)\n    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκ_le : κ ≤ Cardinal.mk M) :\n    ∃ (N : Type*) [Structure L N] [M ⊨ T], Cardinal.mk N = κ := by\n  -- 利用 Skolem 函数和子结构的初等嵌入构造所需基数的模型\n  sorry\n\nend ModelTheory""",
    r"""Löwenheim-Skolem 定理是数理逻辑和模型论中最重要的结果之一，由德国逻辑学家利奥波德·勒文海姆（Leopold Löwenheim）于1915年首次证明（向下版本：若一个理论有模型，则它有可数模型），后由挪威数学家托拉尔夫·斯科伦（Thoralf Skolem）在1920年推广和完善。该定理有两个互补的形式：

- **向下 Löwenheim-Skolem 定理**：若一个一阶理论有无限模型，则对任何无限基数 $\kappa \geq |L|$，它有一个基数恰好为 $\kappa$ 的模型
- **向上 Löwenheim-Skolem 定理**：若一个一阶理论有无限模型，则对任何大于等于该模型基数的基数，它都有相应基数的模型

Löwenheim-Skolem 定理揭示了形式理论与模型结构之间的深刻分离：一阶语言无法区分不同大小的无限结构。这一定理对集合论（Skolem 悖论）、代数（非标准模型）和数学基础产生了深远影响。""",
    r"""Löwenheim-Skolem 定理揭示了一个反直觉但极其重要的现象：一阶逻辑无法区分不同大小的无限。想象你有一个数学理论（如实数域的代数理论），它能描述实数的许多性质。你可能会认为，既然实数是不可数的，那么任何满足这个理论的模型都必须是不可数的。但 Löwenheim-Skolem 定理告诉我们：如果理论是一阶的，那么它一定也有可数的模型！这就像你试图用一阶语言捕捉一个庞大帝国的全貌，但语言的能力有限——它无法区分一个可数的子帝国和整个不可数的帝国。这个现象被称为"Skolem 悖论"，它深刻地揭示了形式语言在描述无限结构时的局限性。""",
    r"""设 $L$ 是一阶语言，$T$ 是 $L$ 中的理论。

**向下 Löwenheim-Skolem 定理**：若 $T$ 有一个无限模型 $M$，则对任何基数 $\kappa$ 满足 $|L| \leq \kappa \leq |M|$，存在 $T$ 的一个基数为 $\kappa$ 的模型 $N$。特别地，若 $|L|$ 可数，则 $T$ 有可数模型。

**向上 Löwenheim-Skolem 定理**：若 $T$ 有一个无限模型 $M$，则对任何基数 $\kappa \geq |M|$，存在 $T$ 的一个基数为 $\kappa$ 的模型 $N$。

等价表述：

- 若 $T$ 有任意大的有限模型，则 $T$ 也有无限模型
- 若 $T$ 有无限模型，则 $T$ 有所有大于等于 $|L|$ 的无限基数的模型

其中：

- $|L|$ 表示语言 $L$ 的基数（通常为可数或有限）
- 该定理仅对一阶逻辑成立。对二阶逻辑或更强逻辑不成立
- 向上版本通常通过紧致性定理和常数符号的添加来证明
- 向下版本通常通过 Skolem 函数和初等子结构的构造来证明

**Skolem 悖论**：ZFC 集合论可以证明存在不可数集合，但由 Löwenheim-Skolem 定理，ZFC 自身（若一致）也有可数模型。在这个可数模型中，"不可数集合"的基数实际上是可数的！""",
    r"""1. **Skolem 函数**：对 $L$ 中的每个存在公式 $\exists x \, \varphi(x, \bar{y})$，添加一个 Skolem 函数符号 $f_\varphi(\bar{y})$，并扩展理论要求 $f_\varphi$ 提供见证
2. **子结构的闭包**：从 $M$ 中选取大小为 $\kappa$ 的子集 $A$，对 Skolem 函数取闭包得到一个子结构 $N$
3. **Tarski-Vaught 判别准则**：证明 $N$ 是 $M$ 的初等子结构，即 $N$ 满足与 $M$ 相同的一阶语句
4. **向上版本**：通过向语言中添加 $\kappa$ 个新的不同常数符号和相应的不等式公理，利用紧致性定理构造基数为 $\kappa$ 的模型

核心洞察在于一阶语句只涉及有限多个量词和有限深度的元素关系，因此可以通过对 Skolem 函数取闭包来控制模型的大小。""",
    r"""### 示例 1：ZFC 的可数模型

ZFC 集合论（一阶语言）若一致，则由向下 Löwenheim-Skolem 定理，它有一个可数模型 $M$。在这个模型中，所有集合（包括那些 $M$ 认为是不可数的集合）从外部看都是可数的。这就是著名的 Skolem 悖论。

### 示例 2：实数域的可数模型

实数域 $\mathbb{R}$ 作为一阶结构（语言为 $\{+, \times, 0, 1\}$）有不可数基数。但实数域的代数理论（Th($\mathbb{R}$)）也有可数模型。这个可数模型与标准实数在一阶性质上不可区分，但从外部看它是可数的。

### 示例 3：非标准模型的大小

Peano 算术 PA 有可数模型（标准自然数），也有不可数模型（非标准自然数）。向上 Löwenheim-Skolem 定理保证了 PA 有任意大基数的非标准模型。这些模型在外部看大小不同，但在一阶语言内满足完全相同的语句。""",
    r"""- **集合论**：Skolem 悖论和超限模型的研究
- **模型论**：稳定性理论、范畴性和饱和模型的基础
- **代数**：非标准域、非标准整数和代数闭域的分类
- **数学基础**：形式系统表达能力局限性的哲学探讨
- **逻辑哲学**：模型内部与外部视角差异的研究""",
    r"""- 初等子结构 (Elementary Substructure)：满足相同一阶语句的子结构
- Skolem 函数 (Skolem Function)：为存在量词提供见证的函数
- Tarski-Vaught 判别准则 (Tarski-Vaught Criterion)：判断初等子结构的条件
- 基数 (Cardinality)：集合的大小
- Skolem 悖论 (Skolem's Paradox)：ZFC 可数模型的反直觉现象""",
    r"""### 教材

- [H. B. Enderton. A Mathematical Introduction to Logic. Academic Press, 2nd edition, 2001. Chapter 3]
- [D. Marker. Model Theory: An Introduction. Springer, 2002. Chapter 2]

### 在线资源

- [Mathlib4 - Skolem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Skolem.html)"""
)
