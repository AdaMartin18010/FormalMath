# Riemann-Roch定理：网络权威信息对齐与批判性意见报告

**文档类型**：对齐论证 · 批判性梳理 · 推进计划
**关联文档**：[05-Riemann-Roch定理](./05-Riemann-Roch定理.md) · [05-Riemann-Roch定理-思维表征](./05-Riemann-Roch定理-思维表征.md)
**创建日期**：2026年01月31日

---

## 一、网络权威信息对齐

### 1.1 权威表述对照

| 当前文档表述 | 权威来源 | 对齐结论 |
|-------------|----------|----------|
| 经典 Riemann-Roch：χ(C,O(D)) = deg(D) + 1 - g | 经典；Riemann, Roch, 曲线 | ✅ 一致 |
| HRR：χ(X,E) = ∫_X ch(E)·td(X) | Hirzebruch (1954)；光滑射影概形 | ✅ 一致 |
| GRR：ch(R f_* E)·td(Y) = f_*(ch(E)·td(X)) | SGA 6 (1971)；Wikipedia "Grothendieck–Riemann–Roch" | ✅ 一致：权威常用 **ch(f_* α)·td(TY) = f_*(ch(α)·td(TX))**，$f_*$ 为 K_0 上推前；对凝聚层即 $\sum (-1)^i R^i f_*$ |
| SGA 6（1966–1968）| SGA 6, Berthelot–Grothendieck–Illusie, LNM 225 (1971) | ⚠️ 建议：正文注明出版 1971，作者 Berthelot, Grothendieck, Illusie；标题 *Théorie des intersections et théorème de Riemann-Roch* |
| K_0(X)、Chern 特征、Todd 类 | SGA 6；K-theory | ✅ 一致；与 [07-K理论](./07-K理论.md)、[06-相交理论](./06-相交理论.md) 衔接 |
| 历史与渊源、姊妹篇与网络资源 | 主文已添加；本报告权威对齐已扩展 | 一致 |
| GRR、SGA 6、Fulton Stacks | SGA 6、Fulton Intersection Theory、Stacks | 一致 |

### 1.2 关键术语对齐

| 概念 | 当前文档 | 权威常见表述 | 建议 |
|------|----------|-------------|------|
| GRR 中的推前 | ch(R f_* E)·td(Y) = f_*(...) | ch(f_* α)·td(TY) = f_*(ch(α)·td(TX))；$f_*: K_0(X) \to K_0(Y)$ | 已体现；可补「$f_*$ 为 K_0 上的推前，对层即 $\sum (-1)^i R^i f_*$」|
| 适用态射 | 概形态射 f: X→Y | proper morphism；光滑或 local complete intersection 时用相对切丛/虚切丛 | 建议在 3.1 或 9.3 注明 **proper**，非光滑时可用虚切丛 |
| SGA 6 作者与出版 | Grothendieck，多人合作 | Berthelot, Grothendieck, Illusie；Springer LNM 225 (1971) | 在 4.1 增加作者与 LNM 225 |

### 1.3 权威参考资源

- **SGA 6**：Berthelot–Grothendieck–Illusie, *Théorie des intersections et théorème de Riemann-Roch*, LNM 225 (Springer, 1971)；Numdam SGA 6。
- **教材**：Fulton *Intersection Theory* (Springer)；Vakil 讲义 (Stanford 245)。
- **网络**：Wikipedia "Grothendieck–Riemann–Roch theorem" "Riemann–Roch-type theorem"；nLab "Grothendieck-Riemann-Roch theorem"；Stacks Project bibliography SGA6。
- **姊妹篇**：[06-相交理论](./06-相交理论.md)；[07-K理论](./07-K理论.md)。

---

## 二、批判性意见与建议

已落实：主文已添加历史与渊源（对齐）与姊妹篇与网络资源；本报告权威对齐已扩展。

### 2.1 内容结构

- **历史**：建议在「一、经典 Riemann-Roch」下增加 **1.3 历史与渊源**：Riemann–Roch（曲线）→ Hirzebruch (1954) HRR → Grothendieck SGA 6 GRR 与相交理论、K 理论。
- **重复**：第十节「Riemann-Roch定理的应用」与第五、六、九节部分重复；可保留第十节为应用汇总，但删除与五、六、九完全重复的段落。
- **参考文献**：建议文末增加「参考文献与网络资源」节（SGA 6、Fulton、Wikipedia、Stacks、姊妹篇）。

### 2.2 数学严谨性

- **GRR 适用条件**：$f: X \to Y$ 应为 **proper**；在光滑或 local complete intersection 情形下陈述最简，非光滑时可用虚切丛（virtual tangent bundle）或相对切丛。
- **K_0 与推前**：GRR 在 $K_0(X)$ 上陈述时，$f_*$ 为凝聚层（或向量丛）的推前诱导的 $K_0$ 映射；与 $\sum (-1)^i R^i f_*$ 一致。

### 2.3 与姊妹篇衔接

- **相交理论**：相交积、陈类与 GRR 见 [06-相交理论](./06-相交理论.md)。
- **K 理论**：$K_0$、Chern 特征、高 K 群见 [07-K理论](./07-K理论.md)。

---

## 三、多维概念对比矩阵

### 3.1 Riemann-Roch 定理层次对比

| 定理 | 对象 | 公式 | 典型文献 |
|------|------|------|----------|
| 经典 R–R | 曲线 C，除子 D | χ(O(D)) = deg(D) + 1 - g | Riemann, Roch |
| HRR | 光滑射影 X，向量丛 E | χ(E) = ∫_X ch(E)·td(X) | Hirzebruch 1954 |
| GRR | proper f: X→Y，α∈K_0(X) | ch(f_* α)·td(TY) = f_*(ch(α)·td(TX)) | SGA 6 (1971) |

### 3.2 概念层次（R–R → 应用）

| 概念 | 含义 | 与 R–R 关系 |
|------|------|-------------|
| Chern 特征 ch | K_0 → 上同调环 | GRR/HRR 核心 |
| Todd 类 td | 切丛/虚切丛 | GRR/HRR 核心 |
| 相交理论 | 相交积、陈类 | SGA 6；见 06-相交理论 |
| K 理论 K_0 | 向量丛/凝聚层 Grothendieck 群 | SGA 6；见 07-K理论 |

---

## 四、分层推进计划

### 层次一（即时修订）

| 序号 | 任务 | 产出 |
|------|------|------|
| 1.1 | 增加 1.3 历史与渊源（经典→HRR→GRR/SGA 6）| 新小节 |
| 1.2 | 4.1 注明 SGA 6 作者 Berthelot–Grothendieck–Illusie、LNM 225 (1971) | 4.1 |
| 1.3 | 9.3 GRR 处注明 $f$ **proper**，非光滑时虚切丛一句 | 9.3 |
| 1.4 | 文末增加「参考文献与网络资源」 | 新小节 |

### 层次二（内容增强）

| 序号 | 任务 | 产出 |
|------|------|------|
| 2.1 | GRR 处补「$f_*$ 为 K_0 推前，对层即 $\sum (-1)^i R^i f_*$」| 3.1 或 9.3 |
| 2.2 | 与 [06-相交理论](./06-相交理论.md)、[07-K理论](./07-K理论.md) 交叉引用 | 五、六、十 |

### 层次三（体系化）【✅ 已完成】

- 思维表征独立页见 [05-Riemann-Roch定理-思维表征](./05-Riemann-Roch定理-思维表征.md)。
- 索引更新见 [00-其他数学贡献-对齐与推进索引](./00-其他数学贡献-对齐与推进索引.md)。
