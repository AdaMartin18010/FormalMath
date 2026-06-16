---
msc_primary: 00A99
习题编号: ALG-140
学科: 代数
知识点: 同调代数-群上同调谱序列
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
title: ALG 140 Lyndon Hochschild Serre谱序列
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/spectral+sequence
  wikipedia_url: https://en.wikipedia.org/wiki/Spectral_sequence
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E8%B0%B1%E5%BA%8F%E5%88%97
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Serre/
references:
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q3503315
    consulted_at: '2026-06-16'
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
---
# Lyndon-Hochschild-Serre谱序列

## 题目

设 $G$ 是群，$H \triangleleft G$ 是正规子群。对 $G$-模 $M$，LHS谱序列联系群上同调。

**(a)** 证明：$H^p(G/H, H^q(H, M)) \Rightarrow H^{p+q}(G, M)$。

**(b)** 用此谱序列证明inflation-restriction正合列：
$$0 \to H^1(G/H, M^H) \to H^1(G, M) \to H^1(H, M)^{G/H} \to H^2(G/H, M^H) \to \cdots$$

**(c)** 计算 $H^*(\mathbb{Z}/p \times \mathbb{Z}/p, \mathbb{Z}/p)$。

## 解答

### (a) LHS谱序列

**证明：**

函子 $\text{Hom}_{\mathbb{Z}[G]}(\mathbb{Z}, -) = \text{Hom}_{\mathbb{Z}[G/H]}(\mathbb{Z}, \text{Hom}_{\mathbb{Z}[H]}(\mathbb{Z}, -))$。

应用Grothendieck谱序列于 $F = (-)^H$，$G = (-)^{G/H}$。

$(R^q F)(M) = H^q(H, M)$，$G$ 作用由共轭诱导。

得谱序列。$\square$

### (b) 膨胀-限制序列

**证明：**

由谱序列的低次项：
- $E^{2,0}_2 = H^2(G/H, M^H)$
- $E^{1,1}_2 = H^1(G/H, H^1(H, M))$
- $E^{0,2}_2 = H^0(G/H, H^2(H, M))$

$E^3 = H^3(G, M)$，有滤过。

由 $E_2$ 页结构，$d_2: E^{0,1}_2 \to E^{2,0}_2$ 给出连接同态。

正合列来自谱序列的边界映射。$\square$

### (c) 初等交换$p$群上同调

**解答：**

$G = \mathbb{Z}/p \times \mathbb{Z}/p = \langle a \rangle \times \langle b \rangle$。

用Künneth公式（或LHS）：
$$H^*(G, \mathbb{Z}/p) \cong H^*(\mathbb{Z}/p, \mathbb{Z}/p) \otimes H^*(\mathbb{Z}/p, \mathbb{Z}/p)$$

作为分次代数：
$$\cong \mathbb{Z}/p[x_1, x_2] \otimes \Lambda(y_1, y_2)$$
其中 $|x_i| = 2$，$|y_i| = 1$。

维数：$\dim H^n(G, \mathbb{Z}/p) = n+1$。

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845