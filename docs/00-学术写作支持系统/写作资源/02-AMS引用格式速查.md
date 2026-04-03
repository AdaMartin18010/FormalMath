---
msc_primary: "00A99"
---

# AMS引用格式速查

## 1. 文内引用格式

### 1.1 标准编号引用

```latex
% 单篇引用
This result was proved by Smith [12].
Smith proved that $\pi$ is transcendental [12].

% 多篇引用
This has been studied extensively [3, 7, 12].

% 连续编号
For more details, see [3, 7-10, 12].

% 引用作为句子成分
In [12], Smith proved that...
The theorem [12, Thm. 3.1] states that...
```

### 1.2 作者-年份引用

```latex
% 首次出现
Smith (1882) proved that $\pi$ is transcendental.

% 括号形式
It has been shown (Smith 1882) that...

% 多作者
Smith and Jones (1990) showed...
Smith et al. (1995) proved...
```

## 2. 参考文献列表格式

### 2.1 书籍

```
[1] J. P. Serre, A Course in Arithmetic, Graduate Texts in 
    Mathematics, vol. 7, Springer-Verlag, New York, 1973.

[2] M. Artin, Algebra, 2nd ed., Pearson, Boston, 2010.
```

### 2.2 期刊文章

```
[3] A. Wiles, Modular elliptic curves and Fermat's Last Theorem, 
    Ann. of Math. (2) 141 (1995), no. 3, 443-551.

[4] J. H. Silverman, The arithmetic of elliptic curves, 
    Invent. Math. 23 (1974), 179-206.
```

### 2.3 预印本与会议

```
[5] T. Tao, The prime number theorem, arXiv:math/0309380, 2003.

[6] L. Valiant, A theory of the learnable, STOC (1984), 436-445.
```

## 3. BibTeX条目模板

### 3.1 @book

```bibtex
@book{key,
  author    = {First Last},
  title     = {Book Title},
  publisher = {Publisher},
  year      = {2023}
}
```

### 3.2 @article

```bibtex
@article{key,
  author  = {First Last},
  title   = {Article Title},
  journal = {Journal Name},
  volume  = {42},
  pages   = {123--145},
  year    = {2023}
}
```

### 3.3 @unpublished

```bibtex
@unpublished{key,
  author = {First Last},
  title  = {Paper Title},
  year   = {2024},
  note   = {arXiv:2401.12345}
}
```

---

*最后更新：2026年4月*
