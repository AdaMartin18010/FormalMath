---
msc_primary: 97A30
msc_secondary:
- 00A05
level: silver
course: UCLA 微分几何
chapter: '0'
references:
  textbooks:
  - title: Differential Geometry of Curves and Surfaces
    author: Manfredo P. do Carmo
    edition: 1st
    publisher: Prentice-Hall
    year: 1976
    isbn: '9780132125895'
    mr_number: MR0394451
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
  - title: 'How to Solve It: A New Aspect of Mathematical Method'
    author: George Pólya
    edition: 2nd
    publisher: Princeton University Press
    year: 2004
    isbn: '9780691119663'
    doi: 10.1515/9781400828678
  databases:
  - id: wikidata
    type: database
    name: Wikidata
    entry_url: https://www.wikidata.org/entity/Q188444
    consulted_at: '2026-06-16'
title: UCLA 微分几何 学习诊断手册
external_ids:
  nlab_url: https://ncatlab.org/nlab/show/differential+geometry
  wikipedia_url: https://en.wikipedia.org/wiki/Differential_geometry
  stacks_search_url: https://stacks.math.columbia.edu/search?query=%E5%BE%AE%E5%88%86%E5%87%A0%E4%BD%95
---
# UCLA 微分几何学习诊断手册

## 常见错误模式

### 错误1: 混淆内外蕴几何

**错误认知**: 曲率只依赖于曲面在三维空间中的嵌入
**正确理解**: Gauss绝妙定理：Gauss曲率是内蕴量，只依赖于第一基本形式。
**检测方法**: 检查学生是否能计算平面圆柱的Gauss曲率K=0

### 错误2: 符号混淆

**错误认知**: E,F,G 和 L,M,N 的定义混淆
**正确理解**: E=⟨r_u,r_u⟩, F=⟨r_u,r_v⟩, G=⟨r_v,r_v⟩ (第一基本形式)；L=⟨r_uu,n⟩, M=⟨r_uv,n⟩, N=⟨r_vv,n⟩ (第二基本形式)

### 错误3: 测地线误解

**错误认知**: 测地线是曲面上最短的曲线
**正确理解**: 测地线是局部最短的，但整体不一定最短（如球面上的大圆有正反两个方向）

## 能力层级

| 层级 | 表现 | 建议 |
|------|------|------|
| L1 | 能计算曲线曲率挠率 | 加强曲面参数化 |
| L2 | 能计算第一/二基本形式 | 练习主曲率计算 |
| L3 | 理解Gauss-Bonnet | 学习测地线方程 |
| L4 | 理解抽象流形 | 研究Riemann几何 |

## 交叉引用

- [相关: Ch01-向量与向量运算](../00-银层核心课程/MIT-18.02-多元微积分/Ch01-向量与向量运算.md)
- [相关: ANA-001-序列极限四则运算](../00-习题示例反例库/实分析/ANA-001-序列极限四则运算.md)
- [相关: 01-拓扑空间](../00-知识层次体系/L1-形式化定义层/05-拓扑学基础/01-拓扑空间.md)
---

## 参考与延伸阅读

### 教材

- Manfredo P. do Carmo, *Differential Geometry of Curves and Surfaces*, 1st ed., Prentice-Hall, 1976 (ISBN: 9780132125895; MR: MR0394451)

### 数据库与网络资源

- [Wikidata](https://www.wikidata.org/entity/Q188444)

### 课程与外部链接

- [Nlab Url](https://ncatlab.org/nlab/show/differential+geometry)
- [Wikipedia Url](https://en.wikipedia.org/wiki/Differential_geometry)
- [Stacks Search Url](https://stacks.math.columbia.edu/search?query=%E5%BE%AE%E5%88%86%E5%87%A0%E4%BD%95)