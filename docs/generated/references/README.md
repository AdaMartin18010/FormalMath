---
msc_primary: 00

  - 00A99
title: FormalMath 参考文献系统
processed_at: '2026-04-05'
---
# FormalMath 参考文献系统

本目录包含FormalMath项目的完整参考文献数据库和相关指南。

---

## 文件结构

```
docs/generated/references/
├── README.md                           # 本文件
├── 00-参考文献完善执行摘要.md           # 执行摘要和统计
├── FormalMath-References.bib           # 完整BibTeX数据库
├── 参考文献完整性报告.md                # 详细审查报告
├── 分支文献推荐指南.md                  # 按数学分支推荐
└── 快速引用速查表.md                    # 常用引用格式
```

---

## 快速开始

### 查找文献

1. **按分支查找**: 参考 `分支文献推荐指南.md`
2. **快速复制**: 使用 `快速引用速查表.md` 中的预格式化引用
3. **完整搜索**: 在 `FormalMath-References.bib` 中搜索

### 在LaTeX中使用

```latex
\documentclass{article}
\bibliographystyle{amsplain}

\begin{document}
As shown by \cite{rudin1976}, ...

\bibliography{ FormalMath-References }
\end{document}
```

### 在Markdown中使用

```markdown
根据Rudin的经典教材[1]，我们可以...

## 参考文献

[1] W. Rudin, Principles of Mathematical Analysis, 3rd ed., 
    McGraw-Hill, 1976. ISBN: 978-0-07-054235-8
```

---

## 数据库统计

- **总条目数**: 120+
- **覆盖分支**: 10+ 数学分支
- **格式标准**: AMS (美国数学学会)
- **标识符**: DOI, ISBN, arXiv编号

### 分支覆盖

| 分支 | 条目数 |
|------|--------|
| 代数学 | 35 |
| 分析学 | 25 |
| 几何与拓扑 | 15 |
| 数论 | 12 |
| 逻辑与基础 | 7 |
| 其他 | 26+ |

---

## 引用格式标准

本项目采用 **AMS (美国数学学会)** 引用格式。

### 书籍

```
[编号] 作者, 书名, 版次, 出版社, 年份. ISBN: xxx
```

### 期刊文章

```
[编号] 作者, 文章标题, 期刊名 卷号 (年份), 期号, 页码. DOI: xxx
```

### 预印本

```
[编号] 作者, 文章标题, arXiv:编号 [分类], 年份.
```

---

## 推荐阅读顺序

1. **新用户**: 先读 `00-参考文献完善执行摘要.md`
2. **查找文献**: 参考 `分支文献推荐指南.md`
3. **快速引用**: 使用 `快速引用速查表.md`
4. **深入了解**: 查看 `参考文献完整性报告.md`

---

## 五星必读经典

### 代数学
- S. Lang, *Algebra*, 3rd ed., 2002
- D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed., 2004
- M. Artin, *Algebra*, 2nd ed., 2011

### 分析学
- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., 1976
- L. Ahlfors, *Complex Analysis*, 3rd ed., 1979
- G. Folland, *Real Analysis*, 2nd ed., 1999

### 几何与拓扑
- J. Munkres, *Topology*, 2nd ed., 2000
- A. Hatcher, *Algebraic Topology*, 2002
- M. do Carmo, *Riemannian Geometry*, 1992

### 数论
- G. Hardy & E. Wright, *An Introduction to the Theory of Numbers*, 6th ed., 2008
- J. Neukirch, *Algebraic Number Theory*, 1999
- J. Silverman, *The Arithmetic of Elliptic Curves*, 1986

---

## 在线资源

| 资源 | URL | 说明 |
|------|-----|------|
| Stacks Project | stacks.math.columbia.edu | 代数几何 |
| nLab | ncatlab.org | 范畴论 |
| MacTutor | mathshistory.st-andrews.ac.uk | 数学史 |
| OEIS | oeis.org | 整数序列 |
| MathWorld | mathworld.wolfram.com | 数学百科 |

---

## 贡献指南

如需添加新文献：

1. 在 `FormalMath-References.bib` 中添加BibTeX条目
2. 更新相关分支的推荐指南
3. 确保包含DOI或ISBN
4. 遵循现有格式规范

---

## 引用检查清单

- [ ] 所有引用都有参考文献条目
- [ ] 作者姓名格式一致 (名 姓)
- [ ] 书名使用斜体
- [ ] 包含DOI或ISBN (如适用)
- [ ] 在线资源注明访问日期
- [ ] 引用编号按出现顺序排列
- [ ] 无孤立引用

---

*FormalMath参考文献系统*  
*最后更新: 2026年4月4日*
