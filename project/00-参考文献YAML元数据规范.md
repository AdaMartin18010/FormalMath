# 参考文献 YAML 元数据规范

## 1. 目的

为 FormalMath 项目所有 Markdown 文档建立统一的 `references` 元数据标准，解决 DOI、arXiv ID、zbMATH、MathSciNet MR Number 检出率为 0% 的问题，确保参考文献可被机器解析、交叉引用和外部链接。

## 2. 适用范围

- 所有 `docs/` 目录下的知识文档
- 所有 `concept/` 目录下的概念说明
- 所有 `research/` 目录下的研究笔记

## 3. 字段位置

`references` 必须置于 YAML frontmatter 内部，位于文件最顶端的 `---` 与 `---` 之间。

```yaml
---
title: "文档标题"
msc_primary: "26A99"
references:
  textbooks:
    - ...
  papers:
    - ...
  databases:
    - ...
---
```

## 4. 顶层结构

| 字段 | 类型 | 说明 |
|------|------|------|
| `textbooks` | list | 教材与专著引用列表 |
| `papers` | list | 学术论文引用列表 |
| `databases` | list | 在线数据库与百科引用列表 |

以上三个字段至少出现其一；若文档暂无引用，可保留空列表 `[]` 或空对象 `{}`。

## 5. 条目类型规范

### 5.1 textbook（教材/专著）

| 属性 | 必填 | 类型 | 说明 |
|------|------|------|------|
| `id` | ✅ | string | 唯一引用标识，如 `rudin_pma` |
| `type` | ✅ | string | 固定值 `textbook` |
| `title` | ✅ | string | 书名 |
| `authors` | ✅ | list | 作者列表 |
| `publisher` | ✅ | string | 出版社 |
| `year` | ✅ | integer | 出版年份 |
| `edition` | ❌ | string | 版次，如 "3rd" |
| `isbn` | ❌ | string | ISBN-10 或 ISBN-13 |
| `msc` | ❌ | string | MSC 分类号 |
| `chapters` | ❌ | list | 本文档具体引用的章节 |
| `pages` | ❌ | string | 具体页码范围 |
| `url` | ❌ | string | 官方链接或永久链接 |
| `note` | ❌ | string | 补充说明（如中译本信息） |

### 5.2 paper（学术论文）

| 属性 | 必填 | 类型 | 说明 |
|------|------|------|------|
| `id` | ✅ | string | 唯一引用标识 |
| `type` | ✅ | string | 固定值 `paper` |
| `title` | ✅ | string | 论文标题 |
| `authors` | ✅ | list | 作者列表 |
| `year` | ✅ | integer | 发表年份 |
| `journal` | ❌ | string | 期刊名 |
| `volume` | ❌ | string | 卷号 |
| `issue` | ❌ | string | 期号 |
| `pages` | ❌ | string | 页码范围 |
| `doi` | ❌ | string | DOI，格式 `10.xxxx/xxxx` |
| `arxiv_id` | ❌ | string | arXiv ID，如 `math/0102034` 或 `2401.12345` |
| `mr_number` | ❌ | string | MathSciNet MR Number，如 `MR123456` |
| `zb_id` | ❌ | string | zbMATH 编号，如 `0766.14001` |
| `url` | ❌ | string | 永久链接或预印本链接 |

### 5.3 database（在线数据库/百科）

| 属性 | 必填 | 类型 | 说明 |
|------|------|------|------|
| `id` | ✅ | string | 唯一引用标识，如 `nlab` |
| `type` | ✅ | string | 固定值 `database` |
| `name` | ✅ | string | 数据库名称 |
| `entry` | ❌ | string | 具体查询词条或 Tag |
| `entry_url` | ❌ | string | 带占位符的 URL 模板，如 `https://ncatlab.org/nlab/show/{entry}` |
| `consulted_at` | ❌ | string | 查询日期，ISO 8601 格式 |
| `note` | ❌ | string | 补充说明 |

## 6. 完整示例

### 示例 1：实分析（Real Analysis）— Rudin

```yaml
references:
  textbooks:
    - id: rudin_pma
      type: textbook
      title: "Principles of Mathematical Analysis"
      authors: ["Walter Rudin"]
      publisher: "McGraw-Hill"
      edition: "3rd"
      year: 1976
      isbn: "978-0070542358"
      msc: "26-01"
      chapters:
        - "Chapter 1: The Real and Complex Number Systems"
        - "Chapter 2: Basic Topology"
        - "Chapter 3: Numerical Sequences and Series"
  databases:
    - id: nlab
      type: database
      name: "nLab"
      entry: "real number"
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: "2026-04-17"
```

### 示例 2：代数几何（Algebraic Geometry）— Hartshorne

```yaml
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: "Algebraic Geometry"
      authors: ["Robin Hartshorne"]
      publisher: "Springer"
      edition: "1st"
      year: 1977
      isbn: "978-0387902449"
      msc: "14-01"
      chapters:
        - "Chapter II: Schemes"
        - "Chapter III: Cohomology"
  databases:
    - id: stacks_project
      type: database
      name: "Stacks Project"
      entry: "01H8"
      entry_url: "https://stacks.math.columbia.edu/tag/{entry}"
      consulted_at: "2026-04-17"
```

### 示例 3：线性代数（Linear Algebra）— Strang

```yaml
references:
  textbooks:
    - id: strang_la
      type: textbook
      title: "Introduction to Linear Algebra"
      authors: ["Gilbert Strang"]
      publisher: "Wellesley-Cambridge Press"
      edition: "5th"
      year: 2016
      isbn: "978-0980232776"
      msc: "15-01"
      chapters:
        - "Chapter 1: Introduction to Vectors"
        - "Chapter 2: Solving Linear Equations"
  databases:
    - id: mathworld
      type: database
      name: "MathWorld"
      entry: "LinearAlgebra"
      entry_url: "https://mathworld.wolfram.com/{entry}.html"
      consulted_at: "2026-04-17"
```

### 示例 4：拓扑学（Topology）— Munkres

```yaml
references:
  textbooks:
    - id: munkres_top
      type: textbook
      title: "Topology"
      authors: ["James R. Munkres"]
      publisher: "Pearson"
      edition: "2nd"
      year: 2000
      isbn: "978-0131816299"
      msc: "54-01"
      chapters:
        - "Chapter 2: Topological Spaces and Continuous Functions"
        - "Chapter 3: Connectedness and Compactness"
  databases:
    - id: nlab
      type: database
      name: "nLab"
      entry: "topological space"
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: "2026-04-17"
```

### 示例 5：数论（Number Theory）— Hardy & Wright

```yaml
references:
  textbooks:
    - id: hardy_wright_nt
      type: textbook
      title: "An Introduction to the Theory of Numbers"
      authors: ["G. H. Hardy", "E. M. Wright"]
      publisher: "Oxford University Press"
      edition: "6th"
      year: 2008
      isbn: "978-0199219865"
      msc: "11-01"
      chapters:
        - "Chapter 1: The Series of Primes"
        - "Chapter 2: Farey Series and a Theorem of Minkowski"
  databases:
    - id: zbmath
      type: database
      name: "zbMATH Open"
      entry: "1159.11001"
      entry_url: "https://zbmath.org/?q=an:{entry}"
      consulted_at: "2026-04-17"
```

### 示例 6：抽象代数（Abstract Algebra）— Dummit & Foote

```yaml
references:
  textbooks:
    - id: dummit_foote_aa
      type: textbook
      title: "Abstract Algebra"
      authors: ["David S. Dummit", "Richard M. Foote"]
      publisher: "Wiley"
      edition: "3rd"
      year: 2003
      isbn: "978-0471433347"
      msc: "13-01"
      chapters:
        - "Chapter 1: Introduction to Groups"
        - "Chapter 7: Introduction to Rings"
  databases:
    - id: nlab
      type: database
      name: "nLab"
      entry: "group"
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: "2026-04-17"
```

## 7. 批处理脚本使用指南

使用 `scripts/batch_add_references.py` 批量为 Markdown 文件注入 `references` 字段：

```bash
# 查看将要修改的文件（dry-run）
python scripts/batch_add_references.py --dir docs/03-分析学/01-实分析/ --dry-run

# 为所有缺失 references 的文件注入空模板
python scripts/batch_add_references.py --dir docs/03-分析学/01-实分析/ --all

# 注入指定教材模板（含 Rudin + nLab）
python scripts/batch_add_references.py --dir docs/03-分析学/01-实分析/ --inject rudin_pma,nlab
```

## 8. 版本与维护

- **版本**: 1.0
- **生效日期**: 2026-04-17
- **维护责任**: P2-Ref 任务组
- **下次审计**: 2026-05-17
