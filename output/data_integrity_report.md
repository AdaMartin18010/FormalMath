---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# FormalMath 数据完整性检查报告

**检查时间**: 2026-04-05 11:39:46
**检查目录**: G:\_src\FormalMath

## 检查概览

| 检查项 | 结果 |
|--------|------|
| JSON文件有效 | 3679 |
| JSON文件无效 | 10 |
| YAML文件有效 | 117 |
| YAML文件无效 | 153 |
| Markdown文件已检查 | 10285 |

## 问题统计

- **错误总数**: 6019
- **警告总数**: 17643

## 错误详情

### JSON格式错误 (10个)

- **math_data.json**: JSON解析错误: Unexpected UTF-8 BOM (decode using utf-8-sig): line 1 column 1 (char 0)
- **.vscode\extensions.json**: JSON解析错误: Expecting value: line 3 column 5 (char 29)
- **.vscode\settings.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 3 (char 4)
- **FormalMath-Enhanced\lean4\FormalMath\.lake\packages\mathlib\.vscode\extensions.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 2 (char 3)
- **FormalMath-Enhanced\lean4\FormalMath\.lake\packages\proofwidgets\widget\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 3 column 5 (char 29)
- **FormalMath-Enhanced\testing\test-data\mock-learning-paths.json**: JSON解析错误: Expecting ',' delimiter: line 101 column 33 (char 5709)
- **FormalMath-Interactive\node_modules\lib0\.vscode\launch.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 3 (char 4)
- **FormalMath-Interactive\node_modules\msw\src\tsconfig.src.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 3 (char 4)
- **FormalMath-Interactive\node_modules\msw\src\browser\tsconfig.browser.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 4 column 5 (char 66)
- **FormalMath-Interactive\node_modules\rxjs\src\tsconfig.cjs.spec.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 3 column 3 (char 40)

### YAML格式错误 (153个)

- **00-代数学概念依赖配置.yaml**: YAML解析错误: while parsing a block collection
  in "00-代数学概念依赖配置.yaml", line 20, column 9
expected <block end>, but found '<scalar>'
  in "00-代数学概念依赖配置.yaml", line 26, column 19
- **concept_prerequisites_geometry_topology_update.yaml**: YAML解析错误: while parsing a block mapping
  in "concept_prerequisites_geometry_topology_update.yaml", line 17, column 9
expected <block end>, but found '<scalar>'
  in "concept_prerequisites_geometry_topology_update.yaml", line 19, column 20
- **concept\concept_prerequisites.yaml**: YAML解析错误: while parsing a block mapping
  in "concept\concept_prerequisites.yaml", line 20, column 7
expected <block end>, but found '<scalar>'
  in "concept\concept_prerequisites.yaml", line 22, column 16
- **k8s\02-configmap.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\02-configmap.yaml", line 1, column 1
but found another document
  in "k8s\02-configmap.yaml", line 40, column 1
- **k8s\03-secret.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\03-secret.yaml", line 1, column 1
but found another document
  in "k8s\03-secret.yaml", line 31, column 1
- **k8s\06-service.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\06-service.yaml", line 1, column 1
but found another document
  in "k8s\06-service.yaml", line 20, column 1
- **k8s\07-ingress.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\07-ingress.yaml", line 1, column 1
but found another document
  in "k8s\07-ingress.yaml", line 70, column 1
- **k8s\08-hpa.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\08-hpa.yaml", line 1, column 1
but found another document
  in "k8s\08-hpa.yaml", line 46, column 1
- **k8s\09-monitoring.yaml**: YAML解析错误: expected a single document in the stream
  in "k8s\09-monitoring.yaml", line 2, column 1
but found another document
  in "k8s\09-monitoring.yaml", line 20, column 1
- **project\concept_prerequisites_400.yaml**: YAML解析错误: while parsing a block mapping
  in "project\concept_prerequisites_400.yaml", line 16, column 9
expected <block end>, but found '<scalar>'
  in "project\concept_prerequisites_400.yaml", line 19, column 22
- ... 还有 143 个类似问题

### 链接错误 (5855个)

- **00-FormalMath项目内容索引-完整版.md**: 链接指向的文件不存在: 00-国际对齐精度验证报告-2026年4月.md
- **00-FormalMath项目内容索引-完整版.md**: 链接指向的文件不存在: 00-国际对齐修正清单-2026年4月.md
- **00-FormalMath项目内容索引-完整版.md**: 链接指向的文件不存在: 00-日英数学术语对照表.md
- **00-数学家索引重建报告.md**: 链接指向的文件不存在: ./黎曼数学理念/02-数学内容深度分析/01-黎曼几何/01-1854就职演讲详解.md
- **00-术语词典统一报告.md**: 链接指向的文件不存在: ../00-标准术语表-8语言.md
- **INDEX.md**: 链接指向的文件不存在: 数学家理念体系/00-数学家索引-2025年12月.md
- **INDEX.md**: 链接指向的文件不存在: 数学家理念体系/00-数学家索引-2025年12月.md
- **README.md**: 链接指向的文件不存在: 数学家理念体系/00-数学家索引-2025年12月.md
- **README.md**: 链接指向的文件不存在: 00-日英数学术语对照表.md
- **concept\00-知识结构总览.md**: 链接指向的文件不存在: ./../docs/10-应用数学/01-核心内容/案例库/按数学分支/00-索引.md
- ... 还有 5845 个类似问题

### Frontmatter错误 (1个)

- **.github\pull_request_template.md**: YAML frontmatter格式错误

## 警告详情

### 数学公式 (7371个)

- **00-MIT课程内容对齐报告.md**: 公式括号不匹配: d: X \times X \to [0, \infty)...
- **00-MIT课程内容对齐报告.md**: 公式方括号不匹配: d: X \times X \to [0, \infty)...
- **00-应急方案详细手册.md**: 公式花括号不匹配: (pgrep -d',' node)
df -h
free -m

# 3. 检查数据库性能
# P...
- **docs\00-数学符号对照表.md**: 公式括号不匹配: [0, +\infty)...
- **docs\00-数学符号对照表.md**: 公式方括号不匹配: [0, +\infty)...
- **docs\00-数学符号对照表.md**: 公式括号不匹配: (-\infty, 0]...
- **docs\00-数学符号对照表.md**: 公式方括号不匹配: (-\infty, 0]...
- **docs\FormalMath符号使用规范.md**: 公式括号不匹配: \text{ran}(f) = [0, \infty)...
- **docs\FormalMath符号使用规范.md**: 公式方括号不匹配: \text{ran}(f) = [0, \infty)...
- **docs\FormalMath符号标准化推进报告-2025年1月.md**: 公式括号不匹配: ([^...
- ... 还有 7361 个类似问题

### 文档结构 (236个)

- **00-概念文档合并报告.md**: 文档缺少一级标题
- **.github\pull_request_template.md**: 文档缺少一级标题
- **.github\ISSUE_TEMPLATE\bug_report.md**: 文档缺少一级标题
- **.github\ISSUE_TEMPLATE\documentation.md**: 文档缺少一级标题
- **.github\ISSUE_TEMPLATE\feature_request.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-P0优先级空洞文档列表-2026年01月01日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-格式检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-符号一致性检查报告-2026年01月31日.md**: 文档缺少一级标题
- ... 还有 226 个类似问题

### 概念引用 (9994个)

- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.008
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.011
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.009
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.010
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.012
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.013
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.014
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.032
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.025
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.033
- ... 还有 9984 个类似问题

### 文件命名 (42个)

- **docs\00-核心概念理解三问\11-核心定理多表征\21-van Kampen定理-五种表征.md**: 文件名包含空格
- **docs\00-核心概念理解三问\11-核心定理多表征\22-Seifert-van Kampen定理-五种表征.md**: 文件名包含空格
- **docs\00-核心概念理解三问\11-核心定理多表征\35-de Rham定理-五种表征.md**: 文件名包含空格
- **docs\03-分析学\03-泛函分析-扩展\06-C代数与von Neumann代数-深度扩展版.md**: 文件名包含空格
- **docs\工作示例\01-概念理解\28- Zorn与极大元-工作示例.md**: 文件名包含空格
- **docs\工作示例\01-概念理解\30- Riemann积分与Darboux和-工作示例.md**: 文件名包含空格
- **docs\工作示例\02-计算示例\19- Jordan标准形-工作示例.md**: 文件名包含空格
- **docs\工作示例\02-计算示例\20- Gram-Schmidt正交化-工作示例.md**: 文件名包含空格
- **docs\工作示例\02-计算示例\27- Green公式计算-工作示例.md**: 文件名包含空格
- **docs\工作示例\03-证明示例\15- Banach不动点-工作示例.md**: 文件名包含空格
- ... 还有 32 个类似问题

## 修复建议

1. **JSON格式错误**: 使用JSON验证器检查并修复格式问题
2. **YAML格式错误**: 检查缩进和语法，确保符合YAML规范
3. **链接错误**: 更新或移除失效的相对链接
4. **数学公式问题**: 检查公式的括号匹配和LaTeX语法
