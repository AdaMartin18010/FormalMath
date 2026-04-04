# FormalMath 数据完整性检查报告

**检查时间**: 2026-04-04 16:41:49
**检查目录**: G:\_src\FormalMath

## 检查概览

| 检查项 | 结果 |
|--------|------|
| JSON文件有效 | 2117 |
| JSON文件无效 | 79 |
| YAML文件有效 | 312 |
| YAML文件无效 | 19 |
| Markdown文件已检查 | 10851 |

## 问题统计

- **错误总数**: 32637
- **警告总数**: 17213

## 错误详情

### JSON格式错误 (79个)

- **.vscode\extensions.json**: JSON解析错误: Expecting value: line 3 column 5 (char 29)
- **.vscode\settings.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 3 (char 4)
- **project\UPMC-french-mathematical-terminology.json**: JSON解析错误: Invalid \escape: line 132 column 95 (char 12460)
- **FormalMath-Enhanced\testing\test-data\mock-learning-paths.json**: JSON解析错误: Expecting ',' delimiter: line 101 column 33 (char 5709)
- **FormalMath-Interactive\node_modules\array-buffer-byte-length\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 3 (char 84)
- **FormalMath-Interactive\node_modules\async-function\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 2 (char 79)
- **FormalMath-Interactive\node_modules\available-typed-arrays\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 3 column 5 (char 29)
- **FormalMath-Interactive\node_modules\call-bind-apply-helpers\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 2 (char 79)
- **FormalMath-Interactive\node_modules\call-bound\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 6 column 2 (char 100)
- **FormalMath-Interactive\node_modules\data-view-buffer\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 4 column 39 (char 94)
- ... 还有 69 个类似问题

### YAML格式错误 (19个)

- **00-代数学概念依赖配置.yaml**: YAML解析错误: while parsing a block collection
  in "00-代数学概念依赖配置.yaml", line 246, column 7
expected <block end>, but found '?'
  in "00-代数学概念依赖配置.yaml", line 250, column 7
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
- **project\msc_analysis_encoding_table.yaml**: YAML解析错误: mapping values are not allowed here
  in "project\msc_analysis_encoding_table.yaml", line 273, column 26
- **project\层次依赖矩阵.yaml**: YAML解析错误: expected a single document in the stream
  in "project\层次依赖矩阵.yaml", line 7, column 1
but found another document
  in "project\层次依赖矩阵.yaml", line 516, column 1
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\group.yaml**: YAML解析错误: while parsing a block mapping
  in "docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\group.yaml", line 239, column 9
expected <block end>, but found '<scalar>'
  in "docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\group.yaml", line 240, column 29
- ... 还有 9 个类似问题

### 链接错误 (32538个)

- **00-FormalMath第十一批任务完成报告-全局依赖图与拓扑排序.md**: 链接指向的文件不存在: ../concept/核心概念/00-核心概念索引.md
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../issues
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../discussions
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../pulls
- **CONTRIBUTING.md**: 链接指向的文件不存在: docs/00-贡献者指南/api文档.md
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../discussions
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../issues/new/choose
- **concept\00-P0P1改进工作完成报告-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- **concept\00-P0P1改进最终总结-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- **concept\00-国际主流数学认知理论整合框架-2025年1月.md**: 链接指向的文件不存在: ./00-概念体系深度改进计划-2025年1月.md
- ... 还有 32528 个类似问题

### Frontmatter错误 (1个)

- **.github\pull_request_template.md**: YAML frontmatter格式错误

## 警告详情

### 数学公式 (7131个)

- **00-MIT课程内容对齐报告.md**: 公式括号不匹配: d: X \times X \to [0, \infty)...
- **00-MIT课程内容对齐报告.md**: 公式方括号不匹配: d: X \times X \to [0, \infty)...
- **docs\00-数学符号对照表.md**: 公式括号不匹配: [0, +\infty)...
- **docs\00-数学符号对照表.md**: 公式方括号不匹配: [0, +\infty)...
- **docs\00-数学符号对照表.md**: 公式括号不匹配: (-\infty, 0]...
- **docs\00-数学符号对照表.md**: 公式方括号不匹配: (-\infty, 0]...
- **docs\FormalMath术语词典-分析学.md**: 公式括号不匹配: [a,b) = \{x \in \mathbb{R} \mid a \leq x < b\}...
- **docs\FormalMath术语词典-分析学.md**: 公式方括号不匹配: [a,b) = \{x \in \mathbb{R} \mid a \leq x < b\}...
- **docs\FormalMath术语词典-分析学.md**: 公式括号不匹配: [a,b)...
- **docs\FormalMath术语词典-分析学.md**: 公式方括号不匹配: [a,b)...
- ... 还有 7121 个类似问题

### 文档结构 (431个)

- **00-MSC编码第九批最终报告.md**: 文档缺少一级标题
- **.github\pull_request_template.md**: 文档缺少一级标题
- **project\concept_graph_validation_report.md**: 文档缺少一级标题
- **project\data_quality_report.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-P0优先级空洞文档列表-2026年01月01日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-格式检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-符号一致性检查报告-2026年01月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\历史报告\00-内容深度评估报告-2026年01月01日.md**: 文档缺少一级标题
- ... 还有 421 个类似问题

### 概念引用 (9609个)

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
- ... 还有 9599 个类似问题

### 文件命名 (42个)

- **docs\12-泛函分析\06-C代数与von Neumann代数-深度扩展版.md**: 文件名包含空格
- **docs\00-核心概念理解三问\11-核心定理多表征\21-van Kampen定理-五种表征.md**: 文件名包含空格
- **docs\00-核心概念理解三问\11-核心定理多表征\22-Seifert-van Kampen定理-五种表征.md**: 文件名包含空格
- **docs\00-核心概念理解三问\11-核心定理多表征\35-de Rham定理-五种表征.md**: 文件名包含空格
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
