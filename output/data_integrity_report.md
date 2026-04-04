# FormalMath 数据完整性检查报告

**检查时间**: 2026-04-04 17:02:16
**检查目录**: G:\_src\FormalMath

## 检查概览

| 检查项 | 结果 |
|--------|------|
| JSON文件有效 | 2121 |
| JSON文件无效 | 78 |
| YAML文件有效 | 196 |
| YAML文件无效 | 136 |
| Markdown文件已检查 | 10905 |

## 问题统计

- **错误总数**: 32763
- **警告总数**: 16824

## 错误详情

### JSON格式错误 (78个)

- **.vscode\extensions.json**: JSON解析错误: Expecting value: line 3 column 5 (char 29)
- **.vscode\settings.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 2 column 3 (char 4)
- **FormalMath-Enhanced\testing\test-data\mock-learning-paths.json**: JSON解析错误: Expecting ',' delimiter: line 101 column 33 (char 5709)
- **FormalMath-Interactive\node_modules\array-buffer-byte-length\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 3 (char 84)
- **FormalMath-Interactive\node_modules\async-function\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 2 (char 79)
- **FormalMath-Interactive\node_modules\available-typed-arrays\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 3 column 5 (char 29)
- **FormalMath-Interactive\node_modules\call-bind-apply-helpers\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 5 column 2 (char 79)
- **FormalMath-Interactive\node_modules\call-bound\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 6 column 2 (char 100)
- **FormalMath-Interactive\node_modules\data-view-buffer\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 4 column 39 (char 94)
- **FormalMath-Interactive\node_modules\data-view-byte-length\tsconfig.json**: JSON解析错误: Expecting property name enclosed in double quotes: line 4 column 39 (char 94)
- ... 还有 68 个类似问题

### YAML格式错误 (136个)

- **00-代数学概念依赖配置.yaml**: YAML解析错误: while parsing a block mapping
  in "00-代数学概念依赖配置.yaml", line 11, column 7
expected <block end>, but found '<scalar>'
  in "00-代数学概念依赖配置.yaml", line 15, column 22
- **concept_prerequisites_geometry_topology_update.yaml**: YAML解析错误: while parsing a block mapping
  in "concept_prerequisites_geometry_topology_update.yaml", line 12, column 5
expected <block end>, but found '<scalar>'
  in "concept_prerequisites_geometry_topology_update.yaml", line 13, column 12
- **concept\concept_prerequisites.yaml**: YAML解析错误: while parsing a block mapping
  in "concept\concept_prerequisites.yaml", line 7, column 3
expected <block end>, but found '<scalar>'
  in "concept\concept_prerequisites.yaml", line 8, column 18
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
  in "project\concept_prerequisites_400.yaml", line 12, column 5
expected <block end>, but found '<scalar>'
  in "project\concept_prerequisites_400.yaml", line 13, column 12
- ... 还有 126 个类似问题

### 链接错误 (32548个)

- **00-FormalMath第十一批任务完成报告-全局依赖图与拓扑排序.md**: 链接指向的文件不存在: ../concept/核心概念/00-核心概念索引.md
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../issues
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../discussions
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../pulls
- **CONTRIBUTING.md**: 链接指向的文件不存在: docs/00-贡献者指南/api文档.md
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../discussions
- **CONTRIBUTING.md**: 链接指向的文件不存在: ../../issues/new/choose
- **INDEX.md**: 链接指向的文件不存在: docs/09-形式化证明/lean4-examples/
- **concept\00-P0P1改进工作完成报告-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- **concept\00-P0P1改进最终总结-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- ... 还有 32538 个类似问题

### Frontmatter错误 (1个)

- **.github\pull_request_template.md**: YAML frontmatter格式错误

## 警告详情

### 数学公式 (7134个)

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
- **docs\FormalMath术语词典-分析学.md**: 公式括号不匹配: [a,b) = \{x \in \mathbb{R} \mid a \leq x < b\}...
- **docs\FormalMath术语词典-分析学.md**: 公式方括号不匹配: [a,b) = \{x \in \mathbb{R} \mid a \leq x < b\}...
- **docs\FormalMath术语词典-分析学.md**: 公式括号不匹配: [a,b)...
- ... 还有 7124 个类似问题

### 文档结构 (426个)

- **.github\pull_request_template.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-P0优先级空洞文档列表-2026年01月01日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-文档实质性内容检查报告-2026年01月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-格式检查报告-2026年01月15日.md**: 文档缺少一级标题
- **00-归档\2026年01月\全面归档-2026年01月31日\00-符号一致性检查报告-2026年01月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\历史报告\00-内容深度评估报告-2026年01月01日.md**: 文档缺少一级标题
- **00-归档\2026年01月\历史报告\00-命名检查报告-2025年12月31日.md**: 文档缺少一级标题
- **00-归档\2026年01月\历史报告\00-待删除文档列表-2026年01月01日.md**: 文档缺少一级标题
- **00-归档\2026年01月\历史报告\00-批量删除执行报告-2026年01月01日.md**: 文档缺少一级标题
- ... 还有 416 个类似问题

### 概念引用 (9222个)

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
- ... 还有 9212 个类似问题

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
