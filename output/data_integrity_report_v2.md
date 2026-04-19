---
title: FormalMath 数据完整性检查报告
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 数据完整性检查报告

**检查时间**: 2026-04-04 16:46:27
**检查目录**: G:\_src\FormalMath
**检查范围**: 排除 node_modules, .git, .vscode, 00-归档

## 检查概览

| 检查项 | 结果 |
|--------|------|
| JSON文件有效 | 120 |
| JSON文件无效 | 1 |
| YAML文件有效 | 15 |
| YAML文件无效 | 124 |
| Markdown文件已检查 | 8223 |

## 问题统计

- **错误总数**: 31861
- **警告总数**: 9567

## 错误详情 (需要修复)

### JSON格式错误 (1个)

- **FormalMath-Enhanced\testing\test-data\mock-learning-paths.json**: JSON解析错误: Expecting ',' delimiter: line 101 column 33 (char 5709)

### YAML格式错误 (124个)

- **00-代数学概念依赖配置.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 11, column 7:
        - concept_id: C.CORE.008
          ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 15, column 22:
          wikipedia_zh: "https://zh.wikipedia.org/wiki/群"
                         ^
- **concept\concept_prerequisites.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 7, column 3:
      version: "1.0'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 18:
      last_updated: "2026-04-04"
                     ^
- **k8s\02-configmap.yaml**: YAML解析错误: expected a single document in the stream
  in "<unicode string>", line 1, column 1:
    apiVersion: v1
    ^
but found another document
  in "<unicode string>", line 40, column 1:
    ---
    ^
- **k8s\03-secret.yaml**: YAML解析错误: expected a single document in the stream
  in "<unicode string>", line 1, column 1:
    apiVersion: v1
    ^
but found another document
  in "<unicode string>", line 31, column 1:
    ---
    ^
- **k8s\07-ingress.yaml**: YAML解析错误: expected a single document in the stream
  in "<unicode string>", line 1, column 1:
    apiVersion: networking.k8s.io/v1
    ^
but found another document
  in "<unicode string>", line 70, column 1:
    ---
    ^
- **project\concept_prerequisites_probability_extension.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      version: "1.0'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 7, column 10:
      date: "2026-04-04"
             ^
- **project\msc_applied_math_mapping.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      version: "1.0'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 7, column 10:
      date: "2026-04-04"
             ^
- **project\msc_geometry_topology_mapping.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 1:
    version: "1.0'
    ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 7, column 11:
    created: "2026-04-04"
              ^
- **project\概念关联图谱数据.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 12, column 7:
        - id: "GRP'
          ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 13, column 14:
          name: "群"
                 ^
- **concept\03-主题概念梳理\06-数论概念-prerequisites-更新.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      title: "数论概念前置条件配置'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 7, column 17:
      description: "与Wikipedia结构对齐的数论概念前置条件"
                    ^
- **docs\09-形式化证明\mathlib4-mapping.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 8, column 3:
      project: FormalMath
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 12, column 18:
      last_updated: "2026-04-03"
                     ^
- **docs\00-核心概念理解三问\12-知识图谱系统\03-关系数据\concept-relations.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 14, column 5:
      - source: "group'
        ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 15, column 14:
        target: "set"
                 ^
- **docs\00-核心概念理解三问\12-知识图谱系统\03-关系数据\theorem-relations.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 13, column 5:
      - theorem: "lagrange-theorem'
        ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 15, column 14:
          - id: "group"
                 ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\commutator.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "commutator'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "交换子"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\eigenvalue.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "eigenvalue'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "特征值"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\field.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "field'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "域"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\group.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "group'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "群"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\homomorphism.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "homomorphism'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "同态"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\ideal.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "ideal'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "理想"
             ^
- **docs\00-核心概念理解三问\12-知识图谱系统\01-概念节点\代数学\invariant-ring.yaml**: YAML解析错误: while parsing a block mapping
  in "<unicode string>", line 6, column 3:
      id: "invariant-ring'
      ^
expected <block end>, but found '<scalar>'
  in "<unicode string>", line 8, column 10:
        zh: "不变量环"
             ^
- ... 还有 104 个类似问题

### 链接错误 (31736个)

- **00-FormalMath第十一批任务完成报告-全局依赖图与拓扑排序.md**: 链接指向的文件不存在: ../concept/核心概念/00-核心概念索引.md
- **CONTRIBUTING.md**: 链接指向的文件不存在: docs/00-贡献者指南/api文档.md
- **INDEX.md**: 链接指向的文件不存在: docs/09-形式化证明/lean4-examples/
- **concept\00-P0P1改进工作完成报告-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- **concept\00-P0P1改进最终总结-2025年11月.md**: 链接指向的文件不存在: ./00-P0P1改进完成总结-2025年11月.md
- **concept\00-国际主流数学认知理论整合框架-2025年1月.md**: 链接指向的文件不存在: ./00-概念体系深度改进计划-2025年1月.md
- **concept\00-国际主流数学认知理论整合框架-2025年1月.md**: 链接指向的文件不存在: ../view/03-数学认知的心理学视角/01-CPFS结构理论/01-CPFS结构理论.md
- **concept\00-国际主流数学认知理论整合框架-2025年1月.md**: 链接指向的文件不存在: ../view/数学认知结构理论框架.md
- **concept\00-国际优秀教育国家思维表征方法研究-2025年11月28日.md**: 链接指向的文件不存在: ../04-认知工具/07-认知方式表征综合.md
- **concept\00-完整索引.md**: 链接指向的文件不存在: ./00-集合论视角的概念层次结构分析.md
- **concept\00-对标分析与改进计划-2025年11月28日.md**: 链接指向的文件不存在: ../view/资料库/01-数学家思维过程/00-数学家思维过程总览.md
- **concept\00-思维表征方法全面整合指南-2025年11月28日.md**: 链接指向的文件不存在: ../04-认知工具/07-认知方式表征综合.md
- **concept\00-思维表征方法全面梳理完成报告-2025年11月28日.md**: 链接指向的文件不存在: ../04-认知工具/07-认知方式表征综合.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-概念体系深度改进计划-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/00-资源收集进展总结报告-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/MIT-OCW数学课程资源索引-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/新加坡数学教育课程资源索引-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/IB-AP数学课程资源索引-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/Stanford-数学课程资源索引-2025年1月.md
- **concept\00-改进计划实施进度跟踪-2025年1月.md**: 链接指向的文件不存在: ./00-资源库/Harvard-数学课程资源索引-2025年1月.md
- ... 还有 5860 个类似问题

## 警告详情 (建议优化)

### 元数据 (3个)

- **00-Wikipedia代数学概念结构映射.json**: 缺少last_updated字段
- **wikipedia_applied_math_mapping.json**: 缺少last_updated字段
- **project\wikipedia_probability_statistics_mapping.json**: 缺少last_updated字段

### 文件命名 (21个)

- **docs\00-核心概念理解三问\11-核心定理多表征\21-van Kampen定理-五种表征.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\00-核心概念理解三问\11-核心定理多表征\22-Seifert-van Kampen定理-五种表征.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\00-核心概念理解三问\11-核心定理多表征\35-de Rham定理-五种表征.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\01-概念理解\28- Zorn与极大元-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\01-概念理解\30- Riemann积分与Darboux和-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\02-计算示例\19- Jordan标准形-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\02-计算示例\20- Gram-Schmidt正交化-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\02-计算示例\27- Green公式计算-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\15- Banach不动点-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\16- Hahn-Banach延拓-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\17- Fermat小定理-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\18- Bolzano-Weierstrass-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\19- Lagrange中值-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\20- 可数并可数-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- **docs\工作示例\03-证明示例\21- 闭图像定理-工作示例.md**: 文件名包含空格（建议使用中横线或下划线）
- ... 还有 6 个类似问题

### 概念引用 (9543个)

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
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.034
- **00-代数学概念依赖配置.yaml**: 引用的概念ID可能不存在: C.CORE.035
- **concept_prerequisites_geometry_topology_update.yaml**: 引用的概念ID可能不存在: continuous_map
- **concept_prerequisites_geometry_topology_update.yaml**: 引用的概念ID可能不存在: bijection
- **concept_prerequisites_geometry_topology_update.yaml**: 引用的概念ID可能不存在: topological_invariant
- ... 还有 4377 个类似问题

## 修复建议

### JSON格式错误
1. 使用JSON验证器（如 jsonlint.com）检查文件
2. 修复引号、逗号等语法问题

### YAML格式错误
1. 检查缩进（使用空格而非Tab）
2. 确保特殊字符正确转义
3. 检查冒号后是否有空格

### 链接错误
1. 更新失效的相对链接指向正确的文件路径
2. 对于已删除的文件，移除相关链接
3. 使用绝对路径 `/docs/...` 或正确的相对路径 `./file.md`

### 文件命名
1. 文件名中的空格替换为中横线 `-` 或下划线 `_`
2. 避免使用特殊字符

