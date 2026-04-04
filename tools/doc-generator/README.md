# FormalMath 文档自动生成系统

## 简介

FormalMath 文档自动生成系统是一个综合性的文档生成工具，支持：

- **API文档自动生成** - 从Python源代码提取文档
- **概念图谱文档生成** - 生成知识图谱可视化
- **Lean4文档生成** - 从Lean4源码生成定理文档
- **多格式导出** - 支持Markdown、HTML、JSON、PDF等格式
- **国际化文档生成** - 支持中英文多语言

## 目录结构

```
doc-generator/
├── __init__.py                 # 包初始化
├── doc_generator.py            # 主生成器
├── api_doc_generator.py        # API文档生成器
├── concept_graph_generator.py  # 概念图谱生成器
├── lean4_doc_generator.py      # Lean4文档生成器
├── multi_format_exporter.py    # 多格式导出器
├── i18n_generator.py           # 国际化生成器
├── generate_docs.py            # 命令行脚本
├── templates/                  # 模板文件
├── output/                     # 输出目录
└── README.md                   # 本文件
```

## 快速开始

### 安装依赖

```bash
# Python 3.8+ 已内置所需库
# 可选: 安装YAML支持
pip install pyyaml
```

### 基本用法

```bash
# 生成所有文档
cd tools/doc-generator
python generate_docs.py

# 或从项目根目录
python tools/doc-generator/generate_docs.py
```

### 命令行选项

```bash
# 查看帮助
python generate_docs.py --help

# 生成所有文档
python generate_docs.py

# 只生成API文档
python generate_docs.py --api-only

# 只生成概念图谱
python generate_docs.py --concepts-only

# 只生成Lean4文档
python generate_docs.py --lean4-only

# 只生成国际化文档
python generate_docs.py --i18n-only

# 指定输出目录
python generate_docs.py -o ./my-output

# 指定导出格式
python generate_docs.py -f markdown html json

# 指定语言
python generate_docs.py -l zh en

# 显示详细输出
python generate_docs.py -v
```

## 模块说明

### API文档生成器 (api_doc_generator.py)

从Python源代码提取：
- 类和函数定义
- 文档字符串
- 函数签名
- 参数信息

生成输出：
- Markdown格式的API文档
- HTML格式的交互式文档
- JSON格式的机器可读数据

### 概念图谱生成器 (concept_graph_generator.py)

从概念文档提取：
- 概念定义
- 前置知识关系
- 难度等级
- 学习时长

生成输出：
- D3.js可视化数据
- Mermaid图表
- 学习路径文档
- 统计报告

### Lean4文档生成器 (lean4_doc_generator.py)

从Lean4源码提取：
- 定理和引理
- 定义和结构
- 证明状态
- Mathlib映射

生成输出：
- 定理索引和详情
- 证明指南
- 覆盖率报告
- HTML参考文档

### 多格式导出器 (multi_format_exporter.py)

支持导出格式：
- Markdown合集
- HTML单页
- JSON数据
- PDF导出指南
- DOCX导出指南

### 国际化生成器 (i18n_generator.py)

支持功能：
- 多语言文档生成
- 术语翻译对照
- 语言切换导航
- 中英双语词汇表

## 配置

可以通过修改 `doc_generator.py` 中的 `GenerationConfig` 来配置：

```python
config = GenerationConfig(
    output_dir=Path("docs/generated"),      # 输出目录
    enable_api_doc=True,                     # 启用API文档
    enable_concept_graph=True,               # 启用概念图谱
    enable_lean4_doc=True,                   # 启用Lean4文档
    enable_i18n=True,                        # 启用国际化
    formats=["markdown", "html", "json"],    # 导出格式
    languages=["zh", "en"]                   # 语言
)
```

## 输出结构

```
docs/generated/
├── index.md                    # 主索引
├── generation_report.json      # 生成报告
├── api/                        # API文档
│   ├── index.md
│   ├── modules/
│   └── api_reference.html
├── concepts/                   # 概念图谱
│   ├── overview.md
│   ├── visualization/
│   │   ├── concept_graph.html
│   │   └── concept_graph.json
│   ├── learning_paths.md
│   └── statistics.md
├── lean4/                      # Lean4文档
│   ├── theorems.md
│   ├── theorem_details.md
│   ├── mathlib_mapping.md
│   ├── coverage_report.md
│   └── lean4_reference.html
├── i18n/                       # 国际化
│   ├── language_nav.md
│   ├── bilingual_glossary.md
│   ├── translations.json
│   ├── zh/
│   └── en/
└── export/                     # 导出格式
    ├── formalmath_complete.md
    ├── formalmath_complete.html
    ├── formalmath_data.json
    ├── pdf_export_guide.md
    └── docx_export_guide.md
```

## 集成到工作流

### GitHub Actions 示例

```yaml
name: Generate Documentation

on:
  push:
    branches: [ main ]
  schedule:
    - cron: '0 0 * * 0'  # 每周日运行

jobs:
  docs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.10'
      
      - name: Generate Documentation
        run: |
          cd tools/doc-generator
          python generate_docs.py
      
      - name: Deploy to GitHub Pages
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./docs/generated
```

### 本地定时任务

**Linux/macOS (crontab):**
```bash
# 每天凌晨2点运行
0 2 * * * cd /path/to/FormalMath && python tools/doc-generator/generate_docs.py >> /var/log/formalmath-docs.log 2>&1
```

**Windows (任务计划程序):**
```powershell
# PowerShell脚本
$action = New-ScheduledTaskAction -Execute "python" -Argument "tools/doc-generator/generate_docs.py" -WorkingDirectory "G:\_src\FormalMath"
$trigger = New-ScheduledTaskTrigger -Daily -At 2am
Register-ScheduledTask -Action $action -Trigger $trigger -TaskName "FormalMath-Doc-Generation"
```

## 开发指南

### 添加新的生成器

1. 创建新的生成器类，继承基类或独立实现
2. 实现 `generate_from_directory` 方法
3. 在主生成器中集成新模块
4. 添加命令行参数支持

### 自定义模板

1. 在 `templates/` 目录创建模板文件
2. 在生成器中引用模板
3. 支持Jinja2或类似模板引擎

### 扩展翻译

在 `i18n_generator.py` 中添加新术语：

```python
math_terms = {
    '新术语': 'New Term',
    # ...
}
```

## 故障排除

### 常见问题

**问题**: 找不到Python模块  
**解决**: 确保在正确目录运行，或添加 `sys.path`

**问题**: 中文显示乱码  
**解决**: 确保文件使用UTF-8编码

**问题**: 生成的PDF格式不正确  
**解决**: 使用 `pdf_export_guide.md` 中的方法手动转换

### 调试模式

```bash
# 显示详细错误信息
python generate_docs.py -v
```

## 贡献指南

欢迎贡献代码！请：

1. Fork 本仓库
2. 创建功能分支
3. 提交 Pull Request
4. 确保代码通过测试

## 许可证

MIT License - 参见项目根目录的 LICENSE 文件

## 联系方式

- 项目主页: https://github.com/formalmath/formalmath
- 问题反馈: https://github.com/formalmath/formalmath/issues

---

*由 FormalMath 团队维护*
