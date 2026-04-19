---
title: FormalMath 文档自动生成系统架构
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 文档自动生成系统架构

## 系统概述

```
┌─────────────────────────────────────────────────────────────┐
│                    DocumentGenerator                        │
│                    (统一入口与协调器)                        │
└────────────────────┬────────────────────────────────────────┘
                     │
    ┌────────────────┼────────────────┐
    │                │                │
    ▼                ▼                ▼
┌─────────┐   ┌────────────┐   ┌──────────┐
│APIDoc   │   │ConceptGraph│   │Lean4Doc  │
│Generator│   │Generator   │   │Generator │
└────┬────┘   └─────┬──────┘   └────┬─────┘
     │              │               │
     └──────────────┼───────────────┘
                    │
        ┌───────────┴───────────┐
        │                       │
        ▼                       ▼
┌───────────────┐      ┌────────────────┐
│I18nGenerator  │      │MultiFormat     │
│(国际化)       │      │Exporter        │
└───────────────┘      │(多格式导出)     │
                       └────────────────┘
```

## 模块说明

### 1. DocumentGenerator (主协调器)

**文件**: `doc_generator.py`

**职责**:
- 配置管理
- 模块调度
- 生成流程协调
- 报告汇总

**核心方法**:
```python
generate_all(source_paths: Dict[str, Path]) -> Dict[str, Any]
```

### 2. APIDocGenerator (API文档生成器)

**文件**: `api_doc_generator.py`

**输入**: Python源代码(.py)

**处理流程**:
```
.py文件 → AST解析 → 提取类/函数 → 格式化 → 输出文档
```

**输出**:
- Markdown: 结构化API文档
- HTML: 交互式文档
- JSON: 机器可读数据

### 3. ConceptGraphGenerator (概念图谱生成器)

**文件**: `concept_graph_generator.py`

**输入**: Markdown概念文档(.md) + YAML数据

**处理流程**:
```
Markdown → 提取概念 → 构建关系图 → 可视化数据 → 输出
```

**输出**:
- JSON: D3.js/Vis.js可视化数据
- HTML: 交互式概念图谱
- Mermaid: 依赖关系图
- Markdown: 学习路径、统计报告

### 4. Lean4DocGenerator (Lean4文档生成器)

**文件**: `lean4_doc_generator.py`

**输入**: Lean4源代码(.lean)

**处理流程**:
```
.lean文件 → 语法解析 → 提取定理/定义 → 分析证明状态 → 输出
```

**输出**:
- Markdown: 定理列表、详情、证明指南
- HTML: 形式化参考文档
- JSON: 定理数据库
- Markdown: 覆盖率报告、Mathlib映射

### 5. I18nGenerator (国际化生成器)

**文件**: `i18n_generator.py`

**输入**: Markdown文档(.md)

**处理流程**:
```
源文档 → 术语翻译 → 生成多语言版本 → 输出
```

**输出**:
- 多语言Markdown文档
- 术语翻译对照表
- 语言切换导航
- 双语词汇表

### 6. MultiFormatExporter (多格式导出器)

**文件**: `multi_format_exporter.py`

**输入**: 生成的所有文档

**处理流程**:
```
文档集合 → 格式转换 → 打包输出
```

**输出**:
- Markdown合集
- HTML单页
- JSON数据包
- PDF/DOCX导出指南

## 数据流

```
┌─────────────────────────────────────────────────────────────┐
│                         数据源                               │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│  │Python源码│  │概念文档  │  │Lean4源码│  │Markdown  │   │
│  │(.py)     │  │(.md)     │  │(.lean)   │  │(.md)     │   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │
└───────┼─────────────┼─────────────┼─────────────┼──────────┘
        │             │             │             │
        ▼             ▼             ▼             ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│  APIDoc     │ │   Concept   │ │   Lean4     │ │    I18n     │
│  Generator  │ │   Graph     │ │   Doc       │ │  Generator  │
│             │ │  Generator  │ │  Generator  │ │             │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │               │
       └───────────────┴───────────────┴───────────────┘
                           │
                           ▼
                  ┌────────────────┐
                  │ 统一输出目录    │
                  │ docs/generated │
                  └───────┬────────┘
                          │
           ┌──────────────┼──────────────┐
           │              │              │
           ▼              ▼              ▼
    ┌────────────┐ ┌────────────┐ ┌────────────┐
    │  Markdown  │ │    HTML    │ │    JSON    │
    │   文档     │ │  可视化    │ │   数据     │
    └────────────┘ └────────────┘ └────────────┘
```

## 配置系统

### GenerationConfig 配置项

```python
@dataclass
class GenerationConfig:
    output_dir: Path              # 输出目录
    template_dir: Path            # 模板目录
    
    enable_api_doc: bool          # 启用API文档
    enable_concept_graph: bool    # 启用概念图谱
    enable_lean4_doc: bool        # 启用Lean4文档
    enable_i18n: bool             # 启用国际化
    
    formats: List[str]            # 导出格式
    languages: List[str]          # 语言列表
    default_language: str         # 默认语言
```

## 扩展点

### 添加新的文档生成器

1. 创建新的生成器类:
```python
class NewDocGenerator:
    def __init__(self, output_dir: Path, template_dir: Path = None):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate_from_directory(self, source_dir: Path) -> List[str]:
        # 实现生成逻辑
        generated_files = []
        # ...
        return generated_files
```

2. 在主生成器中集成:
```python
# doc_generator.py
from .new_doc_generator import NewDocGenerator

class DocumentGenerator:
    def __init__(self, config: Optional[GenerationConfig] = None):
        # ...
        self.new_generator = NewDocGenerator(
            output_dir=self.config.output_dir / "new"
        )
```

3. 添加配置选项:
```python
@dataclass
class GenerationConfig:
    # ...
    enable_new_doc: bool = True
```

### 自定义输出格式

在 `MultiFormatExporter` 中添加新的导出方法:

```python
def _export_custom_format(self, source_dir: Path) -> Path:
    """导出自定义格式"""
    output_path = self.export_dir / "custom_format.txt"
    # 实现转换逻辑
    return output_path
```

## 性能考虑

### 并行处理

未来可以添加并行支持:

```python
from concurrent.futures import ThreadPoolExecutor

def generate_all_parallel(self):
    with ThreadPoolExecutor() as executor:
        futures = []
        if self.config.enable_api_doc:
            futures.append(executor.submit(self._generate_api_docs, ...))
        # ...
```

### 增量生成

可以通过缓存和比较时间戳实现增量生成:

```python
def should_regenerate(self, source: Path, output: Path) -> bool:
    if not output.exists():
        return True
    return source.stat().st_mtime > output.stat().st_mtime
```

## 错误处理

### 错误处理策略

1. **源文件错误**: 记录警告，继续处理其他文件
2. **解析错误**: 跳过当前文件，记录错误信息
3. **生成错误**: 记录到报告，不影响其他模块

### 错误报告

所有错误记录在 `generation_report['errors']` 中:

```python
self.generation_report['errors'].append({
    'module': 'api_doc',
    'file': str(file_path),
    'error': str(e),
    'timestamp': datetime.now().isoformat()
})
```

## 测试策略

### 单元测试

每个生成器应有独立的单元测试:

```python
def test_api_doc_generator():
    gen = APIDocGenerator(output_dir=Path("test_output"))
    files = gen.generate_from_directory(Path("test_data"))
    assert len(files) > 0
```

### 集成测试

测试完整的生成流程:

```python
def test_full_generation():
    config = GenerationConfig(output_dir=Path("test_output"))
    generator = DocumentGenerator(config)
    report = generator.generate_all()
    assert report['duration'] > 0
    assert len(report['generated_files']) > 0
```

## 部署方案

### 本地使用

```bash
python generate_docs.py
```

### CI/CD集成

GitHub Actions:
```yaml
- name: Generate Documentation
  run: |
    cd tools/doc-generator
    python generate_docs.py
```

### 定时任务

Linux Cron:
```bash
0 2 * * * cd /path/to/FormalMath && python tools/doc-generator/generate_docs.py
```

Windows Task Scheduler:
```powershell
# 使用 generate-all-docs.ps1 脚本
```

---

*文档版本: 1.0.0*
*最后更新: 2026-04-04*
