#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 文档生成器主类
Document Generator Main Class

整合所有文档生成功能的统一接口
"""

import json
import yaml
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Any, Union
from dataclasses import dataclass, asdict

from .api_doc_generator import APIDocGenerator
from .concept_graph_generator import ConceptGraphGenerator
from .lean4_doc_generator import Lean4DocGenerator
from .multi_format_exporter import MultiFormatExporter
from .i18n_generator import I18nGenerator


@dataclass
class GenerationConfig:
    """文档生成配置"""
    output_dir: Path = None
    template_dir: Path = None
    
    # 各模块开关
    enable_api_doc: bool = True
    enable_concept_graph: bool = True
    enable_lean4_doc: bool = True
    enable_i18n: bool = True
    
    # 导出格式
    formats: List[str] = None
    
    # 国际化设置
    languages: List[str] = None
    default_language: str = "zh"
    
    def __post_init__(self):
        if self.output_dir is None:
            self.output_dir = Path("docs/generated")
        if self.template_dir is None:
            self.template_dir = Path("tools/doc-generator/templates")
        if self.formats is None:
            self.formats = ["markdown", "html", "json"]
        if self.languages is None:
            self.languages = ["zh", "en"]


class DocumentGenerator:
    """
    FormalMath 统一文档生成器
    
    整合所有文档生成功能，提供统一的生成接口
    """
    
    def __init__(self, config: Optional[GenerationConfig] = None):
        self.config = config or GenerationConfig()
        self.config.output_dir.mkdir(parents=True, exist_ok=True)
        
        # 初始化各生成器
        self.api_generator = APIDocGenerator(
            output_dir=self.config.output_dir / "api",
            template_dir=self.config.template_dir
        )
        self.concept_generator = ConceptGraphGenerator(
            output_dir=self.config.output_dir / "concepts",
            template_dir=self.config.template_dir
        )
        self.lean4_generator = Lean4DocGenerator(
            output_dir=self.config.output_dir / "lean4",
            template_dir=self.config.template_dir
        )
        self.i18n_generator = I18nGenerator(
            output_dir=self.config.output_dir / "i18n",
            template_dir=self.config.template_dir,
            languages=self.config.languages,
            default_language=self.config.default_language
        )
        self.exporter = MultiFormatExporter(
            output_dir=self.config.output_dir
        )
        
        # 生成报告
        self.generation_report: Dict[str, Any] = {}
    
    def generate_all(self, source_paths: Optional[Dict[str, Path]] = None) -> Dict[str, Any]:
        """
        生成所有类型的文档
        
        Args:
            source_paths: 源代码路径配置
                {{
                    'api': Path('tools/api'),
                    'concepts': Path('concept'),
                    'lean4': Path('docs/09-形式化证明/Lean4'),
                    'docs': Path('docs')
                }}
        
        Returns:
            生成报告
        """
        if source_paths is None:
            source_paths = {
                'api': Path('tools'),
                'concepts': Path('concept'),
                'lean4': Path('docs/09-形式化证明'),
                'docs': Path('docs')
            }
        
        start_time = datetime.now()
        self.generation_report = {
            'start_time': start_time.isoformat(),
            'config': {
                'output_dir': str(self.config.output_dir),
                'enable_api_doc': self.config.enable_api_doc,
                'enable_concept_graph': self.config.enable_concept_graph,
                'enable_lean4_doc': self.config.enable_lean4_doc,
                'enable_i18n': self.config.enable_i18n,
                'formats': self.config.formats,
                'languages': self.config.languages
            },
            'generated_files': [],
            'errors': [],
            'stats': {}
        }
        
        print("=" * 60)
        print("FormalMath 文档自动生成系统")
        print("=" * 60)
        
        # 1. 生成API文档
        if self.config.enable_api_doc:
            self._generate_api_docs(source_paths.get('api', Path('tools')))
        
        # 2. 生成概念图谱
        if self.config.enable_concept_graph:
            self._generate_concept_graphs(source_paths.get('concepts', Path('concept')))
        
        # 3. 生成Lean4文档
        if self.config.enable_lean4_doc:
            self._generate_lean4_docs(source_paths.get('lean4', Path('docs/09-形式化证明')))
        
        # 4. 生成国际化文档
        if self.config.enable_i18n:
            self._generate_i18n_docs(source_paths.get('docs', Path('docs')))
        
        # 5. 多格式导出
        self._export_multiple_formats()
        
        # 6. 生成索引
        self._generate_master_index()
        
        end_time = datetime.now()
        self.generation_report['end_time'] = end_time.isoformat()
        self.generation_report['duration'] = (end_time - start_time).total_seconds()
        
        # 保存报告
        self._save_report()
        
        print("\n" + "=" * 60)
        print(f"文档生成完成！总耗时: {self.generation_report['duration']:.2f}秒")
        print(f"生成文件数: {len(self.generation_report['generated_files'])}")
        print(f"错误数: {len(self.generation_report['errors'])}")
        print("=" * 60)
        
        return self.generation_report
    
    def _generate_api_docs(self, source_path: Path):
        """生成API文档"""
        print("\n📚 生成API文档...")
        try:
            files = self.api_generator.generate_from_directory(source_path)
            self.generation_report['generated_files'].extend(files)
            self.generation_report['stats']['api_files'] = len(files)
            print(f"  ✓ 生成 {len(files)} 个API文档文件")
        except Exception as e:
            self.generation_report['errors'].append(f"API文档生成错误: {e}")
            print(f"  ✗ API文档生成失败: {e}")
    
    def _generate_concept_graphs(self, source_path: Path):
        """生成概念图谱"""
        print("\n🕸️ 生成概念图谱...")
        try:
            files = self.concept_generator.generate_from_directory(source_path)
            self.generation_report['generated_files'].extend(files)
            self.generation_report['stats']['concept_files'] = len(files)
            print(f"  ✓ 生成 {len(files)} 个概念图谱文件")
        except Exception as e:
            self.generation_report['errors'].append(f"概念图谱生成错误: {e}")
            print(f"  ✗ 概念图谱生成失败: {e}")
    
    def _generate_lean4_docs(self, source_path: Path):
        """生成Lean4文档"""
        print("\n🔧 生成Lean4文档...")
        try:
            files = self.lean4_generator.generate_from_directory(source_path)
            self.generation_report['generated_files'].extend(files)
            self.generation_report['stats']['lean4_files'] = len(files)
            print(f"  ✓ 生成 {len(files)} 个Lean4文档文件")
        except Exception as e:
            self.generation_report['errors'].append(f"Lean4文档生成错误: {e}")
            print(f"  ✗ Lean4文档生成失败: {e}")
    
    def _generate_i18n_docs(self, source_path: Path):
        """生成国际化文档"""
        print("\n🌍 生成国际化文档...")
        try:
            files = self.i18n_generator.generate_from_directory(source_path)
            self.generation_report['generated_files'].extend(files)
            self.generation_report['stats']['i18n_files'] = len(files)
            print(f"  ✓ 生成 {len(files)} 个国际化文档文件")
        except Exception as e:
            self.generation_report['errors'].append(f"国际化文档生成错误: {e}")
            print(f"  ✗ 国际化文档生成失败: {e}")
    
    def _export_multiple_formats(self):
        """多格式导出"""
        print("\n📦 多格式导出...")
        try:
            for format_type in self.config.formats:
                output_path = self.exporter.export_all(
                    self.config.output_dir,
                    format_type
                )
                self.generation_report['generated_files'].append(str(output_path))
                print(f"  ✓ 导出 {format_type.upper()} 格式")
        except Exception as e:
            self.generation_report['errors'].append(f"多格式导出错误: {e}")
            print(f"  ✗ 多格式导出失败: {e}")
    
    def _generate_master_index(self):
        """生成主索引"""
        print("\n📑 生成主索引...")
        index_path = self.config.output_dir / "index.md"
        
        content = f"""# FormalMath 生成文档索引

**生成时间**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## 文档分类

### API文档
- [API索引](api/index.md)
- [模块文档](api/modules/)

### 概念图谱
- [概念总图](concepts/overview.md)
- [可视化数据](concepts/visualization/)

### Lean4形式化
- [定理列表](lean4/theorems.md)
- [证明文档](lean4/theorem_details.md)
- [Mathlib映射](lean4/mathlib_mapping.md)
- [覆盖率报告](lean4/coverage_report.md)

### 国际化文档
- [语言导航](i18n/language_nav.md)
- [术语对照](i18n/bilingual_glossary.md)
- [英文版](i18n/en/)
- [中文版](i18n/zh/)

### 导出格式
"""
        for fmt in self.config.formats:
            content += f"- [{fmt.upper()}](export/formalmath_{fmt}.md)\n"
        
        content += f"""
## 生成统计

- API文档: {self.generation_report['stats'].get('api_files', 0)} 个
- 概念图谱: {self.generation_report['stats'].get('concept_files', 0)} 个
- Lean4文档: {self.generation_report['stats'].get('lean4_files', 0)} 个
- 国际化文档: {self.generation_report['stats'].get('i18n_files', 0)} 个
- 总计: {len(self.generation_report['generated_files'])} 个文件

---
*由 FormalMath 文档自动生成系统创建*
"""
        
        index_path.write_text(content, encoding='utf-8')
        self.generation_report['generated_files'].append(str(index_path))
        print(f"  ✓ 主索引已生成: {index_path}")
    
    def _save_report(self):
        """保存生成报告"""
        report_path = self.config.output_dir / "generation_report.json"
        with open(report_path, 'w', encoding='utf-8') as f:
            json.dump(self.generation_report, f, ensure_ascii=False, indent=2)
        print(f"\n📊 生成报告已保存: {report_path}")


def main():
    """主函数 - 示例用法"""
    config = GenerationConfig(
        output_dir=Path("docs/generated"),
        enable_api_doc=True,
        enable_concept_graph=True,
        enable_lean4_doc=True,
        enable_i18n=True,
        formats=["markdown", "html", "json"],
        languages=["zh", "en"]
    )
    
    generator = DocumentGenerator(config)
    report = generator.generate_all()
    
    # 打印摘要
    print("\n📋 生成摘要:")
    print(f"  开始时间: {report['start_time']}")
    print(f"  结束时间: {report['end_time']}")
    print(f"  总耗时: {report['duration']:.2f}秒")
    print(f"  生成文件: {len(report['generated_files'])} 个")
    
    return report


if __name__ == '__main__':
    main()
