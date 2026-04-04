#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 文档生成脚本
Document Generation Script

命令行入口，用于自动化生成文档
"""

import sys
import argparse
from pathlib import Path
from datetime import datetime

# 确保可以导入本包
sys.path.insert(0, str(Path(__file__).parent))

try:
    from doc_generator import DocumentGenerator, GenerationConfig
except ImportError:
    try:
        # 尝试直接导入
        import importlib.util
        spec = importlib.util.spec_from_file_location("doc_generator", str(Path(__file__).parent / "doc_generator.py"))
        doc_gen_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(doc_gen_module)
        DocumentGenerator = doc_gen_module.DocumentGenerator
        GenerationConfig = doc_gen_module.GenerationConfig
    except Exception as e:
        print(f"错误: 无法导入文档生成器模块: {e}")
        print("请确保在正确的目录运行此脚本")
        sys.exit(1)


def create_parser() -> argparse.ArgumentParser:
    """创建命令行参数解析器"""
    parser = argparse.ArgumentParser(
        prog='generate_docs.py',
        description='FormalMath 文档自动生成系统',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
示例用法:
  # 生成所有文档
  python generate_docs.py
  
  # 只生成API文档
  python generate_docs.py --api-only
  
  # 指定输出目录
  python generate_docs.py -o ./output
  
  # 导出特定格式
  python generate_docs.py -f markdown html json
  
  # 生成特定语言版本
  python generate_docs.py -l zh en
        '''
    )
    
    parser.add_argument(
        '-o', '--output',
        type=str,
        default='docs/generated',
        help='输出目录 (默认: docs/generated)'
    )
    
    parser.add_argument(
        '-f', '--formats',
        nargs='+',
        choices=['markdown', 'html', 'json', 'pdf', 'docx'],
        default=['markdown', 'html', 'json'],
        help='导出格式 (默认: markdown html json)'
    )
    
    parser.add_argument(
        '-l', '--languages',
        nargs='+',
        default=['zh', 'en'],
        help='生成语言 (默认: zh en)'
    )
    
    parser.add_argument(
        '--api-only',
        action='store_true',
        help='只生成API文档'
    )
    
    parser.add_argument(
        '--concepts-only',
        action='store_true',
        help='只生成概念图谱'
    )
    
    parser.add_argument(
        '--lean4-only',
        action='store_true',
        help='只生成Lean4文档'
    )
    
    parser.add_argument(
        '--i18n-only',
        action='store_true',
        help='只生成国际化文档'
    )
    
    parser.add_argument(
        '--source-api',
        type=str,
        default='tools',
        help='API源代码目录 (默认: tools)'
    )
    
    parser.add_argument(
        '--source-concepts',
        type=str,
        default='concept',
        help='概念文档目录 (默认: concept)'
    )
    
    parser.add_argument(
        '--source-lean4',
        type=str,
        default='docs/09-形式化证明',
        help='Lean4源代码目录 (默认: docs/09-形式化证明)'
    )
    
    parser.add_argument(
        '--source-docs',
        type=str,
        default='docs',
        help='文档源目录 (默认: docs)'
    )
    
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='显示详细输出'
    )
    
    parser.add_argument(
        '--version',
        action='version',
        version='%(prog)s 1.0.0'
    )
    
    return parser


def main():
    """主函数"""
    parser = create_parser()
    args = parser.parse_args()
    
    # 根据参数决定启用哪些模块
    enable_api = not (args.concepts_only or args.lean4_only or args.i18n_only)
    enable_concepts = not (args.api_only or args.lean4_only or args.i18n_only)
    enable_lean4 = not (args.api_only or args.concepts_only or args.i18n_only)
    enable_i18n = not (args.api_only or args.concepts_only or args.lean4_only)
    
    # 如果只指定了一个only，启用对应的模块
    if args.api_only:
        enable_api = True
    if args.concepts_only:
        enable_concepts = True
    if args.lean4_only:
        enable_lean4 = True
    if args.i18n_only:
        enable_i18n = True
    
    # 创建配置
    config = GenerationConfig(
        output_dir=Path(args.output),
        enable_api_doc=enable_api,
        enable_concept_graph=enable_concepts,
        enable_lean4_doc=enable_lean4,
        enable_i18n=enable_i18n,
        formats=args.formats,
        languages=args.languages
    )
    
    # 源路径配置
    source_paths = {
        'api': Path(args.source_api),
        'concepts': Path(args.source_concepts),
        'lean4': Path(args.source_lean4),
        'docs': Path(args.source_docs)
    }
    
    # 显示配置信息
    print("=" * 60)
    print("FormalMath 文档自动生成系统 v1.0.0")
    print("=" * 60)
    print(f"\n配置信息:")
    print(f"  输出目录: {config.output_dir}")
    print(f"  API文档: {'启用' if enable_api else '禁用'}")
    print(f"  概念图谱: {'启用' if enable_concepts else '禁用'}")
    print(f"  Lean4文档: {'启用' if enable_lean4 else '禁用'}")
    print(f"  国际化: {'启用' if enable_i18n else '禁用'}")
    print(f"  导出格式: {', '.join(config.formats)}")
    print(f"  语言: {', '.join(config.languages)}")
    print()
    
    # 执行生成
    try:
        generator = DocumentGenerator(config)
        report = generator.generate_all(source_paths)
        
        # 打印结果
        print("\n" + "=" * 60)
        print("生成完成!")
        print("=" * 60)
        print(f"\n统计信息:")
        print(f"  总耗时: {report['duration']:.2f}秒")
        print(f"  生成文件: {len(report['generated_files'])} 个")
        print(f"  API文档: {report['stats'].get('api_files', 0)} 个")
        print(f"  概念图谱: {report['stats'].get('concept_files', 0)} 个")
        print(f"  Lean4文档: {report['stats'].get('lean4_files', 0)} 个")
        print(f"  国际化: {report['stats'].get('i18n_files', 0)} 个")
        
        if report['errors']:
            print(f"\n警告: 发生 {len(report['errors'])} 个错误")
            if args.verbose:
                for error in report['errors']:
                    print(f"  - {error}")
        
        print(f"\n输出位置: {config.output_dir.absolute()}")
        print(f"主索引: {config.output_dir / 'index.md'}")
        
        return 0
        
    except KeyboardInterrupt:
        print("\n\n用户中断")
        return 130
    except Exception as e:
        print(f"\n\n错误: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
