#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量导出脚本
支持从多个数据源批量导出知识图谱
"""

import sys
from pathlib import Path
from datetime import datetime
from knowledge_graph_exporter import KnowledgeGraphExporter

# 数据源配置
DATA_SOURCES = {
    "visualization": {
        "path": "project/visualization_data.json",
        "type": "json",
        "description": "可视化数据"
    },
    "concepts": {
        "path": "concept/concept_prerequisites.yaml",
        "type": "yaml", 
        "description": "概念前置关系"
    },
    "geometry": {
        "path": "concept_prerequisites_geometry_topology_update.yaml",
        "type": "yaml",
        "description": "几何拓扑概念"
    }
}


def export_all_sources(base_output_dir: Path = None):
    """批量导出所有数据源"""
    if base_output_dir is None:
        base_output_dir = Path("tools/knowledge-graph-exporter/output")
    
    base_output_dir.mkdir(parents=True, exist_ok=True)
    
    results = {}
    
    for source_name, config in DATA_SOURCES.items():
        source_path = Path(config["path"])
        
        if not source_path.exists():
            print(f"⚠️  跳过 {source_name}: 文件不存在 {source_path}")
            continue
        
        print(f"\n{'='*60}")
        print(f"处理: {config['description']} ({source_name})")
        print(f"{'='*60}")
        
        # 创建输出目录
        output_dir = base_output_dir / source_name
        output_dir.mkdir(exist_ok=True)
        
        # 创建导出器
        exporter = KnowledgeGraphExporter(output_dir=output_dir)
        
        # 加载数据
        if config["type"] == "json":
            success = exporter.load_from_json(source_path)
        else:
            success = exporter.load_from_yaml(source_path)
        
        if not success:
            print(f"❌ {source_name} 加载失败")
            continue
        
        # 导出所有格式
        try:
            exported = exporter.export_all()
            results[source_name] = exported
            print(f"✅ {source_name} 导出完成: {len(exported)} 个文件")
        except Exception as e:
            print(f"❌ {source_name} 导出失败: {e}")
    
    # 生成汇总报告
    _generate_summary_report(base_output_dir, results)
    
    return results


def _generate_summary_report(output_dir: Path, results: dict):
    """生成导出汇总报告"""
    report_path = output_dir / "export_summary.md"
    
    lines = [
        "# 知识图谱批量导出报告\n\n",
        f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}\n\n",
        "## 导出结果汇总\n\n",
        "| 数据源 | 状态 | 导出文件数 | 输出目录 |\n",
        "|--------|------|-----------|----------|\n"
    ]
    
    for source_name, files in results.items():
        status = "✅ 成功" if files else "❌ 失败"
        count = len(files) if files else 0
        lines.append(f"| {source_name} | {status} | {count} | `{source_name}/` |\n")
    
    lines.extend([
        "\n## 详细文件列表\n\n"
    ])
    
    for source_name, files in results.items():
        lines.append(f"### {source_name}\n\n")
        if files:
            for fmt, path in files.items():
                lines.append(f"- **{fmt.upper()}**: `{path}`\n")
        else:
            lines.append("- 导出失败\n")
        lines.append("\n")
    
    lines.append("\n---\n*由 FormalMath 批量导出工具自动生成*\n")
    
    report_path.write_text(''.join(lines), encoding='utf-8')
    print(f"\n📄 汇总报告已生成: {report_path}")


def quick_export(input_file: str, output_dir: str = None):
    """快速导出单个文件"""
    input_path = Path(input_file)
    
    if not input_path.exists():
        print(f"错误: 文件不存在 {input_file}")
        return False
    
    if output_dir is None:
        output_dir = f"output/export_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    exporter = KnowledgeGraphExporter(output_dir=output_path)
    
    # 根据扩展名判断类型
    if input_path.suffix == '.json':
        success = exporter.load_from_json(input_path)
    elif input_path.suffix in ['.yaml', '.yml']:
        success = exporter.load_from_yaml(input_path)
    else:
        print(f"错误: 不支持的文件格式 {input_path.suffix}")
        return False
    
    if not success:
        print("数据加载失败")
        return False
    
    # 导出所有格式
    print(f"\n导出到: {output_path}")
    results = exporter.export_all()
    
    print("\n✅ 导出完成!")
    for fmt, path in results.items():
        print(f"  - {fmt.upper()}: {path}")
    
    return True


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='批量导出知识图谱')
    parser.add_argument('--input', '-i', help='单个输入文件（如果不指定则批量处理）')
    parser.add_argument('--output', '-o', help='输出目录')
    parser.add_argument('--example', action='store_true', help='导出示例数据')
    
    args = parser.parse_args()
    
    if args.example:
        # 导出示例数据
        example_file = Path(__file__).parent / "example_data.json"
        if example_file.exists():
            quick_export(str(example_file), args.output or "output/example")
        else:
            print("示例数据文件不存在")
    elif args.input:
        # 导出单个文件
        quick_export(args.input, args.output)
    else:
        # 批量导出所有数据源
        print("开始批量导出所有数据源...")
        results = export_all_sources(Path(args.output) if args.output else None)
        print(f"\n{'='*60}")
        print(f"批量导出完成! 成功: {len(results)} 个数据源")
        print(f"{'='*60}")


if __name__ == '__main__':
    main()
