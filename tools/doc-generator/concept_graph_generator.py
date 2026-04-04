#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念图谱文档生成器
Concept Graph Documentation Generator

生成概念依赖关系图谱、可视化数据、Mermaid图表
"""

import re
import json
import yaml
from pathlib import Path
from typing import List, Dict, Any, Set, Tuple
from collections import defaultdict
from datetime import datetime
from dataclasses import dataclass, field


@dataclass
class Concept:
    """概念节点"""
    id: str
    name: str
    name_en: str = ""
    category: str = ""
    difficulty: int = 1
    estimated_hours: float = 1.0
    description: str = ""
    prerequisites: List[Dict[str, Any]] = field(default_factory=list)
    related_concepts: List[str] = field(default_factory=list)
    learning_objectives: List[str] = field(default_factory=list)
    msc_code: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'id': self.id,
            'name': self.name,
            'name_en': self.name_en,
            'category': self.category,
            'difficulty': self.difficulty,
            'estimated_hours': self.estimated_hours,
            'description': self.description[:100] if self.description else "",
            'prerequisites': self.prerequisites,
            'msc_code': self.msc_code
        }


@dataclass
class ConceptRelation:
    """概念关系"""
    source: str
    target: str
    relation_type: str  # depends_on, related_to, part_of, leads_to
    strength: float = 1.0


class ConceptGraphGenerator:
    """
    概念图谱生成器
    
    从Markdown文档中提取概念信息，生成知识图谱、可视化数据和文档
    """
    
    def __init__(self, output_dir: Path, template_dir: Path = None):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.template_dir = template_dir
        
        self.concepts: Dict[str, Concept] = {}
        self.relations: List[ConceptRelation] = []
        
        # 类别颜色映射
        self.category_colors = {
            "分析学": "#E3F2FD",
            "代数学": "#F3E5F5",
            "几何拓扑": "#E8F5E9",
            "数论逻辑": "#FBE9E7",
            "概率统计": "#FFF8E1",
            "最优化": "#E0F2F1",
            "控制论": "#E1F5FE",
            "信息论": "#F3E5F5",
            "密码学": "#ECEFF1"
        }
    
    def generate_from_directory(self, source_dir: Path) -> List[str]:
        """
        从概念目录生成图谱文档
        
        Args:
            source_dir: 概念文档目录
            
        Returns:
            生成的文件路径列表
        """
        generated_files = []
        source_dir = Path(source_dir)
        
        print(f"  扫描概念目录: {source_dir}")
        
        # 1. 提取所有概念
        if source_dir.exists():
            for md_file in source_dir.rglob("*.md"):
                try:
                    self._extract_concepts_from_file(md_file)
                except Exception as e:
                    print(f"  警告: 处理 {md_file} 失败: {e}")
        
        # 2. 也从docs目录提取概念
        docs_dir = Path("docs")
        if docs_dir.exists():
            for md_file in docs_dir.rglob("*.md"):
                try:
                    self._extract_concepts_from_file(md_file)
                except Exception as e:
                    pass  # 忽略docs目录的错误
        
        print(f"  提取了 {len(self.concepts)} 个概念")
        
        if not self.concepts:
            # 使用示例数据
            self._load_sample_concepts()
        
        # 3. 构建关系
        self._build_relations()
        
        # 4. 生成各类文档
        generated_files.extend(self._generate_visualization_data())
        generated_files.extend(self._generate_mermaid_diagrams())
        generated_files.extend(self._generate_concept_docs())
        generated_files.append(str(self._generate_statistics_report()))
        generated_files.append(str(self._generate_learning_paths()))
        
        return generated_files
    
    def _extract_concepts_from_file(self, file_path: Path):
        """从Markdown文件提取概念"""
        content = file_path.read_text(encoding='utf-8')
        
        # 提取YAML frontmatter
        yaml_match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        metadata = {}
        if yaml_match:
            try:
                metadata = yaml.safe_load(yaml_match.group(1))
            except:
                pass
        
        # 提取标题作为概念名
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if title_match:
            concept_name = title_match.group(1).strip()
            concept_id = self._generate_concept_id(concept_name)
            
            # 提取类别
            category = metadata.get('category', self._detect_category(file_path))
            
            # 提取MSC编码
            msc_code = metadata.get('msc_primary', metadata.get('msc', ''))
            
            # 提取难度（从文件名或内容）
            difficulty = self._detect_difficulty(file_path, content)
            
            # 提取前置知识
            prerequisites = self._extract_prerequisites(content)
            
            concept = Concept(
                id=concept_id,
                name=concept_name,
                name_en=metadata.get('name_en', ''),
                category=category,
                difficulty=difficulty,
                estimated_hours=difficulty * 2.0,
                description=content[:500],
                prerequisites=prerequisites,
                msc_code=msc_code
            )
            
            self.concepts[concept_id] = concept
    
    def _generate_concept_id(self, name: str) -> str:
        """生成概念ID"""
        # 取前4个汉字或拼音首字母
        import hashlib
        hash_obj = hashlib.md5(name.encode('utf-8'))
        return f"C{hash_obj.hexdigest()[:6].upper()}"
    
    def _detect_category(self, file_path: Path) -> str:
        """检测概念类别"""
        path_str = str(file_path).lower()
        
        if '代数' in path_str or '群' in path_str or '环' in path_str:
            return "代数学"
        elif '分析' in path_str or '微积分' in path_str or '实分析' in path_str:
            return "分析学"
        elif '几何' in path_str or '拓扑' in path_str:
            return "几何拓扑"
        elif '数论' in path_str or '逻辑' in path_str:
            return "数论逻辑"
        elif '概率' in path_str or '统计' in path_str:
            return "概率统计"
        else:
            return "基础数学"
    
    def _detect_difficulty(self, file_path: Path, content: str) -> int:
        """检测难度等级"""
        path_str = str(file_path).lower()
        
        if '深度扩展' in path_str or '高级' in content[:1000]:
            return 4
        elif '增强' in path_str or '中级' in content[:1000]:
            return 3
        elif '基础' in path_str:
            return 1
        else:
            return 2
    
    def _extract_prerequisites(self, content: str) -> List[Dict[str, Any]]:
        """提取前置知识"""
        prerequisites = []
        
        # 查找前置知识部分
        prereq_match = re.search(
            r'前置知识|先修|Prerequisites|prerequisites\s*\n(.*?)(?:\n##|\n#|$)',
            content,
            re.DOTALL | re.IGNORECASE
        )
        
        if prereq_match:
            prereq_section = prereq_match.group(1)
            # 提取列表项
            items = re.findall(r'[-*]\s*(.+)', prereq_section)
            for item in items[:5]:  # 最多5个前置知识
                prereq_id = self._generate_concept_id(item.strip())
                prerequisites.append({
                    'concept_id': prereq_id,
                    'name': item.strip(),
                    'relation': '依赖',
                    'level': 'L1'
                })
        
        return prerequisites
    
    def _build_relations(self):
        """构建概念关系"""
        for concept in self.concepts.values():
            for prereq in concept.prerequisites:
                if prereq['concept_id'] in self.concepts:
                    self.relations.append(ConceptRelation(
                        source=prereq['concept_id'],
                        target=concept.id,
                        relation_type='depends_on'
                    ))
    
    def _load_sample_concepts(self):
        """加载示例概念数据"""
        sample_concepts = [
            Concept("C001", "集合论", "Set Theory", "基础数学", 1, 10, "数学基础"),
            Concept("C002", "群论", "Group Theory", "代数学", 2, 20, "代数结构的基础"),
            Concept("C003", "环论", "Ring Theory", "代数学", 3, 25, "代数结构"),
            Concept("C004", "实分析", "Real Analysis", "分析学", 3, 40, "实数分析"),
            Concept("C005", "拓扑学", "Topology", "几何拓扑", 3, 35, "空间性质研究"),
            Concept("C006", "泛函分析", "Functional Analysis", "分析学", 4, 50, "无限维空间"),
        ]
        
        # 添加前置关系
        sample_concepts[1].prerequisites = [{'concept_id': 'C001', 'name': '集合论'}]
        sample_concepts[2].prerequisites = [{'concept_id': 'C002', 'name': '群论'}]
        sample_concepts[4].prerequisites = [{'concept_id': 'C004', 'name': '实分析'}]
        sample_concepts[5].prerequisites = [{'concept_id': 'C004', 'name': '实分析'}]
        
        for c in sample_concepts:
            self.concepts[c.id] = c
        
        self._build_relations()
    
    def _generate_visualization_data(self) -> List[str]:
        """生成可视化数据（D3.js/Vis.js格式）"""
        generated = []
        
        viz_dir = self.output_dir / "visualization"
        viz_dir.mkdir(exist_ok=True)
        
        # 节点数据
        nodes = []
        for c in self.concepts.values():
            node = {
                "id": c.id,
                "label": c.name,
                "title": c.name_en or c.name,
                "category": c.category,
                "difficulty": c.difficulty,
                "estimated_hours": c.estimated_hours,
                "group": self._get_category_group(c.category),
                "color": self.category_colors.get(c.category, "#FFFFFF"),
                "msc_code": c.msc_code
            }
            nodes.append(node)
        
        # 边数据
        edges = []
        for i, rel in enumerate(self.relations):
            edge = {
                "id": f"e{i}",
                "from": rel.source,
                "to": rel.target,
                "label": rel.relation_type,
                "arrows": "to"
            }
            edges.append(edge)
        
        # 保存JSON
        viz_data = {
            "metadata": {
                "generated_at": datetime.now().isoformat(),
                "total_concepts": len(nodes),
                "total_relations": len(edges)
            },
            "nodes": nodes,
            "edges": edges
        }
        
        json_path = viz_dir / "concept_graph.json"
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(viz_data, f, ensure_ascii=False, indent=2)
        generated.append(str(json_path))
        
        # 生成D3.js可视化HTML
        html_path = self._generate_d3_visualization(viz_data)
        generated.append(str(html_path))
        
        print(f"  ✓ 生成可视化数据: {len(nodes)} 节点, {len(edges)} 关系")
        return generated
    
    def _get_category_group(self, category: str) -> int:
        """获取类别分组编号"""
        groups = {
            "分析学": 1, "代数学": 2, "几何拓扑": 3,
            "数论逻辑": 4, "概率统计": 5, "最优化": 6,
            "控制论": 7, "信息论": 8, "密码学": 9,
            "基础数学": 0
        }
        return groups.get(category, 0)
    
    def _generate_d3_visualization(self, viz_data: Dict) -> Path:
        """生成D3.js可视化页面"""
        output_path = self.output_dir / "visualization" / "concept_graph.html"
        
        html_content = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>FormalMath 概念图谱可视化</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        body {{ margin: 0; font-family: -apple-system, sans-serif; background: #f5f7fa; }}
        #container {{ width: 100vw; height: 100vh; }}
        .node {{ cursor: pointer; }}
        .link {{ stroke: #999; stroke-opacity: 0.6; stroke-width: 1.5; }}
        .node-label {{ font-size: 12px; pointer-events: none; text-anchor: middle; }}
        #info-panel {{
            position: fixed; top: 20px; right: 20px;
            background: white; padding: 20px; border-radius: 8px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1); max-width: 300px;
        }}
        .legend {{
            position: fixed; bottom: 20px; left: 20px;
            background: white; padding: 15px; border-radius: 8px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }}
    </style>
</head>
<body>
    <div id="container"></div>
    <div id="info-panel">
        <h3>概念信息</h3>
        <p>点击节点查看详情</p>
    </div>
    <div class="legend">
        <h4>类别图例</h4>
        {self._generate_legend_html()}
    </div>
    
    <script>
        const data = {json.dumps(viz_data, ensure_ascii=False)};
        
        const width = window.innerWidth;
        const height = window.innerHeight;
        
        const svg = d3.select("#container")
            .append("svg")
            .attr("width", width)
            .attr("height", height);
        
        const simulation = d3.forceSimulation(data.nodes)
            .force("link", d3.forceLink(data.edges).id(d => d.id).distance(100))
            .force("charge", d3.forceManyBody().strength(-300))
            .force("center", d3.forceCenter(width / 2, height / 2));
        
        const link = svg.append("g")
            .selectAll("line")
            .data(data.edges)
            .join("line")
            .attr("class", "link");
        
        const node = svg.append("g")
            .selectAll("circle")
            .data(data.nodes)
            .join("circle")
            .attr("class", "node")
            .attr("r", d => 10 + d.difficulty * 3)
            .attr("fill", d => d.color)
            .call(d3.drag()
                .on("start", dragstarted)
                .on("drag", dragged)
                .on("end", dragended));
        
        const label = svg.append("g")
            .selectAll("text")
            .data(data.nodes)
            .join("text")
            .attr("class", "node-label")
            .attr("dy", d => 25 + d.difficulty * 3)
            .text(d => d.label);
        
        node.on("click", (event, d) => {{
            document.getElementById("info-panel").innerHTML = `
                <h3>${{d.label}}</h3>
                <p><strong>类别:</strong> ${{d.category}}</p>
                <p><strong>难度:</strong> ${{d.difficulty}}/5</p>
                <p><strong>预计学时:</strong> ${{d.estimated_hours}}小时</p>
                ${{d.msc_code ? `<p><strong>MSC:</strong> ${{d.msc_code}}</p>` : ''}}
            `;
        }});
        
        simulation.on("tick", () => {{
            link
                .attr("x1", d => d.source.x)
                .attr("y1", d => d.source.y)
                .attr("x2", d => d.target.x)
                .attr("y2", d => d.target.y);
            
            node
                .attr("cx", d => d.x)
                .attr("cy", d => d.y);
            
            label
                .attr("x", d => d.x)
                .attr("y", d => d.y);
        }});
        
        function dragstarted(event, d) {{
            if (!event.active) simulation.alphaTarget(0.3).restart();
            d.fx = d.x; d.fy = d.y;
        }}
        
        function dragged(event, d) {{
            d.fx = event.x; d.fy = event.y;
        }}
        
        function dragended(event, d) {{
            if (!event.active) simulation.alphaTarget(0);
            d.fx = null; d.fy = null;
        }}
    </script>
</body>
</html>'''
        
        output_path.write_text(html_content, encoding='utf-8')
        return output_path
    
    def _generate_legend_html(self) -> str:
        """生成图例HTML"""
        lines = []
        for category, color in self.category_colors.items():
            lines.append(f'<div style="display:flex;align-items:center;margin:5px 0;">')
            lines.append(f'<span style="width:20px;height:20px;background:{color};margin-right:10px;border-radius:3px;"></span>')
            lines.append(f'<span>{category}</span></div>')
        return '\n'.join(lines)
    
    def _generate_mermaid_diagrams(self) -> List[str]:
        """生成Mermaid图表"""
        generated = []
        
        # 1. 概念依赖图
        mermaid_path = self.output_dir / "concept_dependencies.mmd"
        
        lines = ["```mermaid", "graph TD"]
        
        # 添加节点（按类别着色）
        for c in list(self.concepts.values())[:50]:  # 限制数量
            color = self.category_colors.get(c.category, "#FFFFFF")
            lines.append(f'    {c.id}["{c.name}"]')
            lines.append(f'    style {c.id} fill:{color}')
        
        # 添加边
        for rel in self.relations[:100]:
            if rel.source in self.concepts and rel.target in self.concepts:
                lines.append(f"    {rel.source} --> {rel.target}")
        
        lines.append("```")
        
        mermaid_path.write_text('\n'.join(lines), encoding='utf-8')
        generated.append(str(mermaid_path))
        
        # 2. 学习路径图
        learning_path_path = self.output_dir / "learning_paths.mmd"
        
        lines = ["```mermaid", "flowchart LR"]
        lines.append("    subgraph 基础阶段")
        lines.append("        A[集合论] --> B[数系]")
        lines.append("        B --> C[函数]")
        lines.append("    end")
        lines.append("    ")
        lines.append("    subgraph 代数方向")
        lines.append("        C --> D[群论]")
        lines.append("        D --> E[环论]")
        lines.append("        E --> F[域论]")
        lines.append("    end")
        lines.append("    ")
        lines.append("    subgraph 分析方向")
        lines.append("        C --> G[极限]")
        lines.append("        G --> H[微积分]")
        lines.append("        H --> I[实分析]")
        lines.append("        I --> J[泛函分析]")
        lines.append("    end")
        lines.append("```")
        
        learning_path_path.write_text('\n'.join(lines), encoding='utf-8')
        generated.append(str(learning_path_path))
        
        return generated
    
    def _generate_concept_docs(self) -> List[str]:
        """生成概念详细文档"""
        generated = []
        
        docs_dir = self.output_dir / "concepts"
        docs_dir.mkdir(exist_ok=True)
        
        # 生成概念总览
        overview_path = docs_dir / "overview.md"
        
        lines = [
            "# FormalMath 概念总览\n",
            f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n",
            f"**概念总数**: {len(self.concepts)}\n",
            f"**关系总数**: {len(self.relations)}\n\n"
        ]
        
        # 按类别分组
        by_category = defaultdict(list)
        for c in self.concepts.values():
            by_category[c.category].append(c)
        
        for category, concepts in sorted(by_category.items()):
            lines.append(f"## {category}\n\n")
            lines.append("| 概念 | 难度 | 学时 | MSC编码 |\n")
            lines.append("|------|------|------|---------|\n")
            
            for c in sorted(concepts, key=lambda x: x.difficulty):
                msc = c.msc_code or "-"
                lines.append(f"| {c.name} | {'⭐' * c.difficulty} | {c.estimated_hours}h | {msc} |\n")
            
            lines.append("\n")
        
        overview_path.write_text(''.join(lines), encoding='utf-8')
        generated.append(str(overview_path))
        
        return generated
    
    def _generate_statistics_report(self) -> Path:
        """生成统计报告"""
        output_path = self.output_dir / "statistics.md"
        
        # 统计
        total_hours = sum(c.estimated_hours for c in self.concepts.values())
        avg_difficulty = sum(c.difficulty for c in self.concepts.values()) / len(self.concepts) if self.concepts else 0
        
        by_category = defaultdict(int)
        by_difficulty = defaultdict(int)
        for c in self.concepts.values():
            by_category[c.category] += 1
            by_difficulty[c.difficulty] += 1
        
        lines = [
            "# FormalMath 概念统计报告\n\n",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日')}\n\n",
            "## 总体统计\n\n",
            f"- **概念总数**: {len(self.concepts)}\n",
            f"- **关系总数**: {len(self.relations)}\n",
            f"- **总学习时长**: {total_hours:.0f} 小时 ({total_hours/40:.1f} 周)\n",
            f"- **平均难度**: {avg_difficulty:.2f}/5\n\n",
            "## 按类别统计\n\n",
            "| 类别 | 概念数 | 占比 |\n",
            "|------|--------|------|\n"
        ]
        
        for cat, count in sorted(by_category.items(), key=lambda x: -x[1]):
            pct = count / len(self.concepts) * 100
            lines.append(f"| {cat} | {count} | {pct:.1f}% |\n")
        
        lines.extend(["\n", "## 按难度统计\n\n"])
        lines.append("| 难度等级 | 概念数 | 占比 |\n")
        lines.append("|----------|--------|------|\n")
        
        diff_names = {1: "初级", 2: "入门", 3: "中级", 4: "高级", 5: "专家"}
        for diff in sorted(by_difficulty.keys()):
            count = by_difficulty[diff]
            pct = count / len(self.concepts) * 100
            lines.append(f"| {diff} ({diff_names.get(diff, '未知')}) | {count} | {pct:.1f}% |\n")
        
        output_path.write_text(''.join(lines), encoding='utf-8')
        return output_path
    
    def _generate_learning_paths(self) -> Path:
        """生成学习路径文档"""
        output_path = self.output_dir / "learning_paths.md"
        
        content = f'''# FormalMath 推荐学习路径

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 路径一：代数方向

| 阶段 | 概念 | 难度 | 学时 |
|------|------|------|------|
| 基础 | 集合论 | ⭐ | 10h |
| 基础 | 数系构造 | ⭐⭐ | 15h |
| 初级 | 群论基础 | ⭐⭐ | 20h |
| 中级 | 环论与域论 | ⭐⭐⭐ | 25h |
| 高级 | 伽罗瓦理论 | ⭐⭐⭐⭐ | 30h |
| 专家 | 代数几何 | ⭐⭐⭐⭐⭐ | 50h |

**总学时**: 150小时 (约4周)

## 路径二：分析方向

| 阶段 | 概念 | 难度 | 学时 |
|------|------|------|------|
| 基础 | 实数理论 | ⭐ | 10h |
| 初级 | 极限与连续 | ⭐⭐ | 15h |
| 中级 | 微分学 | ⭐⭐⭐ | 20h |
| 中级 | 积分学 | ⭐⭐⭐ | 20h |
| 高级 | 实分析 | ⭐⭐⭐⭐ | 40h |
| 专家 | 泛函分析 | ⭐⭐⭐⭐⭐ | 50h |

**总学时**: 155小时 (约4周)

## 路径三：几何拓扑方向

| 阶段 | 概念 | 难度 | 学时 |
|------|------|------|------|
| 基础 | 欧氏几何 | ⭐ | 10h |
| 初级 | 点集拓扑 | ⭐⭐ | 15h |
| 中级 | 代数拓扑 | ⭐⭐⭐ | 30h |
| 高级 | 微分几何 | ⭐⭐⭐⭐ | 40h |
| 专家 | 代数几何 | ⭐⭐⭐⭐⭐ | 50h |

**总学时**: 145小时 (约3.5周)

---
*由 FormalMath 概念图谱生成器自动创建*
'''
        
        output_path.write_text(content, encoding='utf-8')
        return output_path


def main():
    """主函数"""
    generator = ConceptGraphGenerator(
        output_dir=Path("tools/doc-generator/output/concepts")
    )
    
    files = generator.generate_from_directory(Path("concept"))
    print(f"\n生成文件:")
    for f in files:
        print(f"  - {f}")


if __name__ == '__main__':
    main()
