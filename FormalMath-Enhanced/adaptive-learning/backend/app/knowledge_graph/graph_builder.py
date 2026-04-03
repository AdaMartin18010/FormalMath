"""
知识图谱构建模块
基于 project/links/cross-branch-links.yaml 构建知识图谱
"""
import yaml
import networkx as nx
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional, Any
import os

from ..schemas import ConceptNode, ConceptRelation, ConceptRelationType, DifficultyLevel
from ..core.config import settings


class KnowledgeGraph:
    """知识图谱类 - 使用 NetworkX 实现"""
    
    def __init__(self):
        self.graph = nx.DiGraph()
        self.concepts: Dict[str, ConceptNode] = {}
        self.relations: List[ConceptRelation] = []
        self._initialized = False
    
    def build_from_yaml(self, yaml_path: Optional[str] = None) -> bool:
        """
        从 YAML 文件构建知识图谱
        
        Args:
            yaml_path: YAML 文件路径，默认为配置中的路径
            
        Returns:
            是否成功构建
        """
        if yaml_path is None:
            yaml_path = os.path.join(
                Path(__file__).parent.parent.parent.parent.parent.parent,
                "project", "links", "cross-branch-links.yaml"
            )
        
        try:
            with open(yaml_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
            
            links = data.get('links', [])
            
            # 解析链接构建图
            for link in links:
                self._process_link(link)
            
            # 拓扑排序确保先修关系正确
            self._validate_prerequisites()
            
            self._initialized = True
            print(f"知识图谱构建完成: {len(self.concepts)} 个概念, {len(self.relations)} 个关系")
            return True
            
        except Exception as e:
            print(f"构建知识图谱失败: {e}")
            return False
    
    def _process_link(self, link: Dict[str, Any]):
        """处理单个链接"""
        source_path = link.get('source', '')
        target_path = link.get('target', '')
        link_type = link.get('type', '相关')
        description = link.get('description', '')
        branch_pair = link.get('branch_pair', '')
        
        # 从路径提取概念信息
        source_concept = self._extract_concept_from_path(source_path)
        target_concept = self._extract_concept_from_path(target_path)
        
        if not source_concept or not target_concept:
            return
        
        # 添加概念节点
        for concept in [source_concept, target_concept]:
            if concept.id not in self.concepts:
                self.concepts[concept.id] = concept
                self.graph.add_node(
                    concept.id,
                    name=concept.name,
                    branch=concept.branch,
                    difficulty=concept.difficulty.value
                )
        
        # 添加关系
        relation_type = self._map_relation_type(link_type)
        relation = ConceptRelation(
            source=source_concept.id,
            target=target_concept.id,
            type=relation_type,
            description=description
        )
        self.relations.append(relation)
        
        # 更新概念的关联关系
        if relation_type == ConceptRelationType.PREREQUISITE:
            if target_concept.id not in self.concepts[source_concept.id].successors:
                self.concepts[source_concept.id].successors.append(target_concept.id)
            if source_concept.id not in self.concepts[target_concept.id].prerequisites:
                self.concepts[target_concept.id].prerequisites.append(source_concept.id)
            self.graph.add_edge(source_concept.id, target_concept.id, 
                              relation='prerequisite', weight=1.0)
                              
        elif relation_type == ConceptRelationType.SUCCESSOR:
            if source_concept.id not in self.concepts[target_concept.id].successors:
                self.concepts[target_concept.id].successors.append(source_concept.id)
            if target_concept.id not in self.concepts[source_concept.id].prerequisites:
                self.concepts[source_concept.id].prerequisites.append(target_concept.id)
            self.graph.add_edge(target_concept.id, source_concept.id,
                              relation='prerequisite', weight=1.0)
                              
        else:
            # 相关关系
            if target_concept.id not in self.concepts[source_concept.id].related:
                self.concepts[source_concept.id].related.append(target_concept.id)
            if source_concept.id not in self.concepts[target_concept.id].related:
                self.concepts[target_concept.id].related.append(source_concept.id)
            self.graph.add_edge(source_concept.id, target_concept.id,
                              relation='related', weight=0.5)
    
    def _extract_concept_from_path(self, path: str) -> Optional[ConceptNode]:
        """从文件路径提取概念信息"""
        if not path:
            return None
        
        # 解析路径获取概念名称
        parts = path.replace('\\', '/').split('/')
        
        # 从文件名提取概念名称
        filename = parts[-1] if parts else ""
        
        # 移除扩展名和数字前缀
        name = filename
        if '.' in name:
            name = name.rsplit('.', 1)[0]
        
        # 处理数字前缀如 "01-", "08-"
        if '-' in name and name.split('-')[0].isdigit():
            name = '-'.join(name.split('-')[1:])
        
        # 移除 "-五种表征" 等后缀
        if '-五种表征' in name:
            name = name.replace('-五种表征', '')
        
        # 从路径确定分支
        branch = self._determine_branch(path)
        
        # 生成概念ID
        concept_id = f"{branch}_{name.lower().replace(' ', '_')}"
        
        return ConceptNode(
            id=concept_id,
            name=name.replace('-', ' ').replace('_', ' '),
            branch=branch,
            difficulty=self._estimate_difficulty(path),
            metadata={'source_path': path}
        )
    
    def _determine_branch(self, path: str) -> str:
        """根据路径确定数学分支"""
        path_lower = path.lower()
        
        if '代数' in path or 'algebra' in path_lower:
            return '代数'
        elif '分析' in path or 'analysis' in path_lower:
            return '分析'
        elif '拓扑' in path or 'topology' in path_lower:
            return '拓扑'
        elif '几何' in path or 'geometry' in path_lower:
            return '几何'
        elif '数论' in path or 'number' in path_lower:
            return '数论'
        elif '逻辑' in path or 'logic' in path_lower:
            return '逻辑'
        elif '概率' in path or 'probability' in path_lower:
            return '概率论'
        elif '组合' in path or 'combinatorics' in path_lower:
            return '组合数学'
        else:
            return '基础数学'
    
    def _estimate_difficulty(self, path: str) -> DifficultyLevel:
        """估计概念难度"""
        path_lower = path.lower()
        
        # 根据路径关键词估计难度
        expert_keywords = ['高级', '前沿', '现代', 'advanced', 'modern', 'frontier']
        advanced_keywords = ['深化', '扩展', 'enhanced', 'extended']
        beginner_keywords = ['基础', '入门', 'basic', 'introduction']
        
        for kw in expert_keywords:
            if kw in path_lower:
                return DifficultyLevel.EXPERT
        
        for kw in advanced_keywords:
            if kw in path_lower:
                return DifficultyLevel.ADVANCED
                
        for kw in beginner_keywords:
            if kw in path_lower:
                return DifficultyLevel.BEGINNER
        
        return DifficultyLevel.INTERMEDIATE
    
    def _map_relation_type(self, link_type: str) -> ConceptRelationType:
        """映射关系类型"""
        mapping = {
            '先修': ConceptRelationType.PREREQUISITE,
            '后继': ConceptRelationType.SUCCESSOR,
            '相关': ConceptRelationType.RELATED,
            '交叉': ConceptRelationType.CROSS,
            '应用': ConceptRelationType.APPLICATION,
            '推广': ConceptRelationType.EXTENSION,
        }
        return mapping.get(link_type, ConceptRelationType.RELATED)
    
    def _validate_prerequisites(self):
        """验证并修复先修关系"""
        # 确保没有循环依赖
        try:
            list(nx.topological_sort(self.graph))
        except nx.NetworkXUnfeasible:
            # 有循环，移除权重最小的边
            cycles = list(nx.simple_cycles(self.graph))
            for cycle in cycles:
                # 找到循环中权重最小的边
                min_weight = float('inf')
                edge_to_remove = None
                for i in range(len(cycle)):
                    u, v = cycle[i], cycle[(i+1) % len(cycle)]
                    weight = self.graph[u][v].get('weight', 1)
                    if weight < min_weight:
                        min_weight = weight
                        edge_to_remove = (u, v)
                if edge_to_remove:
                    self.graph.remove_edge(*edge_to_remove)
    
    # ========== 查询方法 ==========
    
    def get_concept(self, concept_id: str) -> Optional[ConceptNode]:
        """获取概念节点"""
        return self.concepts.get(concept_id)
    
    def get_all_concepts(self) -> List[ConceptNode]:
        """获取所有概念"""
        return list(self.concepts.values())
    
    def get_prerequisites(self, concept_id: str, recursive: bool = False) -> List[str]:
        """
        获取概念的先修概念
        
        Args:
            concept_id: 概念ID
            recursive: 是否递归获取所有先修
        """
        if concept_id not in self.concepts:
            return []
        
        if not recursive:
            return self.concepts[concept_id].prerequisites
        
        # 递归获取所有先修
        all_prereqs = set()
        queue = list(self.concepts[concept_id].prerequisites)
        
        while queue:
            prereq = queue.pop(0)
            if prereq not in all_prereqs:
                all_prereqs.add(prereq)
                if prereq in self.concepts:
                    queue.extend(self.concepts[prereq].prerequisites)
        
        return list(all_prereqs)
    
    def get_successors(self, concept_id: str) -> List[str]:
        """获取概念的后继概念"""
        if concept_id not in self.concepts:
            return []
        return self.concepts[concept_id].successors
    
    def get_related_concepts(self, concept_id: str) -> List[str]:
        """获取相关概念"""
        if concept_id not in self.concepts:
            return []
        return self.concepts[concept_id].related
    
    def find_path(self, start: str, end: str) -> List[str]:
        """
        查找两个概念之间的学习路径
        
        Returns:
            概念ID列表，如果无路径则返回空列表
        """
        try:
            return nx.shortest_path(self.graph, start, end, weight='weight')
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            return []
    
    def get_learning_sequence(self, target_concepts: List[str]) -> List[str]:
        """
        获取目标概念的学习序列（拓扑排序）
        
        Args:
            target_concepts: 目标概念列表
            
        Returns:
            按学习顺序排列的概念ID列表
        """
        # 收集所有需要的概念（包括先修）
        all_concepts = set()
        for concept_id in target_concepts:
            all_concepts.add(concept_id)
            all_concepts.update(self.get_prerequisites(concept_id, recursive=True))
        
        # 构建子图
        subgraph = self.graph.subgraph(all_concepts)
        
        try:
            # 拓扑排序
            return list(nx.topological_sort(subgraph))
        except nx.NetworkXUnfeasible:
            # 有循环，使用简单排序
            return list(all_concepts)
    
    def calculate_complexity(self, concept_id: str) -> float:
        """
        计算概念复杂度
        
        基于先修概念数量和难度计算
        """
        if concept_id not in self.concepts:
            return 0.0
        
        prereqs = self.get_prerequisites(concept_id, recursive=True)
        
        # 基础复杂度
        complexity = len(prereqs) * 0.1
        
        # 难度权重
        difficulty_weights = {
            DifficultyLevel.BEGINNER: 0.5,
            DifficultyLevel.INTERMEDIATE: 1.0,
            DifficultyLevel.ADVANCED: 1.5,
            DifficultyLevel.EXPERT: 2.0
        }
        
        concept = self.concepts[concept_id]
        complexity += difficulty_weights.get(concept.difficulty, 1.0)
        
        return min(complexity, 10.0)
    
    def get_branch_concepts(self, branch: str) -> List[ConceptNode]:
        """获取指定分支的所有概念"""
        return [c for c in self.concepts.values() if c.branch == branch]
    
    def search_concepts(self, query: str) -> List[ConceptNode]:
        """搜索概念"""
        query_lower = query.lower()
        results = []
        
        for concept in self.concepts.values():
            if (query_lower in concept.name.lower() or 
                query_lower in concept.description.lower()):
                results.append(concept)
        
        return results


# 全局知识图谱实例
knowledge_graph = KnowledgeGraph()


def get_knowledge_graph() -> KnowledgeGraph:
    """获取知识图谱实例（懒加载）"""
    if not knowledge_graph._initialized:
        knowledge_graph.build_from_yaml()
    return knowledge_graph
