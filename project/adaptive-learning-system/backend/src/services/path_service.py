"""
学习路径服务
提供路径生成、路径管理、路径调整等功能
"""

from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
import json
import os

from models.knowledge_graph import KnowledgeGraph, ConceptNode, RelationEdge
from models.learner import LearnerProfile
from models.learning_path import (
    LearningPath, PathNode, PathStatus, PathRecommendation,
    PathConstraints, PathAdjustment, LearningSchedule, PathMetrics
)
from algorithms.path_generation import (
    AStarPathPlanner, KnowledgeGapAnalyzer, MultiObjectiveOptimizer,
    PathScorer
)
from algorithms.adaptive_engine import (
    RealTimeMonitor, PathAdjustmentEngine, SpacedRepetitionScheduler,
    LearningProgress
)


class PathService:
    """学习路径服务"""
    
    def __init__(
        self,
        knowledge_graph: KnowledgeGraph,
        data_dir: str = "data/learning_paths"
    ):
        self.knowledge_graph = knowledge_graph
        self.data_dir = data_dir
        self.paths: Dict[str, LearningPath] = {}
        self.schedules: Dict[str, LearningSchedule] = {}
        self._ensure_data_dir()
        self._load_paths()
    
    def _ensure_data_dir(self):
        """确保数据目录存在"""
        os.makedirs(self.data_dir, exist_ok=True)
    
    def _load_paths(self):
        """加载学习路径"""
        if not os.path.exists(self.data_dir):
            return
        
        for filename in os.listdir(self.data_dir):
            if filename.endswith('.json'):
                filepath = os.path.join(self.data_dir, filename)
                try:
                    with open(filepath, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                        path = self._dict_to_path(data)
                        self.paths[path.path_id] = path
                except Exception as e:
                    print(f"Error loading path from {filename}: {e}")
    
    def _save_path(self, path: LearningPath):
        """保存学习路径"""
        filepath = os.path.join(self.data_dir, f"{path.path_id}.json")
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(self._path_to_dict(path), f, ensure_ascii=False, indent=2)
    
    def _path_to_dict(self, path: LearningPath) -> Dict[str, Any]:
        """将路径对象转换为字典"""
        return {
            "path_id": path.path_id,
            "learner_id": path.learner_id,
            "name": path.name,
            "description": path.description,
            "goal": path.goal,
            "status": path.status.value,
            "nodes": {
                node_id: {
                    "node_id": node.node_id,
                    "concept_id": node.concept_id,
                    "sequence_number": node.sequence_number,
                    "status": node.status.value,
                    "estimated_duration": node.estimated_duration,
                    "completion_percentage": node.completion_percentage,
                    "mastery_level": node.mastery_level,
                    "difficulty": node.difficulty,
                    "importance": node.importance
                }
                for node_id, node in path.nodes.items()
            },
            "node_order": path.node_order,
            "total_estimated_hours": path.total_estimated_hours,
            "difficulty_curve": path.difficulty_curve,
            "diversity_score": path.diversity_score,
            "algorithm_used": path.algorithm_used,
            "constraints": path.constraints,
            "created_at": path.created_at.isoformat(),
            "started_at": path.started_at.isoformat() if path.started_at else None,
            "target_completion": path.target_completion.isoformat() if path.target_completion else None,
            "completed_at": path.completed_at.isoformat() if path.completed_at else None
        }
    
    def _dict_to_path(self, data: Dict[str, Any]) -> LearningPath:
        """将字典转换为路径对象"""
        path = LearningPath(
            path_id=data.get("path_id", ""),
            learner_id=data.get("learner_id", ""),
            name=data.get("name", ""),
            description=data.get("description", ""),
            goal=data.get("goal", ""),
            algorithm_used=data.get("algorithm_used", ""),
            constraints=data.get("constraints", {}),
            total_estimated_hours=data.get("total_estimated_hours", 0),
            difficulty_curve=data.get("difficulty_curve", []),
            diversity_score=data.get("diversity_score", 0)
        )
        
        # 恢复状态
        if "status" in data:
            path.status = PathStatus(data["status"])
        
        # 恢复节点
        if "nodes" in data:
            for node_id, node_data in data["nodes"].items():
                node = PathNode(
                    node_id=node_data.get("node_id", ""),
                    concept_id=node_data.get("concept_id", ""),
                    sequence_number=node_data.get("sequence_number", 0),
                    estimated_duration=node_data.get("estimated_duration", 60),
                    completion_percentage=node_data.get("completion_percentage", 0),
                    mastery_level=node_data.get("mastery_level", 0),
                    difficulty=node_data.get("difficulty", 1),
                    importance=node_data.get("importance", 1)
                )
                if "status" in node_data:
                    node.status = PathStatus(node_data["status"])
                path.nodes[node_id] = node
        
        path.node_order = data.get("node_order", [])
        
        # 恢复时间戳
        if "created_at" in data:
            path.created_at = datetime.fromisoformat(data["created_at"])
        if data.get("started_at"):
            path.started_at = datetime.fromisoformat(data["started_at"])
        if data.get("target_completion"):
            path.target_completion = datetime.fromisoformat(data["target_completion"])
        if data.get("completed_at"):
            path.completed_at = datetime.fromisoformat(data["completed_at"])
        
        return path
    
    def generate_path(
        self,
        learner: LearnerProfile,
        goal_concepts: List[str],
        constraints: Optional[PathConstraints] = None
    ) -> PathRecommendation:
        """
        生成学习路径
        
        Args:
            learner: 学习者画像
            goal_concepts: 目标概念列表
            constraints: 路径约束条件
        
        Returns:
            PathRecommendation: 路径推荐结果
        """
        if constraints is None:
            constraints = PathConstraints(
                max_total_time_hours=learner.get_weekly_study_hours() * 4,  # 4周
                learning_style_weight=0.3,
                diversity_weight=0.2
            )
        
        # 创建路径规划器
        planner = AStarPathPlanner(self.knowledge_graph, learner)
        
        # 生成多条路径
        candidate_paths = planner.find_multiple_paths(
            start_concepts=list(learner.knowledge_state.keys()),
            goal_concepts=goal_concepts,
            constraints=constraints,
            num_paths=3
        )
        
        # 多目标优化
        optimizer = MultiObjectiveOptimizer(self.knowledge_graph)
        scored_paths = optimizer.optimize(
            candidate_paths,
            objectives={
                "time": 0.3,
                "depth": 0.2,
                "breadth": 0.2,
                "smoothness": 0.3
            }
        )
        
        # 创建推荐结果
        recommendation = PathRecommendation(
            learner_id=learner.learner_id
        )
        
        scorer = PathScorer(learner, constraints)
        
        for path, score in scored_paths:
            recommendation.paths.append(path)
            recommendation.match_scores[path.path_id] = score
            
            # 生成推荐理由
            reasons = []
            if path.diversity_score > 0.7:
                reasons.append("学习内容多样")
            if path.total_estimated_hours <= constraints.max_total_time_hours * 0.8:
                reasons.append("时间效率高")
            if scorer._calculate_smoothness(path) > 0.8:
                reasons.append("难度递进合理")
            
            recommendation.reasons[path.path_id] = "；".join(reasons) if reasons else "综合推荐"
        
        # 保存路径
        for path in recommendation.paths:
            self.paths[path.path_id] = path
            self._save_path(path)
        
        return recommendation
    
    def analyze_knowledge_gaps(
        self,
        learner: LearnerProfile,
        goal_concepts: List[str]
    ) -> Dict[str, Any]:
        """分析知识缺口"""
        analyzer = KnowledgeGapAnalyzer(self.knowledge_graph, learner)
        gaps = analyzer.analyze_gaps(goal_concepts)
        prioritized = analyzer.prioritize_gaps(gaps)
        
        return {
            "gaps": gaps,
            "prioritized": prioritized,
            "total_gaps": len(gaps["knowledge_gaps"]),
            "estimated_time_hours": gaps["estimated_study_time"]
        }
    
    def get_path(self, path_id: str) -> Optional[LearningPath]:
        """获取学习路径"""
        return self.paths.get(path_id)
    
    def start_path(self, path_id: str) -> Optional[LearningPath]:
        """开始学习路径"""
        path = self.paths.get(path_id)
        if not path:
            return None
        
        path.status = PathStatus.ACTIVE
        path.started_at = datetime.now()
        
        # 解锁第一个节点
        if path.node_order:
            first_node = path.nodes[path.node_order[0]]
            first_node.status = PathStatus.ACTIVE
        
        self._save_path(path)
        return path
    
    def update_progress(
        self,
        path_id: str,
        node_id: str,
        progress: float,
        mastery: float
    ) -> Optional[LearningPath]:
        """更新学习进度"""
        path = self.paths.get(path_id)
        if not path:
            return None
        
        path.update_progress(node_id, progress, mastery)
        
        # 检查是否完成
        if len(path.get_completed_nodes()) == len(path.nodes):
            path.status = PathStatus.COMPLETED
            path.completed_at = datetime.now()
        
        self._save_path(path)
        return path
    
    def adjust_path(
        self,
        path_id: str,
        adjustment_type: str = "auto",
        feedback: Optional[Dict[str, Any]] = None
    ) -> Optional[PathAdjustment]:
        """调整学习路径"""
        path = self.paths.get(path_id)
        if not path:
            return None
        
        learner = None  # 需要从外部传入
        engine = PathAdjustmentEngine(path, learner)
        
        if adjustment_type == "optimize":
            adjustment = engine.optimize_path_for_remaining()
        else:
            progress = LearningProgress(path_id=path_id)
            adjustment = engine.adjust_based_on_feedback(progress)
        
        if adjustment:
            self._save_path(path)
        
        return adjustment
    
    def create_schedule(
        self,
        path_id: str,
        learner: LearnerProfile,
        start_date: Optional[datetime] = None
    ) -> Optional[LearningSchedule]:
        """创建学习计划"""
        path = self.paths.get(path_id)
        if not path:
            return None
        
        schedule = LearningSchedule(
            path_id=path_id,
            learner_id=learner.learner_id
        )
        
        daily_hours = learner.time_availability.daily_available_hours
        schedule.create_schedule(path, daily_hours, start_date)
        
        # 添加复习提醒
        for node_id in path.get_completed_nodes():
            node = path.nodes[node_id]
            if node.actual_end:
                schedule.add_review_reminder(node_id, node.actual_end, node.mastery_level)
        
        self.schedules[schedule.schedule_id] = schedule
        
        return schedule
    
    def get_path_statistics(self, path_id: str) -> Optional[Dict[str, Any]]:
        """获取路径统计信息"""
        path = self.paths.get(path_id)
        if not path:
            return None
        
        metrics = PathMetrics()
        
        return {
            "path_id": path_id,
            "status": path.status.value,
            "overall_progress": path.calculate_overall_progress(),
            "total_nodes": len(path.nodes),
            "completed_nodes": len(path.get_completed_nodes()),
            "remaining_hours": path.get_remaining_time(),
            "smoothness": metrics.calculate_smoothness(path),
            "difficulty_curve": path.difficulty_curve,
            "diversity_score": path.diversity_score
        }
    
    def list_paths(self, learner_id: Optional[str] = None) -> List[Dict[str, Any]]:
        """列出学习路径"""
        paths = self.paths.values()
        if learner_id:
            paths = [p for p in paths if p.learner_id == learner_id]
        
        return [p.to_dict() for p in paths]
    
    def delete_path(self, path_id: str) -> bool:
        """删除学习路径"""
        if path_id in self.paths:
            del self.paths[path_id]
            filepath = os.path.join(self.data_dir, f"{path_id}.json")
            if os.path.exists(filepath):
                os.remove(filepath)
            return True
        return False
