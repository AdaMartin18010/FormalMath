"""
学习支持服务
提供资源推荐、学习伙伴匹配、难点预警、成就系统等功能
"""

from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from enum import Enum
import uuid

from models.knowledge_graph import KnowledgeGraph, ConceptNode
from models.learner import LearnerProfile, LearningStyle
from models.learning_path import LearningPath, PathNode


class ResourceType(Enum):
    """资源类型"""
    TEXT = "text"          # 文本
    VIDEO = "video"        # 视频
    AUDIO = "audio"        # 音频
    INTERACTIVE = "interactive"  # 交互式
    EXERCISE = "exercise"  # 练习
    PROJECT = "project"    # 项目


@dataclass
class LearningResource:
    """学习资源"""
    resource_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    title: str = ""
    description: str = ""
    resource_type: ResourceType = ResourceType.TEXT
    concept_id: str = ""
    difficulty: int = 1
    estimated_time: int = 30  # 预计学习时间（分钟）
    url: str = ""
    tags: List[str] = field(default_factory=list)
    
    # 资源质量指标
    rating: float = 4.0  # 评分 (1-5)
    view_count: int = 0  # 浏览次数
    completion_rate: float = 0.0  # 完成率
    
    # 适用学习风格
    suitable_styles: List[LearningStyle] = field(default_factory=list)


@dataclass
class Achievement:
    """成就"""
    achievement_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    description: str = ""
    icon: str = ""
    category: str = ""  # 成就类别
    
    # 解锁条件
    condition_type: str = ""  # 条件类型
    condition_value: Any = None  # 条件值
    
    # 奖励
    points: int = 0  # 积分
    badge_url: str = ""  # 徽章URL


class ResourceRecommendationService:
    """资源推荐服务"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph):
        self.knowledge_graph = knowledge_graph
        self.resources: Dict[str, LearningResource] = {}
        self._load_default_resources()
    
    def _load_default_resources(self):
        """加载默认资源"""
        # 集合概念资源
        self._add_resource(LearningResource(
            title="集合论基础 - 视频讲解",
            description="详细的集合论基础概念讲解",
            resource_type=ResourceType.VIDEO,
            concept_id="集合",
            difficulty=1,
            estimated_time=45,
            url="/resources/videos/set_theory_basics.mp4",
            suitable_styles=[LearningStyle.VISUAL, LearningStyle.AUDITORY],
            tags=["基础", "视频", "集合论"]
        ))
        
        self._add_resource(LearningResource(
            title="集合运算 - 交互式练习",
            description="通过交互式练习掌握集合运算",
            resource_type=ResourceType.INTERACTIVE,
            concept_id="集合",
            difficulty=1,
            estimated_time=30,
            url="/resources/interactive/set_operations.html",
            suitable_styles=[LearningStyle.KINESTHETIC, LearningStyle.VISUAL],
            tags=["交互式", "练习", "集合运算"]
        ))
        
        # 群论资源
        self._add_resource(LearningResource(
            title="群论导论 - 文档",
            description="群论基础概念的详细文档",
            resource_type=ResourceType.TEXT,
            concept_id="群",
            difficulty=2,
            estimated_time=120,
            url="/resources/docs/group_theory_intro.pdf",
            suitable_styles=[LearningStyle.READING],
            tags=["文档", "群论", "代数"]
        ))
        
        self._add_resource(LearningResource(
            title="群论可视化工具",
            description="可视化群的结构和运算",
            resource_type=ResourceType.INTERACTIVE,
            concept_id="群",
            difficulty=2,
            estimated_time=60,
            url="/resources/interactive/group_visualization.html",
            suitable_styles=[LearningStyle.VISUAL, LearningStyle.KINESTHETIC],
            tags=["可视化", "群论", "交互式"]
        ))
        
        # 拓扑学资源
        self._add_resource(LearningResource(
            title="拓扑空间入门",
            description="拓扑空间的概念和例子",
            resource_type=ResourceType.VIDEO,
            concept_id="拓扑空间",
            difficulty=3,
            estimated_time=90,
            url="/resources/videos/topology_intro.mp4",
            suitable_styles=[LearningStyle.VISUAL, LearningStyle.AUDITORY],
            tags=["拓扑", "视频", "进阶"]
        ))
        
        # 添加更多资源...
        self._add_resource(LearningResource(
            title="函数概念 - 音频课程",
            description="随时随地学习函数概念",
            resource_type=ResourceType.AUDIO,
            concept_id="函数",
            difficulty=1,
            estimated_time=40,
            url="/resources/audio/functions_podcast.mp3",
            suitable_styles=[LearningStyle.AUDITORY],
            tags=["音频", "函数", "基础"]
        ))
    
    def _add_resource(self, resource: LearningResource):
        """添加资源"""
        self.resources[resource.resource_id] = resource
    
    def recommend_resources(
        self,
        learner: LearnerProfile,
        concept_id: str,
        count: int = 3
    ) -> List[Dict[str, Any]]:
        """
        推荐学习资源
        
        Args:
            learner: 学习者画像
            concept_id: 概念ID
            count: 推荐数量
        
        Returns:
            推荐资源列表
        """
        # 过滤相关资源
        relevant = [
            r for r in self.resources.values()
            if r.concept_id == concept_id
        ]
        
        if not relevant:
            return []
        
        # 计算匹配分数
        scored_resources = []
        dominant_style = learner.learning_style.dominant_style
        
        for resource in relevant:
            score = 0.0
            
            # 学习风格匹配
            if dominant_style in resource.suitable_styles:
                score += 0.4
            
            # 难度适宜性
            learner_ability = learner.calculate_overall_ability()
            difficulty_diff = abs(resource.difficulty / 4 - learner_ability)
            score += (1 - difficulty_diff) * 0.3
            
            # 资源质量
            score += (resource.rating / 5) * 0.2
            
            # 完成率（倾向于推荐完成率适中的资源）
            if 0.3 <= resource.completion_rate <= 0.8:
                score += 0.1
            
            scored_resources.append((resource, score))
        
        # 排序并返回
        scored_resources.sort(key=lambda x: x[1], reverse=True)
        
        return [
            {
                "resource_id": r.resource_id,
                "title": r.title,
                "description": r.description,
                "type": r.resource_type.value,
                "difficulty": r.difficulty,
                "estimated_time": r.estimated_time,
                "url": r.url,
                "rating": r.rating,
                "score": round(score, 2)
            }
            for r, score in scored_resources[:count]
        ]
    
    def get_resources_by_style(
        self,
        style: LearningStyle,
        concept_id: Optional[str] = None
    ) -> List[LearningResource]:
        """根据学习风格获取资源"""
        resources = self.resources.values()
        
        if concept_id:
            resources = [r for r in resources if r.concept_id == concept_id]
        
        return [r for r in resources if style in r.suitable_styles]
    
    def search_resources(
        self,
        query: str,
        concept_id: Optional[str] = None,
        resource_type: Optional[ResourceType] = None
    ) -> List[LearningResource]:
        """搜索资源"""
        results = []
        query_lower = query.lower()
        
        for resource in self.resources.values():
            if concept_id and resource.concept_id != concept_id:
                continue
            if resource_type and resource.resource_type != resource_type:
                continue
            
            if (query_lower in resource.title.lower() or
                query_lower in resource.description.lower() or
                any(query_lower in tag.lower() for tag in resource.tags)):
                results.append(resource)
        
        return results


class PeerMatchingService:
    """学习伙伴匹配服务"""
    
    def __init__(self):
        self.active_learners: Dict[str, Dict[str, Any]] = {}
    
    def register_learner(
        self,
        learner_id: str,
        current_concepts: List[str],
        learning_style: LearningStyle,
        skill_level: float,
        available_times: List[str]
    ):
        """注册学习者"""
        self.active_learners[learner_id] = {
            "learner_id": learner_id,
            "current_concepts": current_concepts,
            "learning_style": learning_style,
            "skill_level": skill_level,
            "available_times": available_times,
            "last_active": datetime.now()
        }
    
    def find_peers(
        self,
        learner_id: str,
        max_results: int = 5
    ) -> List[Dict[str, Any]]:
        """
        寻找学习伙伴
        
        匹配算法考虑：
        - 学习相同或相似概念
        - 学习风格互补
        - 能力水平相近
        - 时间可用性重叠
        """
        if learner_id not in self.active_learners:
            return []
        
        learner = self.active_learners[learner_id]
        matches = []
        
        for other_id, other in self.active_learners.items():
            if other_id == learner_id:
                continue
            
            score = 0.0
            reasons = []
            
            # 概念重叠（30%）
            concept_overlap = set(learner["current_concepts"]) & set(other["current_concepts"])
            if concept_overlap:
                overlap_ratio = len(concept_overlap) / max(len(learner["current_concepts"]), 1)
                score += overlap_ratio * 0.3
                reasons.append(f"共同学习概念: {', '.join(list(concept_overlap)[:2])}")
            
            # 学习风格互补（20%）
            if learner["learning_style"] != other["learning_style"]:
                score += 0.2
                reasons.append("学习风格互补")
            
            # 能力水平相近（30%）
            skill_diff = abs(learner["skill_level"] - other["skill_level"])
            if skill_diff < 0.3:
                score += 0.3
                reasons.append("能力水平相近")
            
            # 时间可用性（20%）
            time_overlap = set(learner["available_times"]) & set(other["available_times"])
            if time_overlap:
                score += 0.2
                reasons.append("时间可用性匹配")
            
            if score > 0.3:  # 最小匹配阈值
                matches.append({
                    "learner_id": other_id,
                    "match_score": round(score, 2),
                    "reasons": reasons,
                    "common_concepts": list(concept_overlap)[:3]
                })
        
        # 排序并返回
        matches.sort(key=lambda x: x["match_score"], reverse=True)
        return matches[:max_results]
    
    def form_study_group(
        self,
        concept_id: str,
        max_members: int = 4
    ) -> Optional[Dict[str, Any]]:
        """组建学习小组"""
        # 查找学习相同概念的学习者
        candidates = [
            lid for lid, info in self.active_learners.items()
            if concept_id in info["current_concepts"]
        ]
        
        if len(candidates) < 2:
            return None
        
        # 选择能力水平相近的
        candidates_sorted = sorted(
            candidates,
            key=lambda lid: self.active_learners[lid]["skill_level"]
        )
        
        selected = candidates_sorted[:max_members]
        
        return {
            "group_id": str(uuid.uuid4()),
            "concept_id": concept_id,
            "members": selected,
            "formed_at": datetime.now().isoformat()
        }
    
    def remove_inactive_learners(self, max_inactive_hours: int = 24):
        """移除不活跃的学习者"""
        cutoff = datetime.now() - timedelta(hours=max_inactive_hours)
        inactive = [
            lid for lid, info in self.active_learners.items()
            if info["last_active"] < cutoff
        ]
        for lid in inactive:
            del self.active_learners[lid]


class DifficultyWarningService:
    """难点预警服务"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph):
        self.knowledge_graph = knowledge_graph
        self.warning_history: List[Dict[str, Any]] = []
    
    def analyze_concept_difficulty(
        self,
        concept_id: str,
        learner: LearnerProfile
    ) -> Dict[str, Any]:
        """
        分析概念难度并生成预警
        
        Returns:
            预警信息
        """
        warnings = []
        
        concept = self.knowledge_graph.get_node(concept_id)
        if not concept:
            return {"warnings": []}
        
        # 1. 检查先修知识
        prereqs = self.knowledge_graph.get_prerequisites(concept_id)
        unmastered_prereqs = [
            p for p in prereqs
            if not learner.is_concept_mastered(p)
        ]
        
        if unmastered_prereqs:
            warnings.append({
                "type": "prerequisite_gap",
                "severity": "high",
                "message": f"缺少先修知识: {', '.join(unmastered_prereqs[:3])}",
                "missing_prerequisites": unmastered_prereqs,
                "recommendation": "建议先学习先修概念"
            })
        
        # 2. 检查概念复杂度
        complexity = self.knowledge_graph.calculate_complexity(concept_id)
        learner_ability = learner.calculate_overall_ability()
        
        if complexity > learner_ability + 0.3:
            warnings.append({
                "type": "high_complexity",
                "severity": "medium",
                "message": "该概念较为复杂，可能需要更多时间和支持",
                "complexity": complexity,
                "recommendation": "建议增加学习时间，使用更多辅助资源"
            })
        
        # 3. 检查难度跳跃
        if learner.learning_history:
            last_concept = learner.learning_history[-1].get("concept_id", "")
            if last_concept:
                last_node = self.knowledge_graph.get_node(last_concept)
                if last_node and concept.difficulty.value > last_node.difficulty.value + 1:
                    warnings.append({
                        "type": "difficulty_jump",
                        "severity": "medium",
                        "message": "难度跳跃较大，可能需要过渡内容",
                        "recommendation": "建议添加难度过渡概念"
                    })
        
        # 4. 检查学习时间
        weekly_hours = learner.get_weekly_study_hours()
        estimated_time = concept.estimated_time_minutes / 60
        
        if estimated_time > weekly_hours * 0.5:
            warnings.append({
                "type": "time_intensive",
                "severity": "low",
                "message": "该概念需要较多时间，建议分多次学习",
                "estimated_hours": estimated_time,
                "recommendation": "将学习内容分成多个小节"
            })
        
        warning_record = {
            "concept_id": concept_id,
            "learner_id": learner.learner_id,
            "warnings": warnings,
            "timestamp": datetime.now().isoformat()
        }
        self.warning_history.append(warning_record)
        
        return warning_record
    
    def get_warning_statistics(self, learner_id: Optional[str] = None) -> Dict[str, Any]:
        """获取预警统计"""
        history = self.warning_history
        if learner_id:
            history = [h for h in history if h.get("learner_id") == learner_id]
        
        warning_counts = {}
        for record in history:
            for warning in record.get("warnings", []):
                wtype = warning["type"]
                warning_counts[wtype] = warning_counts.get(wtype, 0) + 1
        
        return {
            "total_warnings": sum(len(h.get("warnings", [])) for h in history),
            "warning_types": warning_counts,
            "concepts_with_warnings": len(set(h.get("concept_id") for h in history))
        }


class AchievementSystem:
    """成就系统"""
    
    def __init__(self):
        self.achievements: Dict[str, Achievement] = {}
        self.learner_achievements: Dict[str, List[str]] = {}  # learner_id -> achievement_ids
        self._load_default_achievements()
    
    def _load_default_achievements(self):
        """加载默认成就"""
        default_achievements = [
            Achievement(
                name="初次启程",
                description="开始学习第一条学习路径",
                icon="🚀",
                category="milestone",
                condition_type="path_started",
                condition_value=1,
                points=10
            ),
            Achievement(
                name="初学者",
                description="完成第一个概念的学习",
                icon="🌱",
                category="learning",
                condition_type="concepts_completed",
                condition_value=1,
                points=20
            ),
            Achievement(
                name="探索者",
                description="完成10个概念的学习",
                icon="🔍",
                category="learning",
                condition_type="concepts_completed",
                condition_value=10,
                points=50
            ),
            Achievement(
                name="坚持者",
                description="连续学习7天",
                icon="📅",
                category="consistency",
                condition_type="streak_days",
                condition_value=7,
                points=30
            ),
            Achievement(
                name="勤奋学者",
                description="累计学习50小时",
                icon="📚",
                category="dedication",
                condition_type="total_hours",
                condition_value=50,
                points=100
            ),
            Achievement(
                name="完美掌握",
                description="5个概念的掌握度达到90%以上",
                icon="⭐",
                category="mastery",
                condition_type="high_mastery_count",
                condition_value=5,
                points=75
            ),
            Achievement(
                name="路径完成者",
                description="完成第一条完整的学习路径",
                icon="🏆",
                category="milestone",
                condition_type="path_completed",
                condition_value=1,
                points=100
            ),
            Achievement(
                name="社交学习者",
                description="首次与学习伙伴互动",
                icon="🤝",
                category="social",
                condition_type="peer_interaction",
                condition_value=1,
                points=25
            )
        ]
        
        for achievement in default_achievements:
            achievement.achievement_id = str(uuid.uuid4())
            self.achievements[achievement.achievement_id] = achievement
    
    def check_achievements(self, learner_id: str, stats: Dict[str, Any]) -> List[Achievement]:
        """
        检查并解锁成就
        
        Args:
            learner_id: 学习者ID
            stats: 学习统计数据
        
        Returns:
            新解锁的成就列表
        """
        unlocked = []
        existing = self.learner_achievements.get(learner_id, [])
        
        for achievement_id, achievement in self.achievements.items():
            if achievement_id in existing:
                continue
            
            # 检查条件
            condition_met = False
            condition_type = achievement.condition_type
            condition_value = achievement.condition_value
            
            if condition_type == "concepts_completed":
                condition_met = stats.get("concepts_completed", 0) >= condition_value
            elif condition_type == "streak_days":
                condition_met = stats.get("current_streak", 0) >= condition_value
            elif condition_type == "total_hours":
                condition_met = stats.get("total_hours", 0) >= condition_value
            elif condition_type == "high_mastery_count":
                condition_met = stats.get("high_mastery_count", 0) >= condition_value
            elif condition_type == "path_started":
                condition_met = stats.get("paths_started", 0) >= condition_value
            elif condition_type == "path_completed":
                condition_met = stats.get("paths_completed", 0) >= condition_value
            elif condition_type == "peer_interaction":
                condition_met = stats.get("peer_interactions", 0) >= condition_value
            
            if condition_met:
                unlocked.append(achievement)
                existing.append(achievement_id)
        
        self.learner_achievements[learner_id] = existing
        return unlocked
    
    def get_learner_achievements(self, learner_id: str) -> Dict[str, Any]:
        """获取学习者的成就信息"""
        achievement_ids = self.learner_achievements.get(learner_id, [])
        unlocked = [self.achievements[aid] for aid in achievement_ids if aid in self.achievements]
        
        total_points = sum(a.points for a in unlocked)
        
        return {
            "total_achievements": len(unlocked),
            "total_points": total_points,
            "achievements": [
                {
                    "id": a.achievement_id,
                    "name": a.name,
                    "description": a.description,
                    "icon": a.icon,
                    "category": a.category,
                    "points": a.points
                }
                for a in unlocked
            ],
            "available_achievements": len(self.achievements) - len(unlocked)
        }
    
    def get_leaderboard(self, top_n: int = 10) -> List[Dict[str, Any]]:
        """获取成就排行榜"""
        scores = []
        for learner_id, achievement_ids in self.learner_achievements.items():
            total_points = sum(
                self.achievements[aid].points
                for aid in achievement_ids if aid in self.achievements
            )
            scores.append({
                "learner_id": learner_id,
                "total_points": total_points,
                "achievement_count": len(achievement_ids)
            })
        
        scores.sort(key=lambda x: x["total_points"], reverse=True)
        return scores[:top_n]
