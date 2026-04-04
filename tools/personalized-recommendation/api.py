"""
个性化学习路径推荐系统 - API接口

提供RESTful API接口，支持：
1. 用户画像管理
2. 学习路径推荐
3. 进度追踪
4. 可视化导出
"""

from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
import json
import uuid

from user_profile import (
    UserProfile, LearningGoal, ConceptMastery, LearningStyle,
    LearningPreference, TimePreference, LearningGoalPriority,
    create_preset_profile, USER_PROFILE_QUESTIONS
)
from recommendation_engine import (
    RecommendationEngine, LearningPath, PathStrategy,
    ConceptGraph, PathNode
)
from path_visualization import (
    TimelineView, PathGraphView, ProgressTracker,
    DashboardRenderer, VisualizationTheme,
    export_path_to_json
)


class APIResponse:
    """API响应封装"""
    
    @staticmethod
    def success(data: Any = None, message: str = "Success") -> Dict[str, Any]:
        return {
            "success": True,
            "message": message,
            "data": data,
            "timestamp": datetime.now().isoformat()
        }
    
    @staticmethod
    def error(message: str, code: int = 400, details: Any = None) -> Dict[str, Any]:
        return {
            "success": False,
            "message": message,
            "code": code,
            "details": details,
            "timestamp": datetime.now().isoformat()
        }


class UserProfileAPI:
    """用户画像API"""
    
    # 内存存储（实际应用应使用数据库）
    _users: Dict[str, UserProfile] = {}
    
    @classmethod
    def create_user(cls, name: str, email: str, 
                    preset_type: Optional[str] = None) -> Dict[str, Any]:
        """创建新用户"""
        try:
            if preset_type:
                user = create_preset_profile(preset_type, name, email)
            else:
                user = UserProfile(name=name, email=email)
            
            cls._users[user.user_id] = user
            
            return APIResponse.success(
                data={
                    "user_id": user.user_id,
                    "name": user.name,
                    "email": user.email,
                    "created_at": user.created_at.isoformat()
                },
                message="用户创建成功"
            )
        except Exception as e:
            return APIResponse.error(str(e))
    
    @classmethod
    def get_user(cls, user_id: str) -> Dict[str, Any]:
        """获取用户信息"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        return APIResponse.success(data=user.to_dict())
    
    @classmethod
    def update_learning_style(cls, user_id: str, 
                              style_scores: Dict[str, float]) -> Dict[str, Any]:
        """更新学习风格"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        try:
            style_mapping = {
                "visual": LearningStyle.VISUAL,
                "textual": LearningStyle.TEXTUAL,
                "interactive": LearningStyle.INTERACTIVE,
                "multimodal": LearningStyle.MULTIMODAL
            }
            
            weights = {
                style_mapping[k]: v 
                for k, v in style_scores.items() 
                if k in style_mapping
            }
            
            user.learning_preference.update_style_weights(weights)
            
            return APIResponse.success(
                data={"dominant_style": user.learning_preference.get_dominant_style().value},
                message="学习风格更新成功"
            )
        except Exception as e:
            return APIResponse.error(str(e))
    
    @classmethod
    def update_time_preference(cls, user_id: str,
                               daily_hours: float,
                               weekly_days: int,
                               session_duration: int = 45) -> Dict[str, Any]:
        """更新学习时间偏好"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        user.time_preference.daily_hours = daily_hours
        user.time_preference.weekly_days = weekly_days
        user.time_preference.session_duration = session_duration
        
        return APIResponse.success(
            data={
                "daily_hours": daily_hours,
                "weekly_days": weekly_days,
                "weekly_hours": user.time_preference.get_weekly_hours()
            },
            message="时间偏好更新成功"
        )
    
    @classmethod
    def add_mastery(cls, user_id: str, concept_id: str, 
                    score: float) -> Dict[str, Any]:
        """添加概念掌握度"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        user.update_mastery(concept_id, score)
        
        return APIResponse.success(
            data={
                "concept_id": concept_id,
                "mastery_level": user.get_concept_mastery(concept_id),
                "mastered_concepts_count": len(user.get_mastered_concept_ids())
            },
            message="掌握度更新成功"
        )
    
    @classmethod
    def add_goal(cls, user_id: str, name: str,
                 target_concepts: List[str],
                 deadline: Optional[str] = None,
                 priority: str = "medium") -> Dict[str, Any]:
        """添加学习目标"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        try:
            priority_map = {
                "low": LearningGoalPriority.LOW,
                "medium": LearningGoalPriority.MEDIUM,
                "high": LearningGoalPriority.HIGH,
                "critical": LearningGoalPriority.CRITICAL
            }
            
            goal = LearningGoal(
                name=name,
                target_concepts=target_concepts,
                priority=priority_map.get(priority, LearningGoalPriority.MEDIUM)
            )
            
            if deadline:
                goal.deadline = datetime.fromisoformat(deadline)
            
            user.add_goal(goal)
            
            return APIResponse.success(
                data={
                    "goal_id": goal.goal_id,
                    "name": goal.name,
                    "target_concepts": goal.target_concepts,
                    "days_remaining": goal.get_days_remaining()
                },
                message="学习目标添加成功"
            )
        except Exception as e:
            return APIResponse.error(str(e))
    
    @classmethod
    def get_learning_statistics(cls, user_id: str) -> Dict[str, Any]:
        """获取学习统计"""
        user = cls._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        return APIResponse.success(data=user.get_learning_statistics())
    
    @classmethod
    def get_assessment_questions(cls) -> Dict[str, Any]:
        """获取评估问卷"""
        return APIResponse.success(data=USER_PROFILE_QUESTIONS)


class RecommendationAPI:
    """推荐API"""
    
    _engines: Dict[str, RecommendationEngine] = {}
    _paths: Dict[str, LearningPath] = {}
    
    @classmethod
    def initialize_engine(cls, engine_id: str, concept_graph: ConceptGraph):
        """初始化推荐引擎"""
        cls._engines[engine_id] = RecommendationEngine(concept_graph)
    
    @classmethod
    def recommend_paths(cls, user_id: str,
                       engine_id: str = "default",
                       strategy: str = "adaptive",
                       target_concepts: Optional[List[str]] = None,
                       num_alternatives: int = 2) -> Dict[str, Any]:
        """推荐学习路径"""
        # 获取用户
        user = UserProfileAPI._users.get(user_id)
        if not user:
            return APIResponse.error("用户不存在", code=404)
        
        # 获取引擎
        engine = cls._engines.get(engine_id)
        if not engine:
            return APIResponse.error("推荐引擎未初始化", code=500)
        
        try:
            # 策略映射
            strategy_map = {
                "shortest_time": PathStrategy.SHORTEST_TIME,
                "solid_foundation": PathStrategy.SOLID_FOUNDATION,
                "quick_overview": PathStrategy.QUICK_OVERVIEW,
                "adaptive": PathStrategy.ADAPTIVE,
                "challenge": PathStrategy.CHALLENGE,
                "balanced": PathStrategy.BALANCED
            }
            
            selected_strategy = strategy_map.get(strategy, PathStrategy.ADAPTIVE)
            
            # 生成路径
            paths = engine.recommend(
                user_profile=user,
                strategy=selected_strategy,
                target_concepts=target_concepts,
                num_alternatives=num_alternatives
            )
            
            # 保存路径
            for path in paths:
                cls._paths[path.path_id] = path
            
            return APIResponse.success(
                data={
                    "paths": [p.to_dict() for p in paths],
                    "strategy": strategy,
                    "user_id": user_id
                },
                message="路径推荐成功"
            )
        except Exception as e:
            return APIResponse.error(str(e))
    
    @classmethod
    def get_path_details(cls, path_id: str) -> Dict[str, Any]:
        """获取路径详情"""
        path = cls._paths.get(path_id)
        if not path:
            return APIResponse.error("路径不存在", code=404)
        
        return APIResponse.success(data=path.to_dict())
    
    @classmethod
    def compare_paths(cls, path_ids: List[str]) -> Dict[str, Any]:
        """比较多条路径"""
        paths = []
        for pid in path_ids:
            path = cls._paths.get(pid)
            if path:
                paths.append(path)
        
        if len(paths) < 2:
            return APIResponse.error("至少需要两条路径进行比较")
        
        comparison = {
            "paths": [
                {
                    "path_id": p.path_id,
                    "name": p.name,
                    "total_hours": p.total_estimated_hours,
                    "concept_count": len(p.nodes),
                    "overall_score": p.overall_score,
                    "difficulty_smoothness": p.difficulty_smoothness_score,
                    "time_efficiency": p.time_efficiency_score
                }
                for p in paths
            ],
            "recommendation": paths[0].name  # 评分最高的
        }
        
        return APIResponse.success(data=comparison)


class VisualizationAPI:
    """可视化API"""
    
    @classmethod
    def get_timeline(cls, user_id: str, path_id: str) -> Dict[str, Any]:
        """获取时间线"""
        user = UserProfileAPI._users.get(user_id)
        path = RecommendationAPI._paths.get(path_id)
        
        if not user or not path:
            return APIResponse.error("用户或路径不存在", code=404)
        
        timeline = TimelineView()
        timeline.generate_from_path(path, user)
        
        return APIResponse.success(
            data={
                "events": [e.to_dict() for e in timeline.events],
                "start_date": timeline.start_date.isoformat(),
                "end_date": timeline.end_date.isoformat() if timeline.end_date else None
            }
        )
    
    @classmethod
    def export_timeline_html(cls, user_id: str, path_id: str,
                            theme: str = "light") -> Dict[str, Any]:
        """导出时间线HTML"""
        user = UserProfileAPI._users.get(user_id)
        path = RecommendationAPI._paths.get(path_id)
        
        if not user or not path:
            return APIResponse.error("用户或路径不存在", code=404)
        
        timeline = TimelineView()
        timeline.generate_from_path(path, user)
        
        theme_map = {
            "light": VisualizationTheme.LIGHT,
            "dark": VisualizationTheme.DARK,
            "colorful": VisualizationTheme.COLORFUL
        }
        
        html = timeline.to_html(theme_map.get(theme, VisualizationTheme.LIGHT))
        
        return APIResponse.success(
            data={
                "html": html,
                "filename": f"timeline_{path_id}.html"
            }
        )
    
    @classmethod
    def get_path_graph(cls, path_id: str, 
                       format: str = "mermaid") -> Dict[str, Any]:
        """获取路径依赖图"""
        path = RecommendationAPI._paths.get(path_id)
        if not path:
            return APIResponse.error("路径不存在", code=404)
        
        # 这里需要一个概念图实例
        from recommendation_engine import create_sample_graph
        concept_graph = create_sample_graph()
        
        path_graph = PathGraphView()
        path_graph.generate_from_path(path, concept_graph)
        
        if format == "mermaid":
            return APIResponse.success(data={
                "mermaid_code": path_graph.to_mermaid()
            })
        elif format == "cytoscape":
            return APIResponse.success(data=path_graph.to_cytoscape_json())
        else:
            return APIResponse.error("不支持的格式")
    
    @classmethod
    def get_progress_dashboard(cls, user_id: str, 
                               path_id: str) -> Dict[str, Any]:
        """获取进度仪表板"""
        user = UserProfileAPI._users.get(user_id)
        path = RecommendationAPI._paths.get(path_id)
        
        if not user or not path:
            return APIResponse.error("用户或路径不存在", code=404)
        
        progress = ProgressTracker()
        progress.update_from_user_profile(user, path)
        
        return APIResponse.success(data=progress.to_dashboard_data())
    
    @classmethod
    def export_dashboard_html(cls, user_id: str, path_id: str) -> Dict[str, Any]:
        """导出仪表板HTML"""
        user = UserProfileAPI._users.get(user_id)
        path = RecommendationAPI._paths.get(path_id)
        
        if not user or not path:
            return APIResponse.error("用户或路径不存在", code=404)
        
        from recommendation_engine import create_sample_graph
        concept_graph = create_sample_graph()
        
        renderer = DashboardRenderer()
        html = renderer.render_full_dashboard(user, path, concept_graph)
        
        return APIResponse.success(
            data={
                "html": html,
                "filename": f"dashboard_{user_id}_{path_id}.html"
            }
        )
    
    @classmethod
    def export_path_json(cls, user_id: str, path_id: str) -> Dict[str, Any]:
        """导出路径JSON"""
        user = UserProfileAPI._users.get(user_id)
        path = RecommendationAPI._paths.get(path_id)
        
        if not user or not path:
            return APIResponse.error("用户或路径不存在", code=404)
        
        data = export_path_to_json(path, user)
        
        return APIResponse.success(data=data)


# 预设概念图数据
def initialize_default_engine():
    """初始化默认推荐引擎"""
    from recommendation_engine import create_sample_graph
    concept_graph = create_sample_graph()
    RecommendationAPI.initialize_engine("default", concept_graph)


# 初始化
initialize_default_engine()


if __name__ == "__main__":
    # API测试
    print("=== API接口测试 ===\n")
    
    # 1. 创建用户
    print("1. 创建用户")
    result = UserProfileAPI.create_user("张三", "zhangsan@example.com", "advanced_learner")
    print(f"   结果: {result['message']}")
    user_id = result['data']['user_id']
    print(f"   用户ID: {user_id}")
    
    # 2. 获取用户信息
    print("\n2. 获取用户信息")
    result = UserProfileAPI.get_user(user_id)
    print(f"   用户: {result['data']['name']}")
    print(f"   学习风格: {result['data']['learning_style']}")
    
    # 3. 添加掌握度
    print("\n3. 添加掌握度")
    result = UserProfileAPI.add_mastery(user_id, "set_theory", 0.85)
    print(f"   {result['message']}")
    result = UserProfileAPI.add_mastery(user_id, "functions", 0.75)
    print(f"   {result['message']}")
    
    # 4. 添加学习目标
    print("\n4. 添加学习目标")
    result = UserProfileAPI.add_goal(
        user_id, 
        "掌握代数拓扑",
        ["algebraic_topology", "linear_algebra"],
        priority="high"
    )
    print(f"   {result['message']}")
    print(f"   目标: {result['data']['name']}")
    
    # 5. 推荐路径
    print("\n5. 推荐路径")
    result = RecommendationAPI.recommend_paths(
        user_id,
        strategy="balanced",
        num_alternatives=1
    )
    print(f"   {result['message']}")
    print(f"   推荐路径数: {len(result['data']['paths'])}")
    
    path_id = result['data']['paths'][0]['path_id']
    print(f"   主路径ID: {path_id}")
    print(f"   路径名: {result['data']['paths'][0]['name']}")
    print(f"   总时间: {result['data']['paths'][0]['total_estimated_hours']:.1f}小时")
    
    # 6. 获取路径详情
    print("\n6. 获取路径详情")
    result = RecommendationAPI.get_path_details(path_id)
    print(f"   节点数: {len(result['data']['nodes'])}")
    print(f"   综合评分: {result['data']['overall_score']:.2f}")
    
    # 7. 获取时间线
    print("\n7. 获取时间线")
    result = VisualizationAPI.get_timeline(user_id, path_id)
    print(f"   事件数: {len(result['data']['events'])}")
    print(f"   开始日期: {result['data']['start_date']}")
    
    # 8. 获取进度仪表板
    print("\n8. 获取进度仪表板")
    result = VisualizationAPI.get_progress_dashboard(user_id, path_id)
    print(f"   整体进度: {result['data']['overall_progress']:.1f}%")
    print(f"   已完成: {result['data']['completed_count']}")
    print(f"   进行中: {result['data']['in_progress_count']}")
    
    # 9. 获取路径图（Mermaid）
    print("\n9. 获取路径图（Mermaid格式）")
    result = VisualizationAPI.get_path_graph(path_id, format="mermaid")
    print(f"   Mermaid代码长度: {len(result['data']['mermaid_code'])} 字符")
    
    # 10. 导出路径JSON
    print("\n10. 导出路径JSON")
    result = VisualizationAPI.export_path_json(user_id, path_id)
    print(f"   导出路径: {result['data']['path']['name']}")
    print(f"   用户: {result['data']['user']['name']}")
    
    print("\n=== 所有API测试通过 ===")
