"""
个性化学习路径推荐系统

基于全局依赖图的个性化学习路径推荐算法实现

主要模块:
- user_profile: 用户画像模型
- recommendation_engine: 推荐算法引擎
- path_visualization: 路径可视化组件
- api: API接口

使用示例:
    from personalized_recommendation import (
        UserProfile, RecommendationEngine, ConceptGraph,
        PathStrategy, DashboardRenderer
    )
    
    # 创建概念图
    graph = ConceptGraph()
    graph.add_concept("calculus", "微积分", difficulty=3, estimated_time=180)
    
    # 创建用户画像
    user = UserProfile(name="张三", email="zhangsan@example.com")
    
    # 生成推荐
    engine = RecommendationEngine(graph)
    paths = engine.recommend(user, strategy=PathStrategy.BALANCED)
    
    # 渲染仪表板
    renderer = DashboardRenderer()
    html = renderer.render_full_dashboard(user, paths[0], graph)
"""

__version__ = "1.0.0"
__author__ = "FormalMath Team"

from user_profile import (
    UserProfile, LearningGoal, ConceptMastery, LearningStyle,
    LearningPreference, TimePreference, LearningGoalPriority,
    ProficiencyLevel, create_preset_profile, PRESET_PROFILES
)

from recommendation_engine import (
    RecommendationEngine, LearningPath, PathNode, ConceptGraph,
    PathStrategy, PathScorer, create_sample_graph
)

from path_visualization import (
    TimelineView, PathGraphView, ProgressTracker, DashboardRenderer,
    VisualizationTheme, export_path_to_json
)

from api import (
    UserProfileAPI, RecommendationAPI, VisualizationAPI,
    APIResponse
)

__all__ = [
    # 用户画像
    'UserProfile',
    'LearningGoal',
    'ConceptMastery',
    'LearningStyle',
    'LearningPreference',
    'TimePreference',
    'LearningGoalPriority',
    'ProficiencyLevel',
    'create_preset_profile',
    'PRESET_PROFILES',
    
    # 推荐引擎
    'RecommendationEngine',
    'LearningPath',
    'PathNode',
    'ConceptGraph',
    'PathStrategy',
    'PathScorer',
    'create_sample_graph',
    
    # 可视化
    'TimelineView',
    'PathGraphView',
    'ProgressTracker',
    'DashboardRenderer',
    'VisualizationTheme',
    'export_path_to_json',
    
    # API
    'UserProfileAPI',
    'RecommendationAPI',
    'VisualizationAPI',
    'APIResponse',
]
