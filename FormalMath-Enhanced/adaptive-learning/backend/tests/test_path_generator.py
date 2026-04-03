"""
路径生成算法测试
"""
import pytest
from datetime import datetime

from app.schemas import UserProfile, ConceptNode, DifficultyLevel, CognitiveStyle, LearningPreference
from app.adaptive import generate_learning_path, PathGenerator
from app.knowledge_graph import get_knowledge_graph


@pytest.fixture
def sample_user():
    """创建测试用户"""
    return UserProfile(
        user_id="test_user_001",
        cognitive_style=CognitiveStyle.VISUAL,
        learning_preference=LearningPreference.BALANCED,
        current_level=DifficultyLevel.INTERMEDIATE,
        mastered_concepts={},
        interest_areas=["代数", "分析"]
    )


@pytest.fixture
def sample_concepts():
    """创建测试概念"""
    return [
        ConceptNode(
            id="algebra_group",
            name="群论",
            branch="代数",
            difficulty=DifficultyLevel.INTERMEDIATE,
            estimated_time=60
        ),
        ConceptNode(
            id="algebra_ring",
            name="环论",
            branch="代数",
            difficulty=DifficultyLevel.ADVANCED,
            estimated_time=90
        ),
        ConceptNode(
            id="analysis_limit",
            name="极限",
            branch="分析",
            difficulty=DifficultyLevel.BEGINNER,
            estimated_time=45
        )
    ]


class TestPathGenerator:
    """测试路径生成器"""
    
    def test_path_generator_initialization(self, sample_user):
        """测试路径生成器初始化"""
        generator = PathGenerator(sample_user)
        assert generator.user_profile == sample_user
        assert generator.kg is not None
    
    def test_generate_path_with_empty_targets(self, sample_user):
        """测试空目标列表"""
        generator = PathGenerator(sample_user)
        path = generator.generate([])
        assert path is None
    
    def test_generate_path_with_astar(self, sample_user):
        """测试 A* 算法路径生成"""
        # 确保知识图谱已加载
        kg = get_knowledge_graph()
        if not kg._initialized:
            pytest.skip("知识图谱未加载")
        
        # 使用图谱中实际存在的概念
        target_concepts = list(kg.concepts.keys())[:3]
        
        path = generate_learning_path(
            user_profile=sample_user,
            target_concepts=target_concepts,
            algorithm="astar"
        )
        
        if path:
            assert path.user_id == sample_user.user_id
            assert len(path.nodes) > 0
            assert path.total_concepts > 0
    
    def test_generate_path_with_dp(self, sample_user):
        """测试动态规划路径生成"""
        kg = get_knowledge_graph()
        if not kg._initialized:
            pytest.skip("知识图谱未加载")
        
        target_concepts = list(kg.concepts.keys())[:3]
        
        path = generate_learning_path(
            user_profile=sample_user,
            target_concepts=target_concepts,
            algorithm="dp"
        )
        
        # 动态规划可能返回 None 如果优化目标无法达成
        if path:
            assert path.user_id == sample_user.user_id


class TestLearnerProfiler:
    """测试学习者画像分析"""
    
    def test_cognitive_style_analysis(self):
        """测试认知风格分析"""
        from app.adaptive import LearnerProfiler
        
        profiler = LearnerProfiler()
        # 空活动列表应返回默认风格
        style = profiler.analyze_cognitive_style([])
        assert style == CognitiveStyle.MIXED


class TestKnowledgeGraph:
    """测试知识图谱"""
    
    def test_knowledge_graph_loading(self):
        """测试知识图谱加载"""
        kg = get_knowledge_graph()
        # 知识图谱应该已初始化
        assert kg._initialized or len(kg.concepts) > 0
    
    def test_concept_retrieval(self):
        """测试概念获取"""
        kg = get_knowledge_graph()
        
        # 测试获取所有概念
        concepts = kg.get_all_concepts()
        assert isinstance(concepts, list)
    
    def test_prerequisites_retrieval(self):
        """测试先修概念获取"""
        kg = get_knowledge_graph()
        
        if kg.concepts:
            concept_id = list(kg.concepts.keys())[0]
            prereqs = kg.get_prerequisites(concept_id)
            assert isinstance(prereqs, list)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
