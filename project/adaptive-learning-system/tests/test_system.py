"""
自适应学习路径系统测试
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'backend', 'src'))

import unittest
from datetime import datetime

from models.learner import LearnerProfile, LearningStyleProfile, LearningStyle
from models.knowledge_graph import KnowledgeGraph, ConceptNode, DifficultyLevel, RelationType, RelationEdge
from models.learning_path import LearningPath, PathNode, NodeStatus
from algorithms.path_generation import AStarPathPlanner, KnowledgeGapAnalyzer, PathScorer, PathConstraints
from algorithms.adaptive_engine import SpacedRepetitionScheduler


class TestLearnerProfile(unittest.TestCase):
    """测试学习者画像"""
    
    def test_create_learner(self):
        """测试创建学习者"""
        learner = LearnerProfile(name="测试用户", email="test@example.com")
        self.assertIsNotNone(learner.learner_id)
        self.assertEqual(learner.name, "测试用户")
        self.assertEqual(learner.email, "test@example.com")
    
    def test_learning_style(self):
        """测试学习风格评估"""
        style = LearningStyleProfile(
            visual_score=0.8,
            auditory_score=0.1,
            kinesthetic_score=0.05,
            reading_score=0.05
        )
        self.assertEqual(style.dominant_style, LearningStyle.VISUAL)
    
    def test_overall_ability(self):
        """测试整体能力计算"""
        learner = LearnerProfile()
        learner.ability_level = {0: 0.9, 1: 0.7, 2: 0.5, 3: 0.3}
        ability = learner.calculate_overall_ability()
        self.assertEqual(ability, 0.6)


class TestKnowledgeGraph(unittest.TestCase):
    """测试知识图谱"""
    
    def setUp(self):
        """初始化测试数据"""
        self.kg = KnowledgeGraph()
        
        # 添加测试概念
        self.node1 = ConceptNode(name="集合", difficulty=DifficultyLevel.BEGINNER)
        self.node2 = ConceptNode(name="函数", difficulty=DifficultyLevel.BEGINNER)
        self.node3 = ConceptNode(name="群", difficulty=DifficultyLevel.INTERMEDIATE)
        
        self.id1 = self.kg.add_node(self.node1)
        self.id2 = self.kg.add_node(self.node2)
        self.id3 = self.kg.add_node(self.node3)
        
        # 添加关系
        self.edge1 = RelationEdge(
            source_id=self.id1,
            target_id=self.id2,
            relation_type=RelationType.PREREQUISITE
        )
        self.edge2 = RelationEdge(
            source_id=self.id2,
            target_id=self.id3,
            relation_type=RelationType.PREREQUISITE
        )
        
        self.kg.add_edge(self.edge1)
        self.kg.add_edge(self.edge2)
    
    def test_add_node(self):
        """测试添加节点"""
        self.assertEqual(len(self.kg.nodes), 3)
        self.assertIn(self.id1, self.kg.nodes)
    
    def test_add_edge(self):
        """测试添加边"""
        self.assertEqual(len(self.kg.edges), 2)
    
    def test_get_prerequisites(self):
        """测试获取先修概念"""
        prereqs = self.kg.get_prerequisites(self.id2)
        self.assertIn(self.id1, prereqs)
    
    def test_get_prerequisite_graph(self):
        """测试获取完整先修图"""
        prereqs = self.kg.get_prerequisite_graph(self.id3)
        self.assertIn(self.id1, prereqs)
        self.assertIn(self.id2, prereqs)


class TestLearningPath(unittest.TestCase):
    """测试学习路径"""
    
    def setUp(self):
        """初始化测试数据"""
        self.path = LearningPath(name="测试路径", learner_id="test-learner")
        
        # 添加节点
        self.node1 = PathNode(concept_id="concept-1", sequence_number=0, status=NodeStatus.COMPLETED)
        self.node1.completion_percentage = 1.0
        self.node1.mastery_level = 0.85
        
        self.node2 = PathNode(concept_id="concept-2", sequence_number=1, status=NodeStatus.IN_PROGRESS)
        self.node2.completion_percentage = 0.5
        self.node2.mastery_level = 0.6
        
        self.node3 = PathNode(concept_id="concept-3", sequence_number=2, status=NodeStatus.LOCKED)
        
        self.path.nodes[self.node1.node_id] = self.node1
        self.path.nodes[self.node2.node_id] = self.node2
        self.path.nodes[self.node3.node_id] = self.node3
        self.path.node_order = [self.node1.node_id, self.node2.node_id, self.node3.node_id]
    
    def test_progress_calculation(self):
        """测试进度计算"""
        progress = self.path.calculate_overall_progress()
        expected = (1.0 + 0.5 + 0.0) / 3
        self.assertAlmostEqual(progress, expected)
    
    def test_completed_nodes(self):
        """测试已完成节点"""
        completed = self.path.get_completed_nodes()
        self.assertEqual(len(completed), 1)
        self.assertIn(self.node1.node_id, completed)


class TestPathGeneration(unittest.TestCase):
    """测试路径生成算法"""
    
    def setUp(self):
        """初始化测试数据"""
        self.kg = KnowledgeGraph()
        
        # 创建概念节点
        concepts = [
            ConceptNode(name="集合", difficulty=DifficultyLevel.BEGINNER, estimated_time_minutes=45),
            ConceptNode(name="函数", difficulty=DifficultyLevel.BEGINNER, estimated_time_minutes=60),
            ConceptNode(name="群", difficulty=DifficultyLevel.INTERMEDIATE, estimated_time_minutes=120),
            ConceptNode(name="环", difficulty=DifficultyLevel.INTERMEDIATE, estimated_time_minutes=120),
        ]
        
        self.concept_ids = {}
        for c in concepts:
            cid = self.kg.add_node(c)
            self.concept_ids[c.name] = cid
        
        # 添加关系
        relations = [
            ("集合", "函数", RelationType.PREREQUISITE),
            ("函数", "群", RelationType.PREREQUISITE),
            ("群", "环", RelationType.PREREQUISITE),
        ]
        
        for source, target, rtype in relations:
            edge = RelationEdge(
                source_id=self.concept_ids[source],
                target_id=self.concept_ids[target],
                relation_type=rtype
            )
            self.kg.add_edge(edge)
        
        # 创建学习者
        self.learner = LearnerProfile(name="测试学习者")
        self.learner.knowledge_state[self.concept_ids["集合"]] = 0.8
    
    def test_knowledge_gap_analysis(self):
        """测试知识缺口分析"""
        analyzer = KnowledgeGapAnalyzer(self.kg, self.learner)
        gaps = analyzer.analyze_gaps([self.concept_ids["环"]])
        
        self.assertIn("knowledge_gaps", gaps)
        self.assertIn("estimated_study_time", gaps)
    
    def test_path_planner(self):
        """测试路径规划器"""
        planner = AStarPathPlanner(self.kg, self.learner)
        
        constraints = PathConstraints(max_total_time_hours=10)
        path = planner.find_optimal_path(
            [],
            [self.concept_ids["环"]],
            constraints
        )
        
        self.assertIsNotNone(path)
        self.assertGreater(len(path.nodes), 0)


class TestSpacedRepetition(unittest.TestCase):
    """测试间隔重复算法"""
    
    def test_interval_calculation(self):
        """测试复习间隔计算"""
        scheduler = SpacedRepetitionScheduler(None, None)
        
        # 高掌握度 (乘数 2.0)
        intervals_high = scheduler.calculate_review_intervals("test", 0.9, 0)
        self.assertEqual(intervals_high[0], 2)  # 基础间隔1 * 2.0 = 2
        
        # 中等掌握度 (乘数 1.5)
        intervals_medium = scheduler.calculate_review_intervals("test", 0.75, 0)
        self.assertEqual(intervals_medium[0], 1)  # 基础间隔1 * 1.5 = 1.5 -> int(1.5) = 1
        
        # 低掌握度 (乘数 0.7)
        intervals_low = scheduler.calculate_review_intervals("test", 0.5, 0)
        self.assertEqual(intervals_low[0], 0)  # 基础间隔1 * 0.7 = 0.7 -> int(0.7) = 0


class TestIntegration(unittest.TestCase):
    """集成测试"""
    
    def test_complete_workflow(self):
        """测试完整工作流"""
        # 1. 创建学习者
        learner = LearnerProfile(name="集成测试用户", email="integration@test.com")
        
        # 2. 设置学习风格
        learner.learning_style = LearningStyleProfile(
            visual_score=0.7,
            auditory_score=0.1,
            kinesthetic_score=0.1,
            reading_score=0.1
        )
        
        # 3. 初始化知识图谱
        kg = KnowledgeGraph()
        concept = ConceptNode(name="测试概念", difficulty=DifficultyLevel.BEGINNER)
        cid = kg.add_node(concept)
        
        # 4. 生成路径
        planner = AStarPathPlanner(kg, learner)
        constraints = PathConstraints()
        path = planner.find_optimal_path([], [cid], constraints)
        
        # 5. 验证路径
        self.assertIsNotNone(path)
        self.assertEqual(path.status.value, "pending")
        
        # 6. 更新进度
        node_id = path.node_order[0]
        path.update_progress(node_id, 1.0, 0.85)
        
        # 7. 验证进度
        self.assertEqual(path.nodes[node_id].status.value, "completed")
        self.assertGreater(path.calculate_overall_progress(), 0)


def run_tests():
    """运行所有测试"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # 添加测试类
    suite.addTests(loader.loadTestsFromTestCase(TestLearnerProfile))
    suite.addTests(loader.loadTestsFromTestCase(TestKnowledgeGraph))
    suite.addTests(loader.loadTestsFromTestCase(TestLearningPath))
    suite.addTests(loader.loadTestsFromTestCase(TestPathGeneration))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacedRepetition))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # 运行测试
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
