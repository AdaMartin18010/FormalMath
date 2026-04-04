"""
推荐系统 v2.0 使用示例
=====================

本文件展示如何使用优化后的推荐算法系统。
"""

import logging
from datetime import datetime
from typing import List, Dict, Any

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def example_basic_recommendation():
    """示例1: 基本推荐功能"""
    print("=" * 50)
    print("示例1: 基本推荐功能")
    print("=" * 50)
    
    # 导入推荐器
    from .advanced_hybrid_recommender import get_advanced_recommender
    
    # 假设我们有数据库会话
    # db = get_db_session()
    
    # 创建推荐器实例
    # recommender = get_advanced_recommender(db)
    # recommender.initialize()
    
    # 为用户生成推荐
    # user_id = 123
    # result = recommender.recommend(
    #     user_id=user_id,
    #     n_recommendations=10,
    #     context={"is_new_user": False},
    #     enable_diversity=True,
    #     enable_explanation=True
    # )
    
    # print(f"为用户 {user_id} 生成推荐:")
    # for rec in result["recommendations"]:
    #     print(f"  - {rec['name']} (分数: {rec['final_score']:.4f})")
    #     print(f"    理由: {rec['explanation'].get('primary_reason', 'N/A')}")
    
    print("[演示代码，实际需要数据库连接]")
    print()


def example_feedback_learning():
    """示例2: 反馈学习"""
    print("=" * 50)
    print("示例2: 反馈学习")
    print("=" * 50)
    
    # from .advanced_hybrid_recommender import get_advanced_recommender
    
    # db = get_db_session()
    # recommender = get_advanced_recommender(db)
    
    # 记录用户反馈
    # user_id = 123
    # concept_id = "algebra_group_theory"
    
    # 用户点击了推荐
    # recommender.record_feedback(
    #     user_id=user_id,
    #     concept_id=concept_id,
    #     action="click",
    #     context={"position": 1}
    # )
    
    # 用户完成了学习
    # recommender.record_feedback(
    #     user_id=user_id,
    #     concept_id=concept_id,
    #     action="complete",
    #     rating=4.5,
    #     context={"study_time": 45}
    # )
    
    print("支持的反馈动作:")
    print("  - click: 点击推荐")
    print("  - complete: 完成学习")
    print("  - bookmark: 收藏")
    print("  - share: 分享")
    print("  - dismiss: 忽略")
    print("  - skip: 跳过")
    print("  - rate: 评分")
    print()


def example_cold_start():
    """示例3: 冷启动处理"""
    print("=" * 50)
    print("示例3: 冷启动处理")
    print("=" * 50)
    
    # from .advanced_hybrid_recommender import ColdStartHandler
    
    # db = get_db_session()
    # handler = ColdStartHandler(db)
    
    # 检测冷启动等级
    # user_id = 456  # 新用户
    # level, info = handler.detect_cold_start_level(user_id)
    # print(f"用户 {user_id} 冷启动等级: {level.value}")
    # print(f"  活动数: {info['activity_count']}")
    # print(f"  进度数: {info['progress_count']}")
    # print(f"  是否已知兴趣: {info['has_interest']}")
    
    # 获取冷启动推荐
    # recommendations = handler.get_cold_start_recommendations(
    #     user_id=user_id,
    #     n_recommendations=10,
    #     level=level
    # )
    
    print("冷启动等级:")
    print("  - NEW_USER: 完全新用户")
    print("  - INTEREST_KNOWN: 已知兴趣")
    print("  - SOME_ACTIVITY: 有一些活动")
    print("  - WARM_USER: 接近正常用户")
    print()


def example_diversity_enhancement():
    """示例4: 多样性增强"""
    print("=" * 50)
    print("示例4: 多样性增强")
    print("=" * 50)
    
    # from .advanced_hybrid_recommender import DiversityEnhancer, RecommendationItem
    
    # 创建多样性增强器
    # enhancer = DiversityEnhancer(
    #     lambda_param=0.5,  # 多样性vs相关性平衡参数
    #     branch_diversity_weight=0.4,
    #     difficulty_diversity_weight=0.3,
    #     novelty_weight=0.3
    # )
    
    # 假设有候选推荐
    # candidates = [...]  # List[RecommendationItem]
    
    # 增强多样性
    # diverse_recommendations = enhancer.enhance_diversity(
    #     candidates=candidates,
    #     user_id=123,
    #     n_recommendations=10,
    #     ensure_branch_coverage=True
    # )
    
    print("MMR (Maximal Marginal Relevance) 算法:")
    print("  MMR = λ * Relevance - (1-λ) * max(Similarity)")
    print()
    print("多样性指标:")
    print("  - Intra-list Diversity: 列表内多样性")
    print("  - Inter-list Diversity: 列表间多样性")
    print("  - Branch Coverage: 分支覆盖率")
    print()


def example_ab_testing():
    """示例5: A/B测试"""
    print("=" * 50)
    print("示例5: A/B测试")
    print("=" * 50)
    
    from .ab_testing_framework import get_ab_testing_manager
    
    # 获取A/B测试管理器
    manager = get_ab_testing_manager()
    
    # 从模板创建测试
    test = manager.create_test_from_template(
        template_name="weight_optimization",
        test_id="weight_test_202404"
    )
    
    # 启动测试
    # manager.start_test(test.test_id)
    
    print(f"创建测试: {test.test_id}")
    print(f"名称: {test.name}")
    print(f"描述: {test.description}")
    print(f"状态: {test.status.value}")
    print()
    
    # 分配用户到变体
    # user_id = 123
    # variant = manager.assign_user_to_variant(test.test_id, user_id)
    # print(f"用户 {user_id} 分配到变体: {variant}")
    
    # 记录事件
    # manager.record_event(
    #     test_id=test.test_id,
    #     user_id=user_id,
    #     event_type="click",
    #     value=1.0
    # )
    
    # 获取测试结果
    # results = manager.get_test_results(test.test_id)
    # print(results)
    
    print("可用测试模板:")
    print("  - weight_optimization: 推荐器权重优化")
    print("  - diversity_algorithm: 多样性算法测试")
    print("  - cold_start_strategy: 冷启动策略测试")
    print("  - explanation_effectiveness: 解释性推荐效果")
    print("  - feedback_learning: 反馈学习机制测试")
    print()


def example_evaluation():
    """示例6: 性能评估"""
    print("=" * 50)
    print("示例6: 性能评估")
    print("=" * 50)
    
    from .evaluation_report import EvaluationReportGenerator
    
    # 创建评估器
    # generator = EvaluationReportGenerator()
    
    # 生成评估报告
    # result = generator.generate_report(
    #     recommender=recommender,
    #     test_users=[1, 2, 3, ...],
    #     db_session=db
    # )
    
    # 导出报告
    # generator.export_to_markdown(result, "report.md")
    # generator.export_to_json(result, "report.json")
    
    print("评估维度:")
    print("  1. Accuracy (准确性): Precision, Recall, NDCG, MRR")
    print("  2. Diversity (多样性): Intra-list, Inter-list, Coverage")
    print("  3. Coverage (覆盖率): Catalog, User, Long-tail")
    print("  4. Satisfaction (满意度): CTR, Conversion, Rating")
    print("  5. Performance (性能): Response Time, Throughput")
    print("  6. Cold Start (冷启动): New User CTR, Conversion")
    print()


def example_custom_configuration():
    """示例7: 自定义配置"""
    print("=" * 50)
    print("示例7: 自定义配置")
    print("=" * 50)
    
    # from .advanced_hybrid_recommender import (
    #     AdvancedHybridRecommender,
    #     DynamicWeightAdjuster,
    #     DiversityEnhancer
    # )
    
    print("自定义动态权重调整器:")
    print("""
    weight_adjuster = DynamicWeightAdjuster(
        learning_rate=0.05,      # 学习率
        min_weight=0.05,         # 最小权重
        max_weight=0.6,          # 最大权重
        momentum=0.9,            # 动量
        regularization=0.01      # 正则化
    )
    """)
    
    print("\n自定义多样性增强器:")
    print("""
    diversity_enhancer = DiversityEnhancer(
        lambda_param=0.5,                    # MMR参数
        branch_diversity_weight=0.4,         # 分支多样性权重
        difficulty_diversity_weight=0.3,     # 难度多样性权重
        novelty_weight=0.3                   # 新颖性权重
    )
    """)
    print()


def run_all_examples():
    """运行所有示例"""
    print("\n" + "=" * 50)
    print("FormalMath 推荐系统 v2.0 使用示例")
    print("=" * 50 + "\n")
    
    example_basic_recommendation()
    example_feedback_learning()
    example_cold_start()
    example_diversity_enhancement()
    example_ab_testing()
    example_evaluation()
    example_custom_configuration()
    
    print("=" * 50)
    print("示例演示完成")
    print("=" * 50)


if __name__ == "__main__":
    run_all_examples()
