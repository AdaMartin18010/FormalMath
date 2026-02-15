# -*- coding: utf-8 -*-
"""
demo.py - FormalMath 评估系统演示脚本

本脚本演示评估系统的主要功能，包括：
- 学习者注册与管理
- 各种评估类型的执行
- 反馈和报告生成
- 报告导出
"""

import os
import sys
from datetime import datetime, timedelta

# 导入评估系统模块
from evaluation_criteria import (
    LearnerProfile, MathematicalAbilityProfile, 
    ConceptualUnderstanding, ProceduralFluency, StrategicCompetence,
    AdaptiveReasoning, ProductiveDisposition, EvaluationCriteria
)
from scoring_engine import ScoringEngine
from feedback_generator import FeedbackGenerator, FeedbackType
from report_generator import ReportGenerator, ReportType, ReportFormat
from assessment_system import FormalMathAssessmentSystem, AssessmentConfig, AssessmentType


def print_separator(title: str = ""):
    """打印分隔线"""
    print("\n" + "=" * 60)
    if title:
        print(f"  {title}")
        print("=" * 60)


def print_subsection(title: str):
    """打印子标题"""
    print(f"\n--- {title} ---\n")


def demo_basic_evaluation():
    """演示基础评估功能"""
    print_separator("演示 1: 基础评估功能")
    
    # 创建能力档案
    ability_profile = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=75.0,
            principle_comprehension=70.0,
            relationship_grasp=65.0
        ),
        procedural_fluency=ProceduralFluency(
            accuracy=80.0,
            efficiency=70.0,
            flexibility=60.0
        ),
        strategic_competence=StrategicCompetence(
            problem_analysis=65.0,
            strategy_formulation=70.0,
            strategy_execution=60.0
        ),
        adaptive_reasoning=AdaptiveReasoning(
            logical_thinking=70.0,
            justification_ability=65.0,
            explanation_clarity=60.0
        ),
        productive_disposition=ProductiveDisposition(
            confidence=75.0,
            persistence=80.0,
            appreciation=70.0
        )
    )
    
    print_subsection("五维能力得分")
    scores = ability_profile.get_dimension_scores()
    for dim, score in scores.items():
        bar = "█" * int(score / 10) + "░" * (10 - int(score / 10))
        level = EvaluationCriteria.get_level(score)
        print(f"  {dim:12s}: {score:5.1f} {bar} [{level.name}]")
    
    print_subsection("综合评分")
    overall = ability_profile.calculate_overall_score()
    overall_level = EvaluationCriteria.get_level(overall)
    print(f"  综合得分: {overall:.1f}/100")
    print(f"  能力等级: {overall_level.name}")
    print(f"  等级描述: {EvaluationCriteria.get_level_description(overall_level)}")
    
    print_subsection("强弱分析")
    strengths = ability_profile.identify_strengths(threshold=70)
    weaknesses = ability_profile.identify_weaknesses(threshold=60)
    
    print(f"  强项 (≥70分): {', '.join(strengths) if strengths else '无'}")
    print(f"  待改进 (<60分): {', '.join(weaknesses) if weaknesses else '无'}")
    
    return ability_profile


def demo_scoring_engine():
    """演示评分引擎"""
    print_separator("演示 2: 评分引擎")
    
    scoring_engine = ScoringEngine()
    
    # 创建能力档案
    ability_profile = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=78.0,
            principle_comprehension=72.0,
            relationship_grasp=75.0
        ),
        procedural_fluency=ProceduralFluency(
            accuracy=85.0,
            efficiency=75.0,
            flexibility=70.0
        ),
        strategic_competence=StrategicCompetence(
            problem_analysis=68.0,
            strategy_formulation=72.0,
            strategy_execution=65.0
        ),
        adaptive_reasoning=AdaptiveReasoning(
            logical_thinking=74.0,
            justification_ability=68.0,
            explanation_clarity=70.0
        ),
        productive_disposition=ProductiveDisposition(
            confidence=76.0,
            persistence=82.0,
            appreciation=74.0
        )
    )
    
    print_subsection("数学能力评估")
    result = scoring_engine.evaluate_mathematical_ability(ability_profile)
    
    print(f"  综合得分: {result['overall_score']:.1f}")
    print(f"  能力等级: {result['level'].name}")
    print(f"  等级描述: {result['level_description']}")
    print("\n  各维度得分:")
    for dim, score in result['dimension_scores'].items():
        print(f"    {dim}: {score:.1f}")


def demo_feedback_generation():
    """演示反馈生成"""
    print_separator("演示 3: 反馈生成")
    
    # 创建学习者档案
    learner = LearnerProfile(
        learner_id="demo_student_001",
        name="张三"
    )
    
    # 设置能力档案
    learner.current_ability = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=78.0,
            principle_comprehension=72.0,
            relationship_grasp=75.0
        ),
        procedural_fluency=ProceduralFluency(
            accuracy=85.0,
            efficiency=75.0,
            flexibility=70.0
        ),
        strategic_competence=StrategicCompetence(
            problem_analysis=55.0,  # 较低，用于演示改进建议
            strategy_formulation=58.0,
            strategy_execution=52.0
        ),
        adaptive_reasoning=AdaptiveReasoning(
            logical_thinking=74.0,
            justification_ability=68.0,
            explanation_clarity=70.0
        ),
        productive_disposition=ProductiveDisposition(
            confidence=76.0,
            persistence=82.0,
            appreciation=74.0
        )
    )
    
    # 创建评估结果
    scoring_engine = ScoringEngine()
    assessment_result = scoring_engine.evaluate_mathematical_ability(learner.current_ability)
    
    # 生成反馈
    feedback_gen = FeedbackGenerator()
    feedback_report = feedback_gen.generate_feedback(
        learner, assessment_result, FeedbackType.SUMMARY
    )
    
    print_subsection("反馈报告概览")
    print(f"  学习者: {feedback_report.learner_id}")
    print(f"  反馈类型: {feedback_report.feedback_type.name}")
    print(f"  整体反馈: {feedback_report.overall_feedback[:100]}...")
    
    print_subsection("反馈详情")
    for item in feedback_report.items:
        print(f"\n  [{item.priority.value.upper()}] {item.title}")
        print(f"  内容: {item.content[:80]}...")
        if item.suggestions:
            print(f"  建议: {item.suggestions[0][:60]}...")


def demo_full_assessment_system():
    """演示完整评估系统"""
    print_separator("演示 4: 完整评估系统")
    
    # 初始化评估系统
    config = AssessmentConfig()
    assessment_system = FormalMathAssessmentSystem(config)
    
    print_subsection("系统信息")
    info = assessment_system.get_system_info()
    for key, value in info.items():
        print(f"  {key}: {value}")
    
    # 注册学习者
    learner_id = "student_001"
    profile = assessment_system.register_learner(learner_id, "李四")
    print_subsection(f"注册学习者: {profile.name} (ID: {profile.learner_id})")
    
    # 设置能力档案
    profile.current_ability = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=75.0,
            principle_comprehension=70.0,
            relationship_grasp=72.0
        ),
        procedural_fluency=ProceduralFluency(
            accuracy=80.0,
            efficiency=72.0,
            flexibility=68.0
        ),
        strategic_competence=StrategicCompetence(
            problem_analysis=65.0,
            strategy_formulation=68.0,
            strategy_execution=62.0
        ),
        adaptive_reasoning=AdaptiveReasoning(
            logical_thinking=70.0,
            justification_ability=65.0,
            explanation_clarity=68.0
        ),
        productive_disposition=ProductiveDisposition(
            confidence=75.0,
            persistence=80.0,
            appreciation=72.0
        )
    )
    
    # 更新知识状态
    concepts = ["集合论", "函数", "极限", "导数", "积分"]
    for i, concept in enumerate(concepts):
        assessment_system.update_learner_knowledge(learner_id, concept, 60 + i * 8)
    
    print_subsection("知识状态")
    for concept, mastery in profile.knowledge_state.items():
        print(f"  {concept}: {mastery:.1f}%")
    
    # 进行形成性评价
    print_subsection("形成性评价")
    formative_result = assessment_system.conduct_formative_assessment(learner_id)
    print(f"  结果ID: {formative_result.result_id}")
    print(f"  综合得分: {formative_result.overall_score:.1f}")
    print(f"  能力等级: {formative_result.level.name}")
    
    # 进行过程性评价
    print_subsection("过程性评价")
    
    # 模拟学习历史
    for i in range(10):
        assessment_system.record_learning_activity(learner_id, {
            'date': (datetime.now() - timedelta(days=i)).strftime('%Y-%m-%d'),
            'duration': 45 + i * 5,
            'topics': ['代数', '几何'],
            'content_depth': 70 + i * 2,
            'is_active_learning': i % 2 == 0,
            'questions_asked': i % 3
        })
    
    learning_path = {
        'content_items': ['章节1', '章节2', '章节3', '章节4', '章节5'],
        'goals': [
            {'description': '掌握基础概念', 'achieved': True},
            {'description': '完成练习题', 'achieved': True},
            {'description': '通过单元测试', 'achieved': False}
        ]
    }
    
    process_result = assessment_system.conduct_process_assessment(
        learner_id, 
        learning_path=learning_path,
        period_days=14
    )
    print(f"  参与度得分: {process_result.scores.get('participation', 0):.1f}")
    print(f"  主动性得分: {process_result.scores.get('initiative', 0):.1f}")
    print(f"  进度得分: {process_result.scores.get('progress', 0):.1f}")
    print(f"  综合过程得分: {process_result.overall_score:.1f}")
    
    # 生成报告
    print_subsection("生成能力评估报告")
    report = assessment_system.generate_report(
        ReportType.ABILITY,
        learner_id,
        detailed=True
    )
    print(f"  报告ID: {report.report_id}")
    print(f"  报告类型: {report.report_type.value}")
    print(f"  章节数: {len(report.sections)}")
    
    # 导出报告
    output_dir = "./output"
    os.makedirs(output_dir, exist_ok=True)
    
    print_subsection("导出报告")
    
    # 导出为Markdown
    md_path = assessment_system.export_report(
        report, 
        ReportFormat.MARKDOWN, 
        f"{output_dir}/ability_report_{learner_id}.md"
    )
    print(f"  Markdown: {md_path}")
    
    # 导出为JSON
    json_path = assessment_system.export_report(
        report,
        ReportFormat.JSON,
        f"{output_dir}/ability_report_{learner_id}.json"
    )
    print(f"  JSON: {json_path}")
    
    # 导出为HTML
    html_path = assessment_system.export_report(
        report,
        ReportFormat.HTML,
        f"{output_dir}/ability_report_{learner_id}.html"
    )
    print(f"  HTML: {html_path}")
    
    # 进行增值评价（需要先设置初始能力）
    print_subsection("增值评价")
    profile.initial_ability = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=60.0,
            principle_comprehension=55.0,
            relationship_grasp=58.0
        ),
        procedural_fluency=ProceduralFluency(
            accuracy=65.0,
            efficiency=58.0,
            flexibility=55.0
        ),
        strategic_competence=StrategicCompetence(
            problem_analysis=50.0,
            strategy_formulation=52.0,
            strategy_execution=48.0
        ),
        adaptive_reasoning=AdaptiveReasoning(
            logical_thinking=55.0,
            justification_ability=50.0,
            explanation_clarity=52.0
        ),
        productive_disposition=ProductiveDisposition(
            confidence=60.0,
            persistence=65.0,
            appreciation=58.0
        )
    )
    
    value_added_result = assessment_system.conduct_value_added_assessment(
        learner_id, 
        period_days=30
    )
    print(f"  总体增值: {value_added_result.overall_score:+.1f}")
    print(f"  新掌握概念: {value_added_result.metadata.get('new_concepts', 0)}")
    
    return assessment_system, learner_id


def demo_performance_assessment():
    """演示表现性评价"""
    print_separator("演示 5: 表现性评价")
    
    assessment_system = FormalMathAssessmentSystem()
    learner_id = "student_002"
    assessment_system.register_learner(learner_id, "王五")
    
    # 模拟表现数据
    performance_data = {
        'problem_analysis': {
            'understanding_accuracy': 85.0,
            'decomposition_ability': 78.0,
            'info_identification': 82.0
        },
        'method_selection': {
            'applicability_judgment': 80.0,
            'selection_rationality': 85.0,
            'method_combination': 75.0
        },
        'execution': {
            'accuracy': 90.0,
            'efficiency': 80.0,
            'standardization': 85.0
        },
        'verification': {
            'correctness_check': 88.0,
            'rationality_check': 85.0,
            'optimization_ability': 75.0
        }
    }
    
    print_subsection("任务表现数据")
    print("  问题分析能力指标:")
    for k, v in performance_data['problem_analysis'].items():
        print(f"    {k}: {v}")
    
    result = assessment_system.conduct_performance_assessment(learner_id, performance_data)
    
    print_subsection("表现性评价结果")
    print(f"  问题分析: {result.scores.get('problem_analysis', 0):.1f}")
    print(f"  方法选择: {result.scores.get('method_selection', 0):.1f}")
    print(f"  执行操作: {result.scores.get('execution', 0):.1f}")
    print(f"  结果验证: {result.scores.get('verification', 0):.1f}")
    print(f"  综合表现得分: {result.overall_score:.1f}")
    print(f"  表现等级: {result.level.name}")


def demo_divergent_assessment():
    """演示发散思维评价"""
    print_separator("演示 6: 发散思维评价")
    
    assessment_system = FormalMathAssessmentSystem()
    learner_id = "student_003"
    assessment_system.register_learner(learner_id, "赵六")
    
    # 模拟创造性产出数据
    creative_output = {
        'idea_count': 15,
        'generation_speed': 3.5,  # 想法/分钟
        'idea_diversity': 85.0,
        'category_count': 6,
        'perspective_diversity': 80.0,
        'thinking_shifts': 4,
        'uniqueness_score': 75.0,
        'novelty_score': 80.0,
        'rarity_score': 70.0,
        'detail_level': 78.0,
        'refinement_level': 75.0,
        'depth_score': 72.0,
        'ideas': ['想法1', '想法2', '想法3', '想法4', '想法5']
    }
    
    print_subsection("创造性产出数据")
    print(f"  想法数量: {creative_output['idea_count']}")
    print(f"  生成速度: {creative_output['generation_speed']} 想法/分钟")
    print(f"  类别数: {creative_output['category_count']}")
    
    result = assessment_system.conduct_divergent_assessment(learner_id, creative_output)
    
    print_subsection("发散思维评价结果")
    print(f"  流畅性: {result.scores.get('fluency', 0):.1f}")
    print(f"  灵活性: {result.scores.get('flexibility', 0):.1f}")
    print(f"  独创性: {result.scores.get('originality', 0):.1f}")
    print(f"  精细性: {result.scores.get('elaboration', 0):.1f}")
    print(f"  创造性综合得分: {result.overall_score:.1f}")
    print(f"  创造性等级: {result.level.name}")


def demo_realtime_feedback():
    """演示实时反馈"""
    print_separator("演示 7: 实时反馈")
    
    assessment_system = FormalMathAssessmentSystem()
    learner_id = "student_004"
    assessment_system.register_learner(learner_id, "钱七")
    
    print_subsection("答题反馈场景")
    
    # 场景1: 首次答对
    feedback1 = assessment_system.generate_answer_feedback(learner_id, True, 1, 120)
    print(f"  场景1 - 首次答对:")
    print(f"    反馈: {feedback1.content}")
    
    # 场景2: 多次尝试后答对
    feedback2 = assessment_system.generate_answer_feedback(learner_id, True, 3, 300)
    print(f"\n  场景2 - 3次尝试后答对:")
    print(f"    反馈: {feedback2.content}")
    
    # 场景3: 答错
    feedback3 = assessment_system.generate_answer_feedback(learner_id, False, 1, 180)
    print(f"\n  场景3 - 答错:")
    print(f"    反馈: {feedback3.content}")
    print(f"    建议: {feedback3.suggestions}")
    
    print_subsection("学习过程实时反馈")
    
    # 模拟交互数据
    interaction_data = {
        'error_count': 4,
        'time_spent': 650,
        'attempts': 3,
        'hint_used': 0,
        'consecutive_correct': 6
    }
    
    realtime_feedback = assessment_system.generate_real_time_feedback(learner_id, interaction_data)
    if realtime_feedback:
        print(f"  检测到学习模式: {realtime_feedback.content}")
    else:
        print("  当前学习状态正常，无特殊反馈")


def demo_diagnosis_integration():
    """演示认知诊断系统对接"""
    print_separator("演示 8: 认知诊断系统对接")
    
    assessment_system = FormalMathAssessmentSystem()
    learner_id = "student_005"
    profile = assessment_system.register_learner(learner_id, "孙八")
    
    # 设置学习者数据
    profile.current_ability = MathematicalAbilityProfile(
        conceptual_understanding=ConceptualUnderstanding(
            concept_mastery=70.0,
            principle_comprehension=65.0,
            relationship_grasp=68.0
        )
    )
    profile.knowledge_state = {
        '集合': 75.0,
        '函数': 68.0,
        '数列': 55.0,
        '三角函数': 72.0,
        '向量': 60.0
    }
    
    print_subsection("学习者诊断档案")
    diagnosis_profile = assessment_system.get_learner_diagnosis_profile(learner_id)
    print(f"  学习者ID: {diagnosis_profile['learner_id']}")
    print(f"  能力档案: {diagnosis_profile['ability_profile']}")
    print(f"  知识状态: {diagnosis_profile['knowledge_state']}")
    
    # 注册诊断回调
    def diagnosis_callback(data):
        print(f"\n  [诊断回调] 接收到诊断数据: {data.get('type', 'unknown')}")
    
    assessment_system.register_diagnosis_callback(diagnosis_callback)
    
    print_subsection("触发诊断通知")
    assessment_system.notify_diagnosis_system({
        'type': 'ability_update',
        'learner_id': learner_id,
        'timestamp': datetime.now().isoformat()
    })


def main():
    """主函数"""
    print("=" * 60)
    print("  FormalMath 评估系统演示")
    print("  FormalMath Assessment System Demo")
    print("=" * 60)
    
    try:
        # 运行各个演示
        demo_basic_evaluation()
        demo_scoring_engine()
        demo_feedback_generation()
        demo_full_assessment_system()
        demo_performance_assessment()
        demo_divergent_assessment()
        demo_realtime_feedback()
        demo_diagnosis_integration()
        
        print_separator("演示完成")
        print("\n所有演示已成功完成！")
        print("生成的报告文件保存在 ./output/ 目录")
        print("\n你可以查看以下文件:")
        print("  - ability_report_*.md (Markdown格式报告)")
        print("  - ability_report_*.json (JSON格式报告)")
        print("  - ability_report_*.html (HTML格式报告)")
        
    except Exception as e:
        print(f"\n演示过程中出现错误: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
