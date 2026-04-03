"""Feedback generation engine."""
from typing import Dict, List, Optional, Any
import uuid
from datetime import datetime

from sqlalchemy.orm import Session

from app.models.evaluation import FeedbackTemplate, EvaluationRecord
from app.evaluation.model import EvaluationModel


class FeedbackEngine:
    """Generate personalized feedback based on evaluation results."""
    
    # Feedback templates for different scenarios
    FEEDBACK_TEMPLATES = {
        'strength': {
            'excellent': [
                "您在{dimension}方面表现卓越，展现了深厚的功底。",
                "您在{dimension}上的表现令人印象深刻，继续保持！",
                "您在{dimension}方面具有明显优势，可以作为进一步发展的基础。"
            ],
            'good': [
                "您在{dimension}方面表现良好，有较强的能力。",
                "您在{dimension}上取得了不错的成绩，仍有提升空间。"
            ]
        },
        'improvement': {
            'needed': [
                "建议加强{dimension}方面的练习，这是当前的主要提升点。",
                "在{dimension}方面还有较大提升空间，建议制定专项学习计划。",
                "针对{dimension}，建议多进行相关练习和反思。"
            ],
            'moderate': [
                "{dimension}方面可以继续优化，建议保持练习频率。",
                "在{dimension}上有一定基础，通过针对性训练可以进一步提升。"
            ]
        },
        'growth': {
            'significant': [
                "与上次评估相比，您在{dimension}方面取得了显著进步！",
                "恭喜！您在{dimension}上的提升非常明显，努力得到了回报。"
            ],
            'steady': [
                "您在{dimension}方面保持了稳定进步，继续努力！",
                "{dimension}持续改进中，保持当前的学习节奏。"
            ]
        }
    }
    
    LEARNING_SUGGESTIONS = {
        'knowledge_mastery': [
            "系统复习相关概念的定义和性质",
            "通过概念图梳理知识结构",
            "完成基础练习题巩固理解",
            "阅读相关教材和参考资料"
        ],
        'problem_solving': [
            "多做各类应用题，培养解题思路",
            "学习并总结常见的解题策略",
            "尝试一题多解，拓展思维方式",
            "分析错题，总结解题规律"
        ],
        'proof_ability': [
            "学习常见的证明方法和技巧",
            "研读经典定理的证明过程",
            "尝试自己证明一些基本命题",
            "练习书写规范的证明步骤"
        ],
        'application': [
            "寻找数学在实际生活中的应用场景",
            "尝试用数学方法解决实际问题",
            "参与数学建模活动",
            "阅读数学应用案例"
        ],
        'innovation': [
            "尝试提出新的问题或猜想",
            "探索不同数学概念之间的联系",
            "参加数学竞赛或创新项目",
            "阅读数学史，了解概念的发展过程"
        ]
    }
    
    RECOMMENDED_RESOURCES = {
        'knowledge_mastery': [
            {'type': 'video', 'title': '基础概念精讲', 'difficulty': '基础'},
            {'type': 'practice', 'title': '概念理解专项练习', 'difficulty': '基础'},
            {'type': 'reading', 'title': '教材重点章节', 'difficulty': '基础'}
        ],
        'problem_solving': [
            {'type': 'video', 'title': '解题策略与方法', 'difficulty': '进阶'},
            {'type': 'practice', 'title': '综合应用题集', 'difficulty': '进阶'},
            {'type': 'interactive', 'title': '智能解题训练', 'difficulty': '自适应'}
        ],
        'proof_ability': [
            {'type': 'video', 'title': '数学证明方法', 'difficulty': '进阶'},
            {'type': 'practice', 'title': '证明题专项训练', 'difficulty': '进阶'},
            {'type': 'reading', 'title': '经典定理证明选读', 'difficulty': '高级'}
        ],
        'application': [
            {'type': 'project', 'title': '数学应用项目', 'difficulty': '进阶'},
            {'type': 'case', 'title': '实际案例分析', 'difficulty': '进阶'},
            {'type': 'interactive', 'title': '建模工具使用', 'difficulty': '进阶'}
        ],
        'innovation': [
            {'type': 'project', 'title': '开放性问题探索', 'difficulty': '高级'},
            {'type': 'reading', 'title': '数学前沿介绍', 'difficulty': '高级'},
            {'type': 'competition', 'title': '数学竞赛训练', 'difficulty': '高级'}
        ]
    }
    
    def __init__(self, db: Session):
        """Initialize with database session."""
        self.db = db
        self.model = EvaluationModel()
    
    def generate_feedback(
        self,
        user_id: str,
        record_id: str,
        custom_template: Optional[str] = None
    ) -> Dict:
        """Generate personalized feedback.
        
        Args:
            user_id: User ID
            record_id: Evaluation record ID
            custom_template: Optional custom template name
            
        Returns:
            Generated feedback
        """
        # Get evaluation record
        record = self.db.query(EvaluationRecord).filter(
            EvaluationRecord.record_id == record_id
        ).first()
        
        if not record:
            return {'error': 'Evaluation record not found'}
        
        # Get previous record for growth analysis
        previous = self.db.query(EvaluationRecord).filter(
            EvaluationRecord.user_id == user_id,
            EvaluationRecord.id < record.id
        ).order_by(EvaluationRecord.created_at.desc()).first()
        
        scores = {
            'knowledge_mastery': record.knowledge_mastery,
            'problem_solving': record.problem_solving,
            'proof_ability': record.proof_ability,
            'application': record.application,
            'innovation': record.innovation
        }
        
        # Analyze strengths and weaknesses
        analysis = self.model.identify_strengths_weaknesses(scores)
        
        # Generate feedback content
        strengths_feedback = self._generate_strengths_feedback(analysis['strengths'])
        weaknesses_feedback = self._generate_weaknesses_feedback(analysis['weaknesses'])
        
        # Generate growth feedback if previous record exists
        growth_feedback = []
        if previous:
            previous_scores = {
                'knowledge_mastery': previous.knowledge_mastery,
                'problem_solving': previous.problem_solving,
                'proof_ability': previous.proof_ability,
                'application': previous.application,
                'innovation': previous.innovation
            }
            growth = self.model.calculate_growth(scores, previous_scores)
            growth_feedback = self._generate_growth_feedback(growth)
        
        # Generate summary
        summary = self._generate_summary(
            scores, analysis, record.weighted_score
        )
        
        # Generate suggestions
        suggestions = self._generate_suggestions(analysis['weaknesses'])
        
        # Generate learning path
        recommended_path = self._generate_learning_path(analysis)
        
        # Create feedback record
        feedback = FeedbackTemplate(
            feedback_id=f"FB{datetime.now().strftime('%Y%m%d%H%M%S')}{uuid.uuid4().hex[:6].upper()}",
            evaluation_id=record.id,
            user_id=user_id,
            summary=summary,
            strengths=[s['dimension'] for s in analysis['strengths']],
            weaknesses=[w['dimension'] for w in analysis['weaknesses']],
            suggestions=suggestions,
            dimension_feedback={
                'strengths': strengths_feedback,
                'improvements': weaknesses_feedback,
                'growth': growth_feedback
            },
            recommended_resources=self._get_recommended_resources(analysis),
            recommended_path=recommended_path,
            generated_by='auto',
            template_used=custom_template or 'standard'
        )
        
        self.db.add(feedback)
        self.db.commit()
        self.db.refresh(feedback)
        
        return {
            'feedback_id': feedback.feedback_id,
            'user_id': user_id,
            'record_id': record_id,
            'summary': summary,
            'strengths': analysis['strengths'],
            'weaknesses': analysis['weaknesses'],
            'suggestions': suggestions,
            'dimension_feedback': feedback.dimension_feedback,
            'recommended_resources': feedback.recommended_resources,
            'recommended_path': recommended_path,
            'generated_at': feedback.created_at.isoformat()
        }
    
    def _generate_strengths_feedback(self, strengths: List[Dict]) -> List[str]:
        """Generate feedback for strengths."""
        import random
        feedback = []
        for strength in strengths:
            dim_name = self.model.DIMENSION_NAMES_CN.get(
                strength['dimension'], strength['dimension']
            )
            if strength['score'] >= 90:
                template = random.choice(
                    self.FEEDBACK_TEMPLATES['strength']['excellent']
                )
            else:
                template = random.choice(
                    self.FEEDBACK_TEMPLATES['strength']['good']
                )
            feedback.append(template.format(dimension=dim_name))
        return feedback
    
    def _generate_weaknesses_feedback(self, weaknesses: List[Dict]) -> List[str]:
        """Generate feedback for areas to improve."""
        import random
        feedback = []
        for weakness in weaknesses:
            dim_name = self.model.DIMENSION_NAMES_CN.get(
                weakness['dimension'], weakness['dimension']
            )
            if weakness['score'] < 50:
                template = random.choice(
                    self.FEEDBACK_TEMPLATES['improvement']['needed']
                )
            else:
                template = random.choice(
                    self.FEEDBACK_TEMPLATES['improvement']['moderate']
                )
            feedback.append(template.format(dimension=dim_name))
        return feedback
    
    def _generate_growth_feedback(self, growth: Dict) -> List[str]:
        """Generate feedback for growth."""
        import random
        feedback = []
        for dim_name, data in growth['dimension_growth'].items():
            if data['absolute_growth'] > 5:
                cn_name = self.model.DIMENSION_NAMES_CN.get(dim_name, dim_name)
                template = random.choice(
                    self.FEEDBACK_TEMPLATES['growth']['significant']
                )
                feedback.append(template.format(dimension=cn_name))
        return feedback
    
    def _generate_summary(
        self, 
        scores: Dict, 
        analysis: Dict, 
        weighted_score: float
    ) -> str:
        """Generate overall summary."""
        parts = []
        
        # Overall assessment
        if weighted_score >= 90:
            parts.append("您的综合表现卓越，展现了优秀的数学素养。")
        elif weighted_score >= 80:
            parts.append("您的综合表现良好，具备扎实的数学基础。")
        elif weighted_score >= 70:
            parts.append("您的综合表现中等，有稳定的基础但仍有提升空间。")
        else:
            parts.append("您的综合表现需要加强，建议制定系统学习计划。")
        
        # Strengths
        if analysis['strengths']:
            strongest = analysis['strongest']
            cn_name = self.model.DIMENSION_NAMES_CN.get(
                strongest['dimension'], strongest['dimension']
            )
            parts.append(f"您在{cn_name}方面表现最为突出。")
        
        # Weaknesses
        if analysis['weaknesses']:
            weakest = analysis['weakest']
            cn_name = self.model.DIMENSION_NAMES_CN.get(
                weakest['dimension'], weakest['dimension']
            )
            parts.append(f"建议重点加强{cn_name}方面的学习。")
        
        return "".join(parts)
    
    def _generate_suggestions(self, weaknesses: List[Dict]) -> List[Dict]:
        """Generate learning suggestions."""
        suggestions = []
        for weakness in weaknesses[:3]:  # Top 3 weaknesses
            dim = weakness['dimension']
            cn_name = self.model.DIMENSION_NAMES_CN.get(dim, dim)
            
            suggestions.append({
                'dimension': dim,
                'dimension_name': cn_name,
                'priority': 'high' if weakness['score'] < 50 else 'medium',
                'actions': self.LEARNING_SUGGESTIONS.get(dim, []),
                'target_score': min(weakness['score'] + 15, 90)
            })
        return suggestions
    
    def _get_recommended_resources(self, analysis: Dict) -> List[Dict]:
        """Get recommended learning resources."""
        resources = []
        
        # Resources for weak areas
        for weakness in analysis['weaknesses'][:2]:
            dim = weakness['dimension']
            resources.extend(self.RECOMMENDED_RESOURCES.get(dim, []))
        
        # Resources for strongest area (advanced)
        if analysis['strengths']:
            strongest = analysis['strengths'][0]['dimension']
            advanced_resources = [
                r for r in self.RECOMMENDED_RESOURCES.get(strongest, [])
                if r.get('difficulty') in ['高级', '进阶']
            ]
            resources.extend(advanced_resources[:2])
        
        return resources
    
    def _generate_learning_path(self, analysis: Dict) -> Dict:
        """Generate recommended learning path."""
        phases = []
        
        # Phase 1: Address weaknesses
        if analysis['weaknesses']:
            phases.append({
                'phase': 1,
                'name': '基础巩固',
                'duration': '2-3周',
                'focus': [w['dimension'] for w in analysis['weaknesses'][:2]],
                'objectives': ['弥补薄弱环节', '夯实基础']
            })
        
        # Phase 2: Maintain strengths
        if analysis['strengths']:
            phases.append({
                'phase': 2,
                'name': '优势强化',
                'duration': '2周',
                'focus': [s['dimension'] for s in analysis['strengths'][:2]],
                'objectives': ['保持优势领域', '拓展深度']
            })
        
        # Phase 3: Comprehensive
        phases.append({
            'phase': 3,
            'name': '综合提升',
            'duration': '3-4周',
            'focus': ['knowledge_mastery', 'problem_solving', 'application'],
            'objectives': ['提升综合能力', '强化应用']
        })
        
        return {
            'total_duration': '7-9周',
            'phases': phases,
            'expected_outcome': '五维能力均衡发展，综合得分提升10-15分'
        }
    
    def get_feedback_history(
        self, 
        user_id: str, 
        limit: int = 10
    ) -> List[Dict]:
        """Get feedback history for user."""
        feedbacks = self.db.query(FeedbackTemplate).filter(
            FeedbackTemplate.user_id == user_id
        ).order_by(
            FeedbackTemplate.created_at.desc()
        ).limit(limit).all()
        
        return [
            {
                'feedback_id': f.feedback_id,
                'evaluation_id': f.evaluation_id,
                'summary': f.summary,
                'strengths': f.strengths,
                'weaknesses': f.weaknesses,
                'created_at': f.created_at.isoformat()
            }
            for f in feedbacks
        ]
