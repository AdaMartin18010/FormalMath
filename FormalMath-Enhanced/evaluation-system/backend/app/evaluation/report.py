"""Report generation module."""
from typing import Dict, List, Optional, Any
from datetime import datetime
import json
import io
from pathlib import Path

try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import cm
    from reportlab.platypus import (
        SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
        Image, PageBreak, ListFlowable, ListItem
    )
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

from sqlalchemy.orm import Session

from app.models.evaluation import EvaluationRecord, FeedbackTemplate, LearningTrajectory
from app.evaluation.model import EvaluationModel


class ReportGenerator:
    """Generate evaluation reports in various formats."""
    
    def __init__(self, db: Session):
        """Initialize with database session."""
        self.db = db
        self.model = EvaluationModel()
    
    def generate_json_report(
        self,
        user_id: str,
        record_id: Optional[str] = None,
        include_history: bool = True,
        include_comparison: bool = False
    ) -> Dict:
        """Generate comprehensive JSON report.
        
        Args:
            user_id: User ID
            record_id: Specific record ID or None for latest
            include_history: Include learning trajectory
            include_comparison: Include class comparison
            
        Returns:
            Report data as dict
        """
        # Get evaluation record
        if record_id:
            record = self.db.query(EvaluationRecord).filter(
                EvaluationRecord.record_id == record_id
            ).first()
        else:
            record = self.db.query(EvaluationRecord).filter(
                EvaluationRecord.user_id == user_id
            ).order_by(EvaluationRecord.created_at.desc()).first()
        
        if not record:
            return {'error': 'No evaluation record found'}
        
        # Get feedback
        feedback = self.db.query(FeedbackTemplate).filter(
            FeedbackTemplate.evaluation_id == record.id
        ).first()
        
        # Build report
        report = {
            'report_metadata': {
                'report_id': f"RPT{datetime.now().strftime('%Y%m%d%H%M%S')}",
                'user_id': user_id,
                'record_id': record.record_id,
                'generated_at': datetime.utcnow().isoformat(),
                'report_type': 'comprehensive_evaluation'
            },
            'executive_summary': self._generate_executive_summary(record, feedback),
            'detailed_scores': self._generate_detailed_scores(record),
            'dimension_analysis': self._generate_dimension_analysis(record),
            'strengths_and_improvements': self._generate_strengths_improvements(record),
        }
        
        if feedback:
            report['feedback'] = {
                'summary': feedback.summary,
                'strengths': feedback.strengths,
                'weaknesses': feedback.weaknesses,
                'suggestions': feedback.suggestions,
                'recommended_path': feedback.recommended_path
            }
        
        if include_history:
            report['learning_trajectory'] = self._get_learning_trajectory(user_id)
        
        return report
    
    def _generate_executive_summary(
        self, 
        record: EvaluationRecord, 
        feedback: Optional[FeedbackTemplate]
    ) -> Dict:
        """Generate executive summary."""
        return {
            'evaluation_date': record.created_at.isoformat(),
            'evaluation_type': record.evaluation_type.value,
            'overall_score': record.weighted_score,
            'grade': self.model._calculate_grade(record.weighted_score),
            'percentile': self.model._estimate_percentile(record.weighted_score),
            'overall_assessment': feedback.summary if feedback else 'N/A',
            'key_highlights': [
                f"五维综合得分: {record.weighted_score:.1f}",
                f"评价等级: {self.model._calculate_grade(record.weighted_score)}",
                f"评估周期: {record.assessment_period or 'N/A'}"
            ]
        }
    
    def _generate_detailed_scores(self, record: EvaluationRecord) -> Dict:
        """Generate detailed score breakdown."""
        return {
            'total_score': record.total_score,
            'weighted_score': record.weighted_score,
            'dimension_scores': {
                'knowledge_mastery': {
                    'score': record.knowledge_mastery,
                    'weight': 0.30,
                    'weighted_score': record.knowledge_mastery * 0.30,
                    'name': '知识掌握度'
                },
                'problem_solving': {
                    'score': record.problem_solving,
                    'weight': 0.25,
                    'weighted_score': record.problem_solving * 0.25,
                    'name': '问题解决能力'
                },
                'proof_ability': {
                    'score': record.proof_ability,
                    'weight': 0.20,
                    'weighted_score': record.proof_ability * 0.20,
                    'name': '证明能力'
                },
                'application': {
                    'score': record.application,
                    'weight': 0.15,
                    'weighted_score': record.application * 0.15,
                    'name': '应用能力'
                },
                'innovation': {
                    'score': record.innovation,
                    'weight': 0.10,
                    'weighted_score': record.innovation * 0.10,
                    'name': '创新思维'
                }
            },
            'grade_distribution': self._calculate_grade_distribution(record)
        }
    
    def _calculate_grade_distribution(self, record: EvaluationRecord) -> Dict:
        """Calculate grade distribution across dimensions."""
        scores = [
            record.knowledge_mastery,
            record.problem_solving,
            record.proof_ability,
            record.application,
            record.innovation
        ]
        
        distribution = {'A': 0, 'B': 0, 'C': 0, 'D': 0, 'F': 0}
        for score in scores:
            grade = self.model._calculate_grade(score)
            distribution[grade] += 1
        
        return distribution
    
    def _generate_dimension_analysis(self, record: EvaluationRecord) -> Dict:
        """Generate analysis for each dimension."""
        scores = {
            'knowledge_mastery': record.knowledge_mastery,
            'problem_solving': record.problem_solving,
            'proof_ability': record.proof_ability,
            'application': record.application,
            'innovation': record.innovation
        }
        
        analysis = {}
        for dim, score in scores.items():
            cn_name = self.model.DIMENSION_NAMES_CN.get(dim, dim)
            
            if score >= 90:
                level = 'excellent'
                description = f'{cn_name}表现卓越，展现了深厚的理解和应用能力。'
            elif score >= 80:
                level = 'good'
                description = f'{cn_name}表现良好，具备扎实的基础。'
            elif score >= 70:
                level = 'satisfactory'
                description = f'{cn_name}表现中等，掌握了基本概念但仍有提升空间。'
            elif score >= 60:
                level = 'needs_improvement'
                description = f'{cn_name}需要加强，建议系统复习相关知识。'
            else:
                level = 'critical'
                description = f'{cn_name}需要重点关注，建议制定专项学习计划。'
            
            analysis[dim] = {
                'name': cn_name,
                'score': score,
                'level': level,
                'description': description,
                'recommendations': self._get_dimension_recommendations(dim, score)
            }
        
        return analysis
    
    def _get_dimension_recommendations(self, dimension: str, score: float) -> List[str]:
        """Get recommendations for a dimension."""
        recommendations = {
            'knowledge_mastery': [
                "系统复习基础概念和定理",
                "构建知识图谱，梳理概念间联系",
                "完成更多基础练习题"
            ],
            'problem_solving': [
                "学习多种解题策略",
                "分析典型例题的解题思路",
                "进行限时解题训练"
            ],
            'proof_ability': [
                "研读经典定理的证明过程",
                "练习书写规范的证明步骤",
                "尝试多种证明方法"
            ],
            'application': [
                "寻找数学在实际中的应用场景",
                "完成更多应用型题目",
                "参与数学建模活动"
            ],
            'innovation': [
                "尝试开放性问题",
                "探索概念之间的深层联系",
                "阅读数学史和前沿论文"
            ]
        }
        
        return recommendations.get(dimension, [])
    
    def _generate_strengths_improvements(self, record: EvaluationRecord) -> Dict:
        """Generate strengths and improvements analysis."""
        scores = {
            'knowledge_mastery': record.knowledge_mastery,
            'problem_solving': record.problem_solving,
            'proof_ability': record.proof_ability,
            'application': record.application,
            'innovation': record.innovation
        }
        
        return self.model.identify_strengths_weaknesses(scores)
    
    def _get_learning_trajectory(self, user_id: str) -> Dict:
        """Get learning trajectory data."""
        records = self.db.query(LearningTrajectory).filter(
            LearningTrajectory.user_id == user_id
        ).order_by(LearningTrajectory.record_date.asc()).limit(12).all()
        
        if not records:
            return {'error': 'No trajectory data available'}
        
        trajectory_data = []
        for r in records:
            trajectory_data.append({
                'date': r.record_date.isoformat(),
                'period': r.period,
                'scores': {
                    'knowledge_mastery': r.knowledge_mastery,
                    'problem_solving': r.problem_solving,
                    'proof_ability': r.proof_ability,
                    'application': r.application,
                    'innovation': r.innovation
                }
            })
        
        # Calculate trend
        if len(records) >= 2:
            first = records[0]
            last = records[-1]
            
            overall_growth = (
                (last.knowledge_mastery + last.problem_solving + 
                 last.proof_ability + last.application + last.innovation) -
                (first.knowledge_mastery + first.problem_solving +
                 first.proof_ability + first.application + first.innovation)
            ) / 5
            
            trend = 'improving' if overall_growth > 0 else 'declining'
        else:
            trend = 'stable'
            overall_growth = 0
        
        return {
            'data_points': len(records),
            'trajectory': trajectory_data,
            'overall_trend': trend,
            'overall_growth': round(overall_growth, 2)
        }
    
    def generate_pdf_report(
        self,
        user_id: str,
        record_id: Optional[str] = None
    ) -> Optional[bytes]:
        """Generate PDF report.
        
        Args:
            user_id: User ID
            record_id: Specific record ID
            
        Returns:
            PDF content as bytes
        """
        if not REPORTLAB_AVAILABLE:
            return None
        
        # Get data
        report_data = self.generate_json_report(user_id, record_id)
        
        if 'error' in report_data:
            return None
        
        # Create PDF buffer
        buffer = io.BytesIO()
        doc = SimpleDocTemplate(
            buffer,
            pagesize=A4,
            rightMargin=2*cm,
            leftMargin=2*cm,
            topMargin=2*cm,
            bottomMargin=2*cm
        )
        
        # Container for elements
        elements = []
        styles = getSampleStyleSheet()
        
        # Title
        title_style = ParagraphStyle(
            'CustomTitle',
            parent=styles['Heading1'],
            fontSize=20,
            textColor=colors.HexColor('#1a365d'),
            spaceAfter=30
        )
        elements.append(Paragraph("数学能力评估报告", title_style))
        elements.append(Spacer(1, 20))
        
        # Executive Summary
        elements.append(Paragraph("执行摘要", styles['Heading2']))
        summary = report_data['executive_summary']
        summary_text = f"""
        <b>评估日期:</b> {summary['evaluation_date'][:10]}<br/>
        <b>综合得分:</b> {summary['overall_score']:.1f}<br/>
        <b>评价等级:</b> {summary['grade']}<br/>
        <b>整体评价:</b> {summary['overall_assessment']}
        """
        elements.append(Paragraph(summary_text, styles['Normal']))
        elements.append(Spacer(1, 20))
        
        # Scores Table
        elements.append(Paragraph("详细得分", styles['Heading2']))
        scores = report_data['detailed_scores']['dimension_scores']
        
        table_data = [['维度', '得分', '权重', '加权得分']]
        for dim, data in scores.items():
            table_data.append([
                data['name'],
                f"{data['score']:.1f}",
                f"{data['weight']*100:.0f}%",
                f"{data['weighted_score']:.1f}"
            ])
        
        table = Table(table_data)
        table.setStyle(TableStyle([
            ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#1a365d')),
            ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
            ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, 0), 12),
            ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
            ('BACKGROUND', (0, 1), (-1, -1), colors.beige),
            ('GRID', (0, 0), (-1, -1), 1, colors.black)
        ]))
        elements.append(table)
        elements.append(Spacer(1, 30))
        
        # Build PDF
        doc.build(elements)
        pdf_content = buffer.getvalue()
        buffer.close()
        
        return pdf_content
    
    def save_report(
        self,
        user_id: str,
        record_id: Optional[str] = None,
        format: str = 'json',
        output_path: Optional[str] = None
    ) -> str:
        """Save report to file.
        
        Args:
            user_id: User ID
            record_id: Specific record ID
            format: 'json' or 'pdf'
            output_path: Optional output path
            
        Returns:
            Path to saved file
        """
        if output_path is None:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            output_path = f"reports/evaluation_report_{user_id}_{timestamp}.{format}"
        
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        
        if format == 'json':
            report = self.generate_json_report(user_id, record_id)
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(report, f, ensure_ascii=False, indent=2)
        
        elif format == 'pdf':
            pdf_content = self.generate_pdf_report(user_id, record_id)
            if pdf_content:
                with open(output_path, 'wb') as f:
                    f.write(pdf_content)
            else:
                return "Error: PDF generation failed"
        
        return output_path
