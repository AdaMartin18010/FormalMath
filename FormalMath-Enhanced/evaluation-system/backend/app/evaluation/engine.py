"""Evaluation engine implementation."""
from typing import Dict, List, Optional, Any
from datetime import datetime, timedelta
import uuid

from sqlalchemy.orm import Session

from app.evaluation.model import EvaluationModel
from app.models.evaluation import (
    EvaluationRecord, 
    EvaluationStandard,
    LearningTrajectory,
    EvaluationType
)


class EvaluationEngine:
    """Main evaluation engine."""
    
    def __init__(self, db: Session):
        """Initialize with database session."""
        self.db = db
        self.model = EvaluationModel()
    
    def assess(
        self,
        user_id: str,
        assessments: Dict[str, float],
        evaluation_type: EvaluationType = EvaluationType.COMPREHENSIVE,
        period: Optional[str] = None,
        assessor_id: Optional[str] = None,
        notes: Optional[str] = None,
        raw_data: Optional[Dict] = None
    ) -> Dict:
        """Execute comprehensive assessment.
        
        Args:
            user_id: User ID
            assessments: Dict with dimension scores
            evaluation_type: Type of evaluation
            period: Assessment period
            assessor_id: Assessor ID
            notes: Additional notes
            raw_data: Raw assessment data
            
        Returns:
            Assessment result
        """
        # Calculate scores using model
        result = self.model.calculate_score(assessments)
        
        # Create record
        record = EvaluationRecord(
            record_id=f"EV{datetime.now().strftime('%Y%m%d%H%M%S')}{uuid.uuid4().hex[:6].upper()}",
            user_id=user_id,
            evaluation_type=evaluation_type,
            knowledge_mastery=assessments.get('knowledge_mastery', 0.0),
            problem_solving=assessments.get('problem_solving', 0.0),
            proof_ability=assessments.get('proof_ability', 0.0),
            application=assessments.get('application', 0.0),
            innovation=assessments.get('innovation', 0.0),
            total_score=result['total_score'],
            weighted_score=result['weighted_score'],
            dimension_scores=result['dimension_scores'],
            assessment_period=period,
            assessor_id=assessor_id,
            notes=notes,
            raw_data=raw_data
        )
        
        self.db.add(record)
        self.db.commit()
        self.db.refresh(record)
        
        # Update learning trajectory
        self._update_trajectory(user_id, assessments, period)
        
        return {
            'record_id': record.record_id,
            'user_id': user_id,
            'evaluation_type': evaluation_type.value,
            'scores': result,
            'created_at': record.created_at.isoformat()
        }
    
    def _update_trajectory(
        self, 
        user_id: str, 
        assessments: Dict[str, float],
        period: Optional[str] = None
    ):
        """Update learning trajectory."""
        trajectory = LearningTrajectory(
            user_id=user_id,
            record_date=datetime.utcnow(),
            period=period or datetime.utcnow().strftime("%Y-%m"),
            knowledge_mastery=assessments.get('knowledge_mastery', 0.0),
            problem_solving=assessments.get('problem_solving', 0.0),
            proof_ability=assessments.get('proof_ability', 0.0),
            application=assessments.get('application', 0.0),
            innovation=assessments.get('innovation', 0.0)
        )
        
        self.db.add(trajectory)
        self.db.commit()
    
    def get_learning_trajectory(
        self, 
        user_id: str, 
        start_date: Optional[datetime] = None,
        end_date: Optional[datetime] = None
    ) -> List[Dict]:
        """Get learning trajectory for user."""
        query = self.db.query(LearningTrajectory).filter(
            LearningTrajectory.user_id == user_id
        )
        
        if start_date:
            query = query.filter(LearningTrajectory.record_date >= start_date)
        if end_date:
            query = query.filter(LearningTrajectory.record_date <= end_date)
        
        records = query.order_by(LearningTrajectory.record_date.asc()).all()
        
        return [
            {
                'date': r.record_date.isoformat(),
                'period': r.period,
                'scores': {
                    'knowledge_mastery': r.knowledge_mastery,
                    'problem_solving': r.problem_solving,
                    'proof_ability': r.proof_ability,
                    'application': r.application,
                    'innovation': r.innovation
                },
                'value_added': r.value_added,
                'growth_rate': r.growth_rate
            }
            for r in records
        ]
    
    def calculate_growth_analysis(
        self, 
        user_id: str, 
        periods: int = 6
    ) -> Dict:
        """Calculate growth analysis over recent periods."""
        # Get recent records
        records = self.db.query(LearningTrajectory).filter(
            LearningTrajectory.user_id == user_id
        ).order_by(
            LearningTrajectory.record_date.desc()
        ).limit(periods).all()
        
        if len(records) < 2:
            return {
                'error': 'Insufficient data for growth analysis',
                'min_required': 2,
                'current': len(records)
            }
        
        # Reverse to chronological order
        records = list(reversed(records))
        
        # Calculate growth between consecutive periods
        growth_data = []
        for i in range(1, len(records)):
            current = {
                'knowledge_mastery': records[i].knowledge_mastery,
                'problem_solving': records[i].problem_solving,
                'proof_ability': records[i].proof_ability,
                'application': records[i].application,
                'innovation': records[i].innovation
            }
            previous = {
                'knowledge_mastery': records[i-1].knowledge_mastery,
                'problem_solving': records[i-1].problem_solving,
                'proof_ability': records[i-1].proof_ability,
                'application': records[i-1].application,
                'innovation': records[i-1].innovation
            }
            
            growth = self.model.calculate_growth(current, previous)
            growth_data.append({
                'period': records[i].period,
                'growth': growth
            })
        
        # Calculate overall trend
        first_record = records[0]
        last_record = records[-1]
        
        overall = self.model.calculate_growth(
            {
                'knowledge_mastery': last_record.knowledge_mastery,
                'problem_solving': last_record.problem_solving,
                'proof_ability': last_record.proof_ability,
                'application': last_record.application,
                'innovation': last_record.innovation
            },
            {
                'knowledge_mastery': first_record.knowledge_mastery,
                'problem_solving': first_record.problem_solving,
                'proof_ability': first_record.proof_ability,
                'application': first_record.application,
                'innovation': first_record.innovation
            }
        )
        
        return {
            'user_id': user_id,
            'periods_analyzed': len(records),
            'period_growth': growth_data,
            'overall_growth': overall,
            'trend_direction': 'improving' if overall['overall_growth'] > 0 else 'declining'
        }
    
    def get_evaluation_report(
        self, 
        user_id: str,
        record_id: Optional[str] = None
    ) -> Dict:
        """Generate evaluation report."""
        # Get latest or specific record
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
        
        # Get previous record for comparison
        previous = self.db.query(EvaluationRecord).filter(
            EvaluationRecord.user_id == user_id,
            EvaluationRecord.id < record.id
        ).order_by(EvaluationRecord.created_at.desc()).first()
        
        current_scores = {
            'knowledge_mastery': record.knowledge_mastery,
            'problem_solving': record.problem_solving,
            'proof_ability': record.proof_ability,
            'application': record.application,
            'innovation': record.innovation
        }
        
        report = {
            'record_id': record.record_id,
            'user_id': user_id,
            'evaluation_type': record.evaluation_type.value,
            'assessment_date': record.created_at.isoformat(),
            'scores': {
                'total': record.total_score,
                'weighted': record.weighted_score,
                'grade': self.model._calculate_grade(record.weighted_score),
                'dimensions': record.dimension_scores
            },
            'strengths_weaknesses': self.model.identify_strengths_weaknesses(
                current_scores
            ),
            'feedback': record.feedback.summary if record.feedback else None
        }
        
        if previous:
            previous_scores = {
                'knowledge_mastery': previous.knowledge_mastery,
                'problem_solving': previous.problem_solving,
                'proof_ability': previous.proof_ability,
                'application': previous.application,
                'innovation': previous.innovation
            }
            report['growth'] = self.model.calculate_growth(
                current_scores, previous_scores
            )
        
        return report
    
    def get_class_comparison(
        self, 
        user_id: str, 
        class_user_ids: List[str]
    ) -> Dict:
        """Compare user to class average."""
        # Get user's latest scores
        user_record = self.db.query(EvaluationRecord).filter(
            EvaluationRecord.user_id == user_id
        ).order_by(EvaluationRecord.created_at.desc()).first()
        
        if not user_record:
            return {'error': 'No user record found'}
        
        # Get class average
        class_records = self.db.query(EvaluationRecord).filter(
            EvaluationRecord.user_id.in_(class_user_ids)
        ).order_by(
            EvaluationRecord.user_id,
            EvaluationRecord.created_at.desc()
        ).distinct(EvaluationRecord.user_id).all()
        
        if not class_records:
            return {'error': 'No class data available'}
        
        # Calculate class average
        avg_scores = {}
        for dim in ['knowledge_mastery', 'problem_solving', 'proof_ability', 
                    'application', 'innovation']:
            scores = [getattr(r, dim) for r in class_records]
            avg_scores[dim] = sum(scores) / len(scores)
        
        user_scores = {
            'knowledge_mastery': user_record.knowledge_mastery,
            'problem_solving': user_record.problem_solving,
            'proof_ability': user_record.proof_ability,
            'application': user_record.application,
            'innovation': user_record.innovation
        }
        
        return {
            'user_id': user_id,
            'class_size': len(class_records),
            'user_scores': user_scores,
            'class_average': avg_scores,
            'comparison': self.model.compare_to_benchmark(user_scores, avg_scores),
            'rank_percentile': self._calculate_rank(user_scores, class_records)
        }
    
    def _calculate_rank(
        self, 
        user_scores: Dict[str, float], 
        class_records: List[EvaluationRecord]
    ) -> float:
        """Calculate user's percentile rank in class."""
        user_weighted = sum(
            user_scores.get(dim, 0) * weight 
            for dim, weight in self.model.dimensions.items()
        )
        
        class_weighted = []
        for record in class_records:
            scores = {
                'knowledge_mastery': record.knowledge_mastery,
                'problem_solving': record.problem_solving,
                'proof_ability': record.proof_ability,
                'application': record.application,
                'innovation': record.innovation
            }
            weighted = sum(
                scores.get(dim, 0) * weight 
                for dim, weight in self.model.dimensions.items()
            )
            class_weighted.append(weighted)
        
        # Calculate percentile
        below_count = sum(1 for score in class_weighted if score < user_weighted)
        return round(below_count / len(class_weighted) * 100, 2)
