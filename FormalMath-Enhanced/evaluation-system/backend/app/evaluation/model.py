"""Five-dimensional evaluation model."""
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
import math


@dataclass
class DimensionScore:
    """Score for a single dimension."""
    name: str
    score: float
    weight: float
    sub_scores: Optional[Dict[str, float]] = None
    
    def weighted_score(self) -> float:
        """Calculate weighted score."""
        return self.score * self.weight


class EvaluationModel:
    """Five-dimensional evaluation model.
    
    Dimensions:
    - knowledge_mastery: 知识掌握度 (30%)
    - problem_solving: 问题解决能力 (25%)  
    - proof_ability: 证明能力 (20%)
    - application: 应用能力 (15%)
    - innovation: 创新思维 (10%)
    """
    
    DEFAULT_DIMENSIONS = {
        'knowledge_mastery': 0.30,  # 知识掌握度 30%
        'problem_solving': 0.25,    # 问题解决 25%
        'proof_ability': 0.20,      # 证明能力 20%
        'application': 0.15,        # 应用能力 15%
        'innovation': 0.10          # 创新思维 10%
    }
    
    DIMENSION_NAMES_CN = {
        'knowledge_mastery': '知识掌握度',
        'problem_solving': '问题解决能力',
        'proof_ability': '证明能力',
        'application': '应用能力',
        'innovation': '创新思维'
    }
    
    def __init__(self, custom_weights: Optional[Dict[str, float]] = None):
        """Initialize with optional custom weights."""
        self.dimensions = custom_weights or self.DEFAULT_DIMENSIONS.copy()
        self._validate_weights()
    
    def _validate_weights(self):
        """Validate that weights sum to 1.0."""
        total = sum(self.dimensions.values())
        if not math.isclose(total, 1.0, rel_tol=1e-5):
            # Normalize weights
            self.dimensions = {
                k: v / total for k, v in self.dimensions.items()
            }
    
    def calculate_score(self, assessments: Dict[str, float]) -> Dict:
        """Calculate weighted total score.
        
        Args:
            assessments: Dict with dimension names as keys and scores (0-100) as values
            
        Returns:
            Dict with total_score, weighted_scores, and dimension_details
        """
        if not assessments:
            return {
                'total_score': 0.0,
                'weighted_score': 0.0,
                'dimension_scores': {},
                'grade': 'F'
            }
        
        dimension_scores = {}
        weighted_total = 0.0
        
        for dim_name, weight in self.dimensions.items():
            score = assessments.get(dim_name, 0.0)
            # Ensure score is in 0-100 range
            score = max(0.0, min(100.0, score))
            weighted = score * weight
            
            dimension_scores[dim_name] = {
                'name': self.DIMENSION_NAMES_CN.get(dim_name, dim_name),
                'score': round(score, 2),
                'weight': weight,
                'weighted_score': round(weighted, 2),
                'percentage': round(score, 2)
            }
            weighted_total += weighted
        
        # Calculate simple average of provided scores
        raw_total = sum(
            assessments.get(dim, 0.0) 
            for dim in self.dimensions.keys()
        ) / len(self.dimensions)
        
        return {
            'total_score': round(raw_total, 2),
            'weighted_score': round(weighted_total, 2),
            'dimension_scores': dimension_scores,
            'grade': self._calculate_grade(weighted_total),
            'percentile': self._estimate_percentile(weighted_total)
        }
    
    def _calculate_grade(self, score: float) -> str:
        """Calculate letter grade from score."""
        if score >= 90:
            return 'A'
        elif score >= 80:
            return 'B'
        elif score >= 70:
            return 'C'
        elif score >= 60:
            return 'D'
        else:
            return 'F'
    
    def _estimate_percentile(self, score: float) -> int:
        """Estimate percentile from score (simplified)."""
        # Simplified estimation
        if score >= 90:
            return 90 + int((score - 90) * 0.5)
        elif score >= 80:
            return 70 + int((score - 80) * 2)
        elif score >= 70:
            return 50 + int((score - 70) * 2)
        elif score >= 60:
            return 30 + int((score - 60) * 2)
        else:
            return max(0, int(score * 0.5))
    
    def calculate_growth(
        self, 
        current: Dict[str, float], 
        previous: Dict[str, float]
    ) -> Dict:
        """Calculate growth between two assessments.
        
        Args:
            current: Current assessment scores
            previous: Previous assessment scores
            
        Returns:
            Growth analysis
        """
        growth = {}
        total_growth = 0.0
        
        for dim_name in self.dimensions.keys():
            curr = current.get(dim_name, 0.0)
            prev = previous.get(dim_name, 0.0)
            
            absolute_growth = curr - prev
            relative_growth = (absolute_growth / prev * 100) if prev > 0 else 0.0
            
            growth[dim_name] = {
                'current': round(curr, 2),
                'previous': round(prev, 2),
                'absolute_growth': round(absolute_growth, 2),
                'relative_growth': round(relative_growth, 2),
                'trend': 'up' if absolute_growth > 0 else ('down' if absolute_growth < 0 else 'stable')
            }
            total_growth += absolute_growth * self.dimensions[dim_name]
        
        return {
            'dimension_growth': growth,
            'overall_growth': round(total_growth, 2),
            'growth_rate': round(total_growth / sum(previous.values()) * 100, 2) if sum(previous.values()) > 0 else 0.0
        }
    
    def compare_to_benchmark(
        self, 
        scores: Dict[str, float], 
        benchmark: Dict[str, float]
    ) -> Dict:
        """Compare scores to benchmark/class average.
        
        Args:
            scores: Individual scores
            benchmark: Benchmark scores (e.g., class average)
            
        Returns:
            Comparison analysis
        """
        comparison = {}
        
        for dim_name in self.dimensions.keys():
            score = scores.get(dim_name, 0.0)
            bench = benchmark.get(dim_name, 0.0)
            diff = score - bench
            
            comparison[dim_name] = {
                'score': round(score, 2),
                'benchmark': round(bench, 2),
                'difference': round(diff, 2),
                'percent_diff': round(diff / bench * 100, 2) if bench > 0 else 0.0,
                'status': 'above' if diff > 0 else ('below' if diff < 0 else 'equal')
            }
        
        return comparison
    
    def identify_strengths_weaknesses(
        self, 
        scores: Dict[str, float],
        threshold_high: float = 80.0,
        threshold_low: float = 60.0
    ) -> Dict:
        """Identify strengths and weaknesses.
        
        Args:
            scores: Assessment scores
            threshold_high: Score threshold for strengths
            threshold_low: Score threshold for weaknesses
            
        Returns:
            Dict with strengths and weaknesses lists
        """
        strengths = []
        weaknesses = []
        
        for dim_name, score in scores.items():
            dim_info = {
                'dimension': dim_name,
                'name': self.DIMENSION_NAMES_CN.get(dim_name, dim_name),
                'score': score,
                'weight': self.dimensions.get(dim_name, 0.2)
            }
            
            if score >= threshold_high:
                strengths.append(dim_info)
            elif score <= threshold_low:
                weaknesses.append(dim_info)
        
        # Sort by score
        strengths.sort(key=lambda x: x['score'], reverse=True)
        weaknesses.sort(key=lambda x: x['score'])
        
        return {
            'strengths': strengths,
            'weaknesses': weaknesses,
            'strongest': strengths[0] if strengths else None,
            'weakest': weaknesses[0] if weaknesses else None
        }
