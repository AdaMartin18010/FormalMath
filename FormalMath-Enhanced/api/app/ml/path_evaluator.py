"""
路径评估模块
评估学习路径的效果和质量
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
import json


@dataclass
class PathMetrics:
    """路径指标"""
    path_id: str
    
    # 效率指标
    completion_rate: float = 0.0
    time_efficiency: float = 0.0
    learning_velocity: float = 0.0
    
    # 效果指标
    mastery_improvement: float = 0.0
    retention_rate: float = 0.0
    transfer_score: float = 0.0
    
    # 体验指标
    engagement_score: float = 0.0
    satisfaction_score: float = 0.0
    dropout_risk: float = 0.0
    
    # 综合评分
    overall_score: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            'path_id': self.path_id,
            'completion_rate': self.completion_rate,
            'time_efficiency': self.time_efficiency,
            'learning_velocity': self.learning_velocity,
            'mastery_improvement': self.mastery_improvement,
            'retention_rate': self.retention_rate,
            'transfer_score': self.transfer_score,
            'engagement_score': self.engagement_score,
            'satisfaction_score': self.satisfaction_score,
            'dropout_risk': self.dropout_risk,
            'overall_score': self.overall_score
        }


@dataclass
class ABTestResult:
    """A/B测试结果"""
    test_id: str
    variant_a: str
    variant_b: str
    
    sample_size_a: int = 0
    sample_size_b: int = 0
    
    metrics_a: Dict[str, float] = field(default_factory=dict)
    metrics_b: Dict[str, float] = field(default_factory=dict)
    
    improvement: Dict[str, float] = field(default_factory=dict)
    p_values: Dict[str, float] = field(default_factory=dict)
    
    winner: Optional[str] = None
    confidence: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            'test_id': self.test_id,
            'variant_a': self.variant_a,
            'variant_b': self.variant_b,
            'sample_size_a': self.sample_size_a,
            'sample_size_b': self.sample_size_b,
            'metrics_a': self.metrics_a,
            'metrics_b': self.metrics_b,
            'improvement': self.improvement,
            'p_values': self.p_values,
            'winner': self.winner,
            'confidence': self.confidence
        }


class PathEvaluator:
    """路径评估器"""
    
    def __init__(self, knowledge_graph: Any = None):
        self.knowledge_graph = knowledge_graph
        self.metrics_history: Dict[str, List[PathMetrics]] = {}
        
        # 指标权重
        self.metric_weights = {
            'completion_rate': 0.25,
            'time_efficiency': 0.15,
            'learning_velocity': 0.15,
            'mastery_improvement': 0.20,
            'retention_rate': 0.15,
            'engagement_score': 0.10
        }
    
    def evaluate_path(
        self,
        path: Any,  # LearningPath
        execution_data: Dict[str, Any]
    ) -> PathMetrics:
        """
        评估学习路径
        
        Args:
            path: 学习路径
            execution_data: 执行数据
                {
                    'start_time': datetime,
                    'end_time': datetime,
                    'completed_nodes': [concept_ids],
                    'mastery_levels': {concept_id: level},
                    'time_spent': {concept_id: minutes},
                    'interaction_logs': [logs]
                }
        
        Returns:
            路径指标
        """
        metrics = PathMetrics(path_id=path.path_id)
        
        # 计算效率指标
        metrics.completion_rate = self._calc_completion_rate(path, execution_data)
        metrics.time_efficiency = self._calc_time_efficiency(path, execution_data)
        metrics.learning_velocity = self._calc_learning_velocity(execution_data)
        
        # 计算效果指标
        metrics.mastery_improvement = self._calc_mastery_improvement(execution_data)
        metrics.retention_rate = self._calc_retention_rate(execution_data)
        metrics.transfer_score = self._calc_transfer_score(path, execution_data)
        
        # 计算体验指标
        metrics.engagement_score = self._calc_engagement_score(execution_data)
        metrics.satisfaction_score = execution_data.get('satisfaction_rating', 0.5)
        metrics.dropout_risk = self._calc_dropout_risk(path, execution_data)
        
        # 计算综合评分
        metrics.overall_score = self._calc_overall_score(metrics)
        
        # 记录历史
        if path.user_id not in self.metrics_history:
            self.metrics_history[path.user_id] = []
        self.metrics_history[path.user_id].append(metrics)
        
        return metrics
    
    def _calc_completion_rate(self, path, execution_data: Dict) -> float:
        """计算完成率"""
        total_nodes = len(path.nodes)
        completed = len(execution_data.get('completed_nodes', []))
        
        return completed / total_nodes if total_nodes > 0 else 0
    
    def _calc_time_efficiency(self, path, execution_data: Dict) -> float:
        """计算时间效率"""
        estimated_time = path.total_time  # 分钟
        actual_time = sum(execution_data.get('time_spent', {}).values())
        
        if actual_time == 0:
            return 0
        
        # 效率 = 估计时间 / 实际时间（越高越好，但不超过1.5）
        efficiency = min(estimated_time / actual_time, 1.5) / 1.5
        return efficiency
    
    def _calc_learning_velocity(self, execution_data: Dict) -> float:
        """计算学习速度"""
        mastery = execution_data.get('mastery_levels', {})
        time_spent = execution_data.get('time_spent', {})
        
        if not mastery or not time_spent:
            return 0
        
        # 每小时掌握的提升
        total_mastery_gain = sum(mastery.values())
        total_hours = sum(time_spent.values()) / 60
        
        if total_hours == 0:
            return 0
        
        velocity = total_mastery_gain / total_hours
        return min(velocity, 1.0)  # 归一化
    
    def _calc_mastery_improvement(self, execution_data: Dict) -> float:
        """计算掌握度提升"""
        initial = execution_data.get('initial_mastery', {})
        final = execution_data.get('mastery_levels', {})
        
        if not final:
            return 0
        
        improvements = []
        for concept, final_level in final.items():
            initial_level = initial.get(concept, 0)
            improvement = final_level - initial_level
            improvements.append(improvement)
        
        return np.mean(improvements) if improvements else 0
    
    def _calc_retention_rate(self, execution_data: Dict) -> float:
        """计算知识保持率"""
        # 如果有延迟测试数据
        delayed_tests = execution_data.get('delayed_tests', {})
        immediate_tests = execution_data.get('immediate_tests', {})
        
        if not delayed_tests or not immediate_tests:
            # 基于遗忘曲线模型估计
            return execution_data.get('estimated_retention', 0.7)
        
        retention_scores = []
        for concept, delayed_score in delayed_tests.items():
            immediate_score = immediate_tests.get(concept, delayed_score)
            if immediate_score > 0:
                retention = delayed_score / immediate_score
                retention_scores.append(retention)
        
        return np.mean(retention_scores) if retention_scores else 0.7
    
    def _calc_transfer_score(self, path, execution_data: Dict) -> float:
        """计算知识迁移分数"""
        # 检查是否能解决相关但不同的问题
        transfer_tests = execution_data.get('transfer_tests', {})
        
        if not transfer_tests:
            return 0.5  # 默认值
        
        return np.mean(list(transfer_tests.values()))
    
    def _calc_engagement_score(self, execution_data: Dict) -> float:
        """计算参与度分数"""
        logs = execution_data.get('interaction_logs', [])
        
        if not logs:
            return 0.5
        
        # 基于多种指标计算参与度
        metrics = {
            'session_time': len(logs) * 2,  # 假设平均每次交互2分钟
            'interactions_per_session': len(logs),
            'retry_rate': 0,
            'help_seeking_rate': 0
        }
        
        # 计算重试率
        attempts = defaultdict(int)
        for log in logs:
            if 'concept_id' in log:
                attempts[log['concept_id']] += 1
        
        if attempts:
            avg_attempts = np.mean(list(attempts.values()))
            metrics['retry_rate'] = min(avg_attempts / 3, 1.0)  # 归一化
        
        # 综合参与度（简单加权）
        engagement = (
            0.3 * min(metrics['session_time'] / 60, 1.0) +  # 会话时长
            0.3 * min(metrics['interactions_per_session'] / 20, 1.0) +  # 交互数
            0.2 * metrics['retry_rate'] +  # 重试率（坚持度）
            0.2 * (1 - metrics['help_seeking_rate'])  # 自主度
        )
        
        return engagement
    
    def _calc_dropout_risk(self, path, execution_data: Dict) -> float:
        """计算辍学风险"""
        risk_factors = []
        
        # 完成率低增加风险
        completion = self._calc_completion_rate(path, execution_data)
        if completion < 0.3:
            risk_factors.append(0.4)
        
        # 参与度低增加风险
        engagement = self._calc_engagement_score(execution_data)
        if engagement < 0.3:
            risk_factors.append(0.3)
        
        # 进展慢增加风险
        velocity = self._calc_learning_velocity(execution_data)
        if velocity < 0.1:
            risk_factors.append(0.3)
        
        # 综合风险
        return min(sum(risk_factors), 1.0)
    
    def _calc_overall_score(self, metrics: PathMetrics) -> float:
        """计算综合评分"""
        scores = {
            'completion_rate': metrics.completion_rate,
            'time_efficiency': metrics.time_efficiency,
            'learning_velocity': metrics.learning_velocity,
            'mastery_improvement': metrics.mastery_improvement,
            'retention_rate': metrics.retention_rate,
            'engagement_score': metrics.engagement_score
        }
        
        overall = sum(
            scores[metric] * weight
            for metric, weight in self.metric_weights.items()
        )
        
        return overall
    
    def compare_paths(
        self,
        path_a_metrics: PathMetrics,
        path_b_metrics: PathMetrics
    ) -> Dict[str, Any]:
        """比较两条路径"""
        comparison = {}
        
        metrics_to_compare = [
            'completion_rate', 'time_efficiency', 'learning_velocity',
            'mastery_improvement', 'retention_rate', 'overall_score'
        ]
        
        for metric in metrics_to_compare:
            val_a = getattr(path_a_metrics, metric)
            val_b = getattr(path_b_metrics, metric)
            
            improvement = ((val_b - val_a) / val_a * 100) if val_a > 0 else 0
            
            comparison[metric] = {
                'path_a': val_a,
                'path_b': val_b,
                'difference': val_b - val_a,
                'improvement_pct': improvement
            }
        
        return comparison


class ABTestFramework:
    """A/B测试框架"""
    
    def __init__(self, evaluator: PathEvaluator):
        self.evaluator = evaluator
        self.active_tests: Dict[str, Dict] = {}
        self.test_results: Dict[str, ABTestResult] = {}
    
    def create_test(
        self,
        test_name: str,
        variant_a_name: str,
        variant_b_name: str,
        target_metric: str = 'overall_score',
        min_sample_size: int = 30
    ) -> str:
        """创建A/B测试"""
        test_id = f"abtest_{test_name}_{int(datetime.utcnow().timestamp())}"
        
        self.active_tests[test_id] = {
            'test_name': test_name,
            'variant_a': variant_a_name,
            'variant_b': variant_b_name,
            'target_metric': target_metric,
            'min_sample_size': min_sample_size,
            'assignments': {},  # user_id -> variant
            'data_a': [],
            'data_b': [],
            'created_at': datetime.utcnow()
        }
        
        return test_id
    
    def assign_user(self, test_id: str, user_id: str) -> str:
        """为用户分配测试组"""
        if test_id not in self.active_tests:
            raise ValueError(f"Test {test_id} not found")
        
        test = self.active_tests[test_id]
        
        # 如果已分配，返回已有分组
        if user_id in test['assignments']:
            return test['assignments'][user_id]
        
        # 随机分配
        import random
        variant = random.choice(['A', 'B'])
        test['assignments'][user_id] = variant
        
        return variant
    
    def record_result(
        self,
        test_id: str,
        user_id: str,
        metrics: PathMetrics
    ):
        """记录测试结果"""
        if test_id not in self.active_tests:
            return
        
        test = self.active_tests[test_id]
        variant = test['assignments'].get(user_id)
        
        if not variant:
            return
        
        if variant == 'A':
            test['data_a'].append(metrics)
        else:
            test['data_b'].append(metrics)
    
    def analyze_test(self, test_id: str) -> Optional[ABTestResult]:
        """分析测试结果"""
        if test_id not in self.active_tests:
            return None
        
        test = self.active_tests[test_id]
        data_a = test['data_a']
        data_b = test['data_b']
        
        if len(data_a) < test['min_sample_size'] or len(data_b) < test['min_sample_size']:
            return None  # 样本不足
        
        # 计算各指标
        metrics_to_analyze = [
            'completion_rate', 'time_efficiency', 'learning_velocity',
            'mastery_improvement', 'retention_rate', 'engagement_score',
            'overall_score'
        ]
        
        result = ABTestResult(
            test_id=test_id,
            variant_a=test['variant_a'],
            variant_b=test['variant_b'],
            sample_size_a=len(data_a),
            sample_size_b=len(data_b)
        )
        
        for metric in metrics_to_analyze:
            values_a = [getattr(m, metric) for m in data_a]
            values_b = [getattr(m, metric) for m in data_b]
            
            mean_a = np.mean(values_a)
            mean_b = np.mean(values_b)
            
            result.metrics_a[metric] = mean_a
            result.metrics_b[metric] = mean_b
            
            # 计算提升
            if mean_a > 0:
                result.improvement[metric] = (mean_b - mean_a) / mean_a
            else:
                result.improvement[metric] = 0
            
            # 简单t检验近似（p值）
            result.p_values[metric] = self._approximate_p_value(values_a, values_b)
        
        # 确定胜者
        target = test['target_metric']
        if result.p_values.get(target, 1.0) < 0.05:
            if result.improvement.get(target, 0) > 0:
                result.winner = 'B'
            else:
                result.winner = 'A'
            result.confidence = 1 - result.p_values[target]
        
        self.test_results[test_id] = result
        return result
    
    def _approximate_p_value(self, values_a: List[float], values_b: List[float]) -> float:
        """近似计算p值（简化版t检验）"""
        n1, n2 = len(values_a), len(values_b)
        
        if n1 < 2 or n2 < 2:
            return 1.0
        
        mean1, mean2 = np.mean(values_a), np.mean(values_b)
        var1, var2 = np.var(values_a, ddof=1), np.var(values_b, ddof=1)
        
        # 合并方差
        pooled_var = ((n1 - 1) * var1 + (n2 - 1) * var2) / (n1 + n2 - 2)
        
        if pooled_var == 0:
            return 1.0 if mean1 == mean2 else 0.0
        
        # t统计量
        t_stat = (mean1 - mean2) / np.sqrt(pooled_var * (1/n1 + 1/n2))
        
        # 简化的p值估计（使用正态分布近似）
        p_value = 2 * (1 - self._normal_cdf(abs(t_stat)))
        
        return p_value
    
    def _normal_cdf(self, x: float) -> float:
        """标准正态分布CDF"""
        import math
        return 0.5 * (1 + math.erf(x / math.sqrt(2)))
    
    def get_test_summary(self, test_id: str) -> Dict:
        """获取测试摘要"""
        if test_id not in self.active_tests:
            return {'error': 'Test not found'}
        
        test = self.active_tests[test_id]
        result = self.test_results.get(test_id)
        
        summary = {
            'test_name': test['test_name'],
            'variant_a': test['variant_a'],
            'variant_b': test['variant_b'],
            'sample_size_a': len(test['data_a']),
            'sample_size_b': len(test['data_b']),
            'target_metric': test['target_metric'],
            'min_sample_size': test['min_sample_size'],
            'is_complete': (
                len(test['data_a']) >= test['min_sample_size'] and
                len(test['data_b']) >= test['min_sample_size']
            ),
            'days_running': (datetime.utcnow() - test['created_at']).days
        }
        
        if result:
            summary['result'] = result.to_dict()
        
        return summary


class PathComparator:
    """路径比较器"""
    
    def __init__(self, evaluator: PathEvaluator):
        self.evaluator = evaluator
    
    def benchmark_paths(
        self,
        paths: List[Any],
        execution_data_list: List[Dict]
    ) -> Dict[str, Any]:
        """
        对多条路径进行基准测试
        
        Returns:
            {
                'rankings': List[Tuple[path_id, score]],
                'best_path': str,
                'detailed_scores': Dict[path_id, PathMetrics],
                'statistical_comparison': Dict
            }
        """
        # 评估所有路径
        metrics_list = []
        for path, data in zip(paths, execution_data_list):
            metrics = self.evaluator.evaluate_path(path, data)
            metrics_list.append((path.path_id, metrics))
        
        # 排序
        rankings = sorted(
            metrics_list,
            key=lambda x: x[1].overall_score,
            reverse=True
        )
        
        # 统计比较
        comparisons = {}
        for i, (id_a, metrics_a) in enumerate(metrics_list):
            for id_b, metrics_b in metrics_list[i+1:]:
                comparison = self.evaluator.compare_paths(metrics_a, metrics_b)
                comparisons[f"{id_a}_vs_{id_b}"] = comparison
        
        return {
            'rankings': [(pid, m.overall_score) for pid, m in rankings],
            'best_path': rankings[0][0] if rankings else None,
            'detailed_scores': {pid: m.to_dict() for pid, m in metrics_list},
            'statistical_comparison': comparisons
        }
    
    def recommend_optimal_path(
        self,
        user_profile: Dict,
        candidate_paths: List[Any]
    ) -> Tuple[str, float]:
        """
        为用户推荐最优路径
        
        Returns:
            (path_id, confidence)
        """
        # 根据用户特征匹配路径特征
        scores = []
        
        for path in candidate_paths:
            score = self._match_path_to_user(path, user_profile)
            scores.append((path.path_id, score))
        
        scores.sort(key=lambda x: x[1], reverse=True)
        
        best_path, best_score = scores[0] if scores else (None, 0)
        
        # 计算置信度
        if len(scores) > 1 and scores[0][1] > 0:
            confidence = (scores[0][1] - scores[1][1]) / scores[0][1]
        else:
            confidence = 0.5
        
        return best_path, confidence
    
    def _match_path_to_user(self, path, user_profile: Dict) -> float:
        """匹配路径和用户"""
        score = 0.5  # 基础分
        
        # 考虑学习风格
        if hasattr(path, 'style_adaptation'):
            # 路径风格与用户偏好匹配度
            pass
        
        # 考虑难度匹配
        user_level = user_profile.get('current_level', 0.5)
        path_difficulty = getattr(path, 'total_difficulty', 0.5)
        
        # 难度差越小越好
        difficulty_match = 1 - abs(user_level - path_difficulty)
        score += difficulty_match * 0.3
        
        # 考虑时间可用性
        available_time = user_profile.get('daily_available_time', 60)
        path_time = getattr(path, 'total_time', 60)
        
        if path_time <= available_time * 7:  # 一周内可完成
            score += 0.2
        
        return score
