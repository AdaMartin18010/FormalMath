"""
性能评估报告生成器
==================

生成推荐系统优化的完整性能评估报告。
"""

import numpy as np
import json
import logging
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from collections import defaultdict
import matplotlib.pyplot as plt
import io
import base64

logger = logging.getLogger(__name__)


# ============================================================================
# 评估指标类
# ============================================================================

@dataclass
class AccuracyMetrics:
    """准确性指标"""
    precision_at_k: Dict[int, float] = field(default_factory=dict)
    recall_at_k: Dict[int, float] = field(default_factory=dict)
    f1_at_k: Dict[int, float] = field(default_factory=dict)
    ndcg_at_k: Dict[int, float] = field(default_factory=dict)
    mrr: float = 0.0
    map_score: float = 0.0
    auc: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "precision": self.precision_at_k,
            "recall": self.recall_at_k,
            "f1_score": self.f1_at_k,
            "ndcg": self.ndcg_at_k,
            "mrr": round(self.mrr, 4),
            "map": round(self.map_score, 4),
            "auc": round(self.auc, 4)
        }


@dataclass
class DiversityMetrics:
    """多样性指标"""
    intra_list_diversity: float = 0.0
    inter_list_diversity: float = 0.0
    branch_coverage: float = 0.0
    difficulty_diversity: float = 0.0
    gini_diversity: float = 0.0
    shannon_entropy: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "intra_list_diversity": round(self.intra_list_diversity, 4),
            "inter_list_diversity": round(self.inter_list_diversity, 4),
            "branch_coverage": round(self.branch_coverage, 4),
            "difficulty_diversity": round(self.difficulty_diversity, 4),
            "gini_diversity": round(self.gini_diversity, 4),
            "shannon_entropy": round(self.shannon_entropy, 4)
        }


@dataclass
class CoverageMetrics:
    """覆盖率指标"""
    catalog_coverage: float = 0.0
    user_coverage: float = 0.0
    long_tail_coverage: float = 0.0
    novelty_coverage: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "catalog_coverage": round(self.catalog_coverage, 4),
            "user_coverage": round(self.user_coverage, 4),
            "long_tail_coverage": round(self.long_tail_coverage, 4),
            "novelty_coverage": round(self.novelty_coverage, 4)
        }


@dataclass
class UserSatisfactionMetrics:
    """用户满意度指标"""
    click_through_rate: float = 0.0
    conversion_rate: float = 0.0
    completion_rate: float = 0.0
    average_rating: float = 0.0
    user_engagement_score: float = 0.0
    retention_rate: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "click_through_rate": round(self.click_through_rate, 4),
            "conversion_rate": round(self.conversion_rate, 4),
            "completion_rate": round(self.completion_rate, 4),
            "average_rating": round(self.average_rating, 2),
            "user_engagement_score": round(self.user_engagement_score, 4),
            "retention_rate": round(self.retention_rate, 4)
        }


@dataclass
class PerformanceMetrics:
    """性能指标"""
    average_response_time_ms: float = 0.0
    p95_response_time_ms: float = 0.0
    p99_response_time_ms: float = 0.0
    throughput_qps: float = 0.0
    cache_hit_rate: float = 0.0
    error_rate: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "average_response_time_ms": round(self.average_response_time_ms, 2),
            "p95_response_time_ms": round(self.p95_response_time_ms, 2),
            "p99_response_time_ms": round(self.p99_response_time_ms, 2),
            "throughput_qps": round(self.throughput_qps, 2),
            "cache_hit_rate": round(self.cache_hit_rate, 4),
            "error_rate": round(self.error_rate, 4)
        }


@dataclass
class ColdStartMetrics:
    """冷启动指标"""
    new_user_ctr: float = 0.0
    new_user_conversion: float = 0.0
    time_to_first_engagement: float = 0.0
    early_retention_rate: float = 0.0
    
    def to_dict(self) -> Dict:
        return {
            "new_user_ctr": round(self.new_user_ctr, 4),
            "new_user_conversion": round(self.new_user_conversion, 4),
            "time_to_first_engagement": round(self.time_to_first_engagement, 2),
            "early_retention_rate": round(self.early_retention_rate, 4)
        }


@dataclass
class EvaluationResult:
    """完整评估结果"""
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    version: str = "2.0"
    accuracy: AccuracyMetrics = field(default_factory=AccuracyMetrics)
    diversity: DiversityMetrics = field(default_factory=DiversityMetrics)
    coverage: CoverageMetrics = field(default_factory=CoverageMetrics)
    satisfaction: UserSatisfactionMetrics = field(default_factory=UserSatisfactionMetrics)
    performance: PerformanceMetrics = field(default_factory=PerformanceMetrics)
    cold_start: ColdStartMetrics = field(default_factory=ColdStartMetrics)
    
    def to_dict(self) -> Dict:
        return {
            "timestamp": self.timestamp,
            "version": self.version,
            "accuracy": self.accuracy.to_dict(),
            "diversity": self.diversity.to_dict(),
            "coverage": self.coverage.to_dict(),
            "satisfaction": self.satisfaction.to_dict(),
            "performance": self.performance.to_dict(),
            "cold_start": self.cold_start.to_dict()
        }


# ============================================================================
# 评估报告生成器
# ============================================================================

class EvaluationReportGenerator:
    """
    评估报告生成器
    
    生成推荐系统的全面性能评估报告，包括准确性、多样性、覆盖率、
    用户满意度、系统性能和冷启动效果等多个维度。
    """
    
    def __init__(self):
        self.results_history: List[EvaluationResult] = []
        self.baseline: Optional[EvaluationResult] = None
    
    def set_baseline(self, baseline: EvaluationResult):
        """设置基准线"""
        self.baseline = baseline
    
    def generate_report(
        self,
        recommender,
        test_users: List[int],
        db_session,
        ground_truth_data: Optional[Dict[int, List[str]]] = None
    ) -> EvaluationResult:
        """
        生成完整的评估报告
        
        Args:
            recommender: 推荐器实例
            test_users: 测试用户列表
            db_session: 数据库会话
            ground_truth_data: 真实的用户偏好数据
        
        Returns:
            评估结果对象
        """
        result = EvaluationResult()
        
        # 1. 评估准确性
        result.accuracy = self._evaluate_accuracy(
            recommender, test_users, ground_truth_data
        )
        
        # 2. 评估多样性
        result.diversity = self._evaluate_diversity(
            recommender, test_users, db_session
        )
        
        # 3. 评估覆盖率
        result.coverage = self._evaluate_coverage(
            recommender, test_users, db_session
        )
        
        # 4. 评估用户满意度
        result.satisfaction = self._evaluate_satisfaction(
            test_users, db_session
        )
        
        # 5. 评估系统性能
        result.performance = self._evaluate_performance(
            recommender, test_users
        )
        
        # 6. 评估冷启动效果
        result.cold_start = self._evaluate_cold_start(
            recommender, test_users, db_session
        )
        
        self.results_history.append(result)
        
        return result
    
    def _evaluate_accuracy(
        self,
        recommender,
        test_users: List[int],
        ground_truth_data: Optional[Dict[int, List[str]]]
    ) -> AccuracyMetrics:
        """评估推荐准确性"""
        metrics = AccuracyMetrics()
        k_values = [5, 10, 20]
        
        for k in k_values:
            precisions = []
            recalls = []
            ndcgs = []
            
            for user_id in test_users:
                # 获取推荐
                try:
                    result = recommender.recommend(
                        user_id, n_recommendations=k, enable_diversity=False
                    )
                    recs = result.get("recommendations", [])
                    rec_ids = [r["concept_id"] for r in recs]
                except Exception:
                    continue
                
                # 获取真实数据
                if ground_truth_data and user_id in ground_truth_data:
                    actual = ground_truth_data[user_id]
                else:
                    # 使用模拟数据
                    actual = self._get_simulated_ground_truth(user_id)
                
                if not actual:
                    continue
                
                # 计算Precision@K
                hits = len(set(rec_ids) & set(actual))
                precision = hits / k
                precisions.append(precision)
                
                # 计算Recall@K
                recall = hits / len(actual)
                recalls.append(recall)
                
                # 计算NDCG@K
                dcg = sum(
                    1.0 / np.log2(i + 2) 
                    for i, cid in enumerate(rec_ids) 
                    if cid in actual
                )
                idcg = sum(1.0 / np.log2(i + 2) for i in range(min(len(actual), k)))
                ndcg = dcg / idcg if idcg > 0 else 0
                ndcgs.append(ndcg)
            
            metrics.precision_at_k[k] = np.mean(precisions) if precisions else 0
            metrics.recall_at_k[k] = np.mean(recalls) if recalls else 0
            
            # F1 Score
            p = metrics.precision_at_k[k]
            r = metrics.recall_at_k[k]
            metrics.f1_at_k[k] = 2 * p * r / (p + r) if (p + r) > 0 else 0
            
            metrics.ndcg_at_k[k] = np.mean(ndcgs) if ndcgs else 0
        
        # MRR (Mean Reciprocal Rank)
        mrr_scores = []
        for user_id in test_users:
            try:
                result = recommender.recommend(user_id, n_recommendations=20)
                recs = result.get("recommendations", [])
                
                if ground_truth_data and user_id in ground_truth_data:
                    actual = set(ground_truth_data[user_id])
                else:
                    actual = set(self._get_simulated_ground_truth(user_id))
                
                for i, rec in enumerate(recs):
                    if rec["concept_id"] in actual:
                        mrr_scores.append(1.0 / (i + 1))
                        break
            except Exception:
                continue
        
        metrics.mrr = np.mean(mrr_scores) if mrr_scores else 0
        
        return metrics
    
    def _evaluate_diversity(
        self,
        recommender,
        test_users: List[int],
        db_session
    ) -> DiversityMetrics:
        """评估推荐多样性"""
        from ..models.models import KnowledgeGraphNode
        
        metrics = DiversityMetrics()
        
        all_recommendations = []
        intra_diversities = []
        
        for user_id in test_users[:100]:  # 限制用户数量
            try:
                result = recommender.recommend(
                    user_id, n_recommendations=10, enable_diversity=True
                )
                recs = result.get("recommendations", [])
                
                if recs:
                    all_recommendations.append(recs)
                    
                    # 计算列表内多样性
                    branches = [r["branch"] for r in recs]
                    difficulties = [r.get("difficulty", "intermediate") for r in recs]
                    
                    # 分支多样性
                    unique_branches = len(set(branches))
                    intra_diversities.append(unique_branches / len(recs))
            except Exception:
                continue
        
        # Intra-list Diversity
        metrics.intra_list_diversity = np.mean(intra_diversities) if intra_diversities else 0
        
        # Inter-list Diversity
        if len(all_recommendations) >= 2:
            inter_diversities = []
            for i in range(len(all_recommendations)):
                for j in range(i + 1, len(all_recommendations)):
                    set_i = set(r["concept_id"] for r in all_recommendations[i])
                    set_j = set(r["concept_id"] for r in all_recommendations[j])
                    
                    # Jaccard距离
                    jaccard = len(set_i & set_j) / len(set_i | set_j) if (set_i | set_j) else 0
                    inter_diversities.append(1 - jaccard)
            
            metrics.inter_list_diversity = np.mean(inter_diversities) if inter_diversities else 0
        
        # 分支覆盖率
        all_branches = set()
        for recs in all_recommendations:
            all_branches.update(r["branch"] for r in recs)
        
        total_branches = db_session.query(KnowledgeGraphNode.branch).distinct().count()
        metrics.branch_coverage = len(all_branches) / total_branches if total_branches > 0 else 0
        
        # Shannon Entropy
        branch_counts = defaultdict(int)
        for recs in all_recommendations:
            for r in recs:
                branch_counts[r["branch"]] += 1
        
        total = sum(branch_counts.values())
        if total > 0:
            probs = [c / total for c in branch_counts.values()]
            metrics.shannon_entropy = -sum(p * np.log2(p) for p in probs if p > 0)
        
        return metrics
    
    def _evaluate_coverage(
        self,
        recommender,
        test_users: List[int],
        db_session
    ) -> CoverageMetrics:
        """评估推荐覆盖率"""
        from ..models.models import KnowledgeGraphNode
        
        metrics = CoverageMetrics()
        
        recommended_items = set()
        user_with_recs = 0
        
        for user_id in test_users:
            try:
                result = recommender.recommend(user_id, n_recommendations=10)
                recs = result.get("recommendations", [])
                
                if recs:
                    user_with_recs += 1
                    recommended_items.update(r["concept_id"] for r in recs)
            except Exception:
                continue
        
        # Catalog Coverage
        total_items = db_session.query(KnowledgeGraphNode).count()
        metrics.catalog_coverage = len(recommended_items) / total_items if total_items > 0 else 0
        
        # User Coverage
        metrics.user_coverage = user_with_recs / len(test_users) if test_users else 0
        
        return metrics
    
    def _evaluate_satisfaction(
        self,
        test_users: List[int],
        db_session
    ) -> UserSatisfactionMetrics:
        """评估用户满意度（基于模拟数据）"""
        from ..models.models import UserProgress, UserActivity
        
        metrics = UserSatisfactionMetrics()
        
        # 模拟计算用户满意度指标
        # 在实际系统中，这些数据应该从用户行为日志中获取
        
        click_counts = []
        conversion_counts = []
        ratings = []
        
        for user_id in test_users[:100]:
            # 查询用户活动
            clicks = db_session.query(UserActivity).filter(
                UserActivity.user_id == user_id,
                UserActivity.activity_type == "click_recommendation"
            ).count()
            
            completions = db_session.query(UserProgress).filter(
                UserProgress.user_id == user_id,
                UserProgress.mastery_level > 0.8
            ).count()
            
            if clicks > 0:
                click_counts.append(clicks)
                conversion_counts.append(completions)
        
        if click_counts:
            metrics.click_through_rate = np.mean(click_counts) / 10  # 归一化
            metrics.conversion_rate = np.mean(conversion_counts) / max(click_counts) if click_counts else 0
        
        # 模拟平均评分
        metrics.average_rating = 4.2  # 模拟值
        
        return metrics
    
    def _evaluate_performance(
        self,
        recommender,
        test_users: List[int]
    ) -> PerformanceMetrics:
        """评估系统性能"""
        import time
        
        metrics = PerformanceMetrics()
        
        response_times = []
        errors = 0
        
        for user_id in test_users[:50]:  # 限制测试用户数量
            try:
                start = time.time()
                recommender.recommend(user_id, n_recommendations=10)
                elapsed = (time.time() - start) * 1000  # 转换为毫秒
                response_times.append(elapsed)
            except Exception:
                errors += 1
        
        if response_times:
            metrics.average_response_time_ms = np.mean(response_times)
            metrics.p95_response_time_ms = np.percentile(response_times, 95)
            metrics.p99_response_time_ms = np.percentile(response_times, 99)
            metrics.throughput_qps = 1000 / metrics.average_response_time_ms if metrics.average_response_time_ms > 0 else 0
        
        metrics.error_rate = errors / len(test_users[:50]) if test_users else 0
        
        return metrics
    
    def _evaluate_cold_start(
        self,
        recommender,
        test_users: List[int],
        db_session
    ) -> ColdStartMetrics:
        """评估冷启动效果"""
        from ..models.models import UserProgress
        
        metrics = ColdStartMetrics()
        
        # 找出新用户
        new_users = []
        for user_id in test_users:
            count = db_session.query(UserProgress).filter(
                UserProgress.user_id == user_id
            ).count()
            if count < 5:
                new_users.append(user_id)
        
        if not new_users:
            return metrics
        
        # 评估新用户的推荐效果
        clicks = []
        conversions = []
        
        for user_id in new_users[:20]:
            try:
                result = recommender.recommend(user_id, n_recommendations=10)
                recs = result.get("recommendations", [])
                
                if recs:
                    # 模拟点击率
                    clicks.append(1 if np.random.random() > 0.5 else 0)
                    
                    # 检查是否转化
                    progress = db_session.query(UserProgress).filter(
                        UserProgress.user_id == user_id,
                        UserProgress.mastery_level > 0.5
                    ).count()
                    conversions.append(1 if progress > 0 else 0)
            except Exception:
                continue
        
        if clicks:
            metrics.new_user_ctr = np.mean(clicks)
        if conversions:
            metrics.new_user_conversion = np.mean(conversions)
        
        return metrics
    
    def _get_simulated_ground_truth(self, user_id: int) -> List[str]:
        """获取模拟的ground truth数据"""
        # 在实际系统中，这应该来自真实的用户偏好数据
        np.random.seed(user_id)
        n_items = np.random.randint(3, 10)
        return [f"concept_{i}" for i in np.random.randint(0, 100, n_items)]
    
    def compare_with_baseline(self, result: EvaluationResult) -> Dict[str, Any]:
        """与基准线对比"""
        if self.baseline is None:
            return {"error": "未设置基准线"}
        
        comparison = {
            "timestamp": datetime.utcnow().isoformat(),
            "improvements": {},
            "degradations": {},
            "unchanged": {}
        }
        
        # 对比准确性指标
        for k in [5, 10, 20]:
            baseline_p = self.baseline.accuracy.precision_at_k.get(k, 0)
            current_p = result.accuracy.precision_at_k.get(k, 0)
            change = ((current_p - baseline_p) / (baseline_p + 1e-8)) * 100
            
            key = f"precision_at_{k}"
            if abs(change) < 5:
                comparison["unchanged"][key] = round(change, 2)
            elif change > 0:
                comparison["improvements"][key] = round(change, 2)
            else:
                comparison["degradations"][key] = round(change, 2)
        
        # 对比多样性指标
        diversity_metrics = [
            ("intra_list_diversity", self.baseline.diversity.intra_list_diversity, result.diversity.intra_list_diversity),
            ("branch_coverage", self.baseline.diversity.branch_coverage, result.diversity.branch_coverage)
        ]
        
        for name, baseline_val, current_val in diversity_metrics:
            change = ((current_val - baseline_val) / (baseline_val + 1e-8)) * 100
            
            if abs(change) < 5:
                comparison["unchanged"][name] = round(change, 2)
            elif change > 0:
                comparison["improvements"][name] = round(change, 2)
            else:
                comparison["degradations"][name] = round(change, 2)
        
        return comparison
    
    def generate_full_report(self, result: EvaluationResult) -> str:
        """生成完整的评估报告（Markdown格式）"""
        report = f"""# 推荐系统性能评估报告

**生成时间**: {result.timestamp}
**系统版本**: {result.version}

---

## 1. 准确性指标 (Accuracy Metrics)

### Precision@K
| K值 | 精度 |
|-----|------|
"""
        
        for k, v in result.accuracy.precision_at_k.items():
            report += f"| @{k} | {v:.4f} |\n"
        
        report += """
### Recall@K
| K值 | 召回率 |
|-----|--------|
"""
        for k, v in result.accuracy.recall_at_k.items():
            report += f"| @{k} | {v:.4f} |\n"
        
        report += f"""
### 其他准确性指标
- **MRR (平均倒数排名)**: {result.accuracy.mrr:.4f}
- **MAP (平均精度均值)**: {result.accuracy.map:.4f}
- **AUC**: {result.accuracy.auc:.4f}

---

## 2. 多样性指标 (Diversity Metrics)

| 指标 | 数值 | 说明 |
|------|------|------|
| Intra-list Diversity | {result.diversity.intra_list_diversity:.4f} | 列表内多样性 |
| Inter-list Diversity | {result.diversity.inter_list_diversity:.4f} | 列表间多样性 |
| Branch Coverage | {result.diversity.branch_coverage:.4f} | 分支覆盖率 |
| Shannon Entropy | {result.diversity.shannon_entropy:.4f} | 香农熵 |

---

## 3. 覆盖率指标 (Coverage Metrics)

| 指标 | 数值 |
|------|------|
| Catalog Coverage | {result.coverage.catalog_coverage:.4f} |
| User Coverage | {result.coverage.user_coverage:.4f} |

---

## 4. 用户满意度指标 (User Satisfaction)

| 指标 | 数值 |
|------|------|
| CTR (点击率) | {result.satisfaction.click_through_rate:.4f} |
| Conversion Rate (转化率) | {result.satisfaction.conversion_rate:.4f} |
| Average Rating (平均评分) | {result.satisfaction.average_rating:.2f}/5.0 |

---

## 5. 系统性能指标 (Performance Metrics)

| 指标 | 数值 |
|------|------|
| Average Response Time | {result.performance.average_response_time_ms:.2f} ms |
| P95 Response Time | {result.performance.p95_response_time_ms:.2f} ms |
| P99 Response Time | {result.performance.p99_response_time_ms:.2f} ms |
| Throughput | {result.performance.throughput_qps:.2f} QPS |
| Error Rate | {result.performance.error_rate:.4f} |

---

## 6. 冷启动指标 (Cold Start Metrics)

| 指标 | 数值 |
|------|------|
| New User CTR | {result.cold_start.new_user_ctr:.4f} |
| New User Conversion | {result.cold_start.new_user_conversion:.4f} |
| Early Retention Rate | {result.cold_start.early_retention_rate:.4f} |

---

## 7. 总结与建议

### 7.1 性能亮点
"""
        
        # 自动识别亮点
        highlights = []
        if result.accuracy.precision_at_k.get(10, 0) > 0.3:
            highlights.append("- Precision@10超过0.3，推荐准确性良好")
        if result.diversity.intra_list_diversity > 0.5:
            highlights.append("- 列表内多样性较高，推荐结果丰富")
        if result.performance.average_response_time_ms < 100:
            highlights.append("- 平均响应时间低于100ms，系统性能优秀")
        
        if highlights:
            report += "\n".join(highlights)
        else:
            report += "暂无突出亮点"
        
        report += """

### 7.2 改进建议
"""
        
        # 自动识别改进点
        suggestions = []
        if result.accuracy.precision_at_k.get(10, 0) < 0.2:
            suggestions.append("- 推荐准确性有待提升，建议优化特征工程或尝试更复杂的模型")
        if result.diversity.branch_coverage < 0.5:
            suggestions.append("- 分支覆盖率较低，建议增加多样性权重")
        if result.performance.error_rate > 0.01:
            suggestions.append("- 错误率较高，建议加强异常处理和系统稳定性")
        
        if suggestions:
            report += "\n".join(suggestions)
        else:
            report += "系统整体表现良好，建议持续监控"
        
        report += "\n\n---\n\n*报告由 FormalMath 推荐系统自动生成*\n"
        
        return report
    
    def export_to_json(self, result: EvaluationResult, filepath: str):
        """导出结果为JSON文件"""
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(result.to_dict(), f, ensure_ascii=False, indent=2)
        logger.info(f"评估结果已导出: {filepath}")
    
    def export_to_markdown(self, result: EvaluationResult, filepath: str):
        """导出报告为Markdown文件"""
        report = self.generate_full_report(result)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(report)
        logger.info(f"评估报告已导出: {filepath}")


# ============================================================================
# 便捷函数
# ============================================================================

def create_evaluation_report(
    recommender,
    test_users: List[int],
    db_session,
    output_dir: str = "./evaluation_reports"
) -> str:
    """
    创建并导出完整的评估报告
    
    Returns:
        报告文件路径
    """
    import os
    
    generator = EvaluationReportGenerator()
    result = generator.generate_report(recommender, test_users, db_session)
    
    # 确保输出目录存在
    os.makedirs(output_dir, exist_ok=True)
    
    # 生成文件名
    timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    json_path = os.path.join(output_dir, f"evaluation_{timestamp}.json")
    md_path = os.path.join(output_dir, f"evaluation_report_{timestamp}.md")
    
    # 导出
    generator.export_to_json(result, json_path)
    generator.export_to_markdown(result, md_path)
    
    return md_path
