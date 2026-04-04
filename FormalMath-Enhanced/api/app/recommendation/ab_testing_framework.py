"""
A/B测试框架
===========

为推荐算法优化提供科学的A/B测试支持。

功能特性:
1. 多变量测试支持
2. 流量分配与分组
3. 实时指标追踪
4. 统计显著性检验
5. 自动报告生成
"""

import numpy as np
import logging
from typing import Dict, List, Optional, Tuple, Any, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
from enum import Enum
import hashlib
import json
from scipy import stats

logger = logging.getLogger(__name__)


# ============================================================================
# 枚举与常量
# ============================================================================

class TestStatus(Enum):
    """测试状态"""
    DRAFT = "draft"
    RUNNING = "running"
    PAUSED = "paused"
    COMPLETED = "completed"
    CANCELLED = "cancelled"


class MetricType(Enum):
    """指标类型"""
    CTR = "click_through_rate"
    CONVERSION = "conversion_rate"
    ENGAGEMENT = "engagement_score"
    SATISFACTION = "satisfaction_score"
    DIVERSITY = "diversity_score"
    COVERAGE = "coverage"
    REVENUE = "revenue"


class AllocationMethod(Enum):
    """流量分配方法"""
    RANDOM = "random"
    HASH = "hash"
    ROUND_ROBIN = "round_robin"
    STRATIFIED = "stratified"


# ============================================================================
# 数据类
# ============================================================================

@dataclass
class Variant:
    """测试变体"""
    name: str
    description: str
    config: Dict[str, Any]
    traffic_percentage: float = 0.5
    
    def __post_init__(self):
        if not 0 < self.traffic_percentage <= 1:
            raise ValueError("traffic_percentage必须在(0, 1]之间")


@dataclass
class Metric:
    """指标定义"""
    name: str
    metric_type: MetricType
    description: str
    higher_is_better: bool = True
    min_sample_size: int = 100
    target_value: Optional[float] = None


@dataclass
class TestResult:
    """测试结果"""
    variant_name: str
    sample_size: int
    metrics: Dict[str, float]
    confidence_intervals: Dict[str, Tuple[float, float]]
    p_values: Dict[str, float]
    is_significant: bool
    effect_sizes: Dict[str, float]


@dataclass
class ABTest:
    """A/B测试定义"""
    test_id: str
    name: str
    description: str
    variants: List[Variant]
    metrics: List[Metric]
    status: TestStatus = TestStatus.DRAFT
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    min_duration_days: int = 7
    min_samples_per_variant: int = 1000
    created_at: datetime = field(default_factory=datetime.utcnow)
    
    # 运行时数据
    user_assignments: Dict[int, str] = field(default_factory=dict)
    event_log: List[Dict] = field(default_factory=list)


# ============================================================================
# A/B测试管理器
# ============================================================================

class ABTestingManager:
    """
    A/B测试管理器
    
    管理推荐算法的A/B测试生命周期，包括创建、运行、分析和报告。
    """
    
    def __init__(self):
        self.tests: Dict[str, ABTest] = {}
        self.active_tests: Dict[str, ABTest] = {}
        self.test_history: List[Dict] = []
        
        # 指标存储
        self.metrics_store: Dict[str, Dict[str, List[float]]] = defaultdict(
            lambda: defaultdict(list)
        )
        
        # 预定义的推荐算法测试模板
        self.recommendation_test_templates = self._init_templates()
    
    def _init_templates(self) -> Dict[str, Dict]:
        """初始化推荐算法测试模板"""
        return {
            "weight_optimization": {
                "name": "推荐器权重优化测试",
                "description": "测试不同推荐器权重配置的效果",
                "variants": [
                    {
                        "name": "control",
                        "description": "控制组：均衡权重",
                        "config": {
                            "weights": {
                                "collaborative": 0.25,
                                "knowledge_graph": 0.25,
                                "reinforcement_learning": 0.25,
                                "content": 0.25
                            }
                        },
                        "traffic_percentage": 0.5
                    },
                    {
                        "name": "treatment",
                        "description": "实验组：知识图谱权重增加",
                        "config": {
                            "weights": {
                                "collaborative": 0.2,
                                "knowledge_graph": 0.4,
                                "reinforcement_learning": 0.2,
                                "content": 0.2
                            }
                        },
                        "traffic_percentage": 0.5
                    }
                ],
                "metrics": ["ctr", "conversion", "engagement", "diversity"]
            },
            
            "diversity_algorithm": {
                "name": "多样性算法测试",
                "description": "测试MMR多样性算法对用户体验的影响",
                "variants": [
                    {
                        "name": "no_diversity",
                        "description": "无多样性优化",
                        "config": {"enable_diversity": False, "lambda_param": 0.0},
                        "traffic_percentage": 0.33
                    },
                    {
                        "name": "balanced",
                        "description": "平衡的多样性与相关性",
                        "config": {"enable_diversity": True, "lambda_param": 0.5},
                        "traffic_percentage": 0.33
                    },
                    {
                        "name": "diversity_focused",
                        "description": "强调多样性",
                        "config": {"enable_diversity": True, "lambda_param": 0.8},
                        "traffic_percentage": 0.34
                    }
                ],
                "metrics": ["ctr", "engagement", "diversity", "satisfaction"]
            },
            
            "cold_start_strategy": {
                "name": "冷启动策略测试",
                "description": "测试不同冷启动处理策略的效果",
                "variants": [
                    {
                        "name": "popular_based",
                        "description": "基于热门概念",
                        "config": {"cold_start_strategy": "popular"},
                        "traffic_percentage": 0.5
                    },
                    {
                        "name": "exploration_based",
                        "description": "基于探索策略",
                        "config": {"cold_start_strategy": "exploration"},
                        "traffic_percentage": 0.5
                    }
                ],
                "metrics": ["conversion", "engagement", "retention"]
            },
            
            "explanation_effectiveness": {
                "name": "解释性推荐效果测试",
                "description": "测试可解释性对用户体验的影响",
                "variants": [
                    {
                        "name": "no_explanation",
                        "description": "无解释",
                        "config": {"enable_explanation": False},
                        "traffic_percentage": 0.5
                    },
                    {
                        "name": "with_explanation",
                        "description": "带详细解释",
                        "config": {"enable_explanation": True},
                        "traffic_percentage": 0.5
                    }
                ],
                "metrics": ["ctr", "conversion", "satisfaction", "trust"]
            },
            
            "feedback_learning": {
                "name": "反馈学习机制测试",
                "description": "测试反馈学习对推荐质量的影响",
                "variants": [
                    {
                        "name": "static_weights",
                        "description": "静态权重",
                        "config": {"enable_dynamic_weights": False},
                        "traffic_percentage": 0.5
                    },
                    {
                        "name": "dynamic_weights",
                        "description": "动态权重调整",
                        "config": {
                            "enable_dynamic_weights": True,
                            "learning_rate": 0.05
                        },
                        "traffic_percentage": 0.5
                    }
                ],
                "metrics": ["ctr", "engagement", "satisfaction", "long_term_retention"]
            }
        }
    
    def create_test_from_template(
        self,
        template_name: str,
        test_id: Optional[str] = None,
        custom_config: Optional[Dict] = None
    ) -> ABTest:
        """从模板创建测试"""
        if template_name not in self.recommendation_test_templates:
            raise ValueError(f"未知模板: {template_name}")
        
        template = self.recommendation_test_templates[template_name]
        
        # 合并自定义配置
        if custom_config:
            template = self._merge_config(template, custom_config)
        
        # 创建变体
        variants = [
            Variant(**v) for v in template["variants"]
        ]
        
        # 创建指标
        metric_map = {
            "ctr": Metric(
                name="click_through_rate",
                metric_type=MetricType.CTR,
                description="点击率",
                higher_is_better=True
            ),
            "conversion": Metric(
                name="conversion_rate",
                metric_type=MetricType.CONVERSION,
                description="转化率",
                higher_is_better=True
            ),
            "engagement": Metric(
                name="engagement_score",
                metric_type=MetricType.ENGAGEMENT,
                description="参与度评分",
                higher_is_better=True
            ),
            "satisfaction": Metric(
                name="satisfaction_score",
                metric_type=MetricType.SATISFACTION,
                description="用户满意度",
                higher_is_better=True
            ),
            "diversity": Metric(
                name="diversity_score",
                metric_type=MetricType.DIVERSITY,
                description="推荐多样性",
                higher_is_better=True
            ),
            "coverage": Metric(
                name="coverage",
                metric_type=MetricType.COVERAGE,
                description="覆盖率",
                higher_is_better=True
            ),
            "retention": Metric(
                name="retention_rate",
                metric_type=MetricType.ENGAGEMENT,
                description="留存率",
                higher_is_better=True
            ),
            "trust": Metric(
                name="trust_score",
                metric_type=MetricType.SATISFACTION,
                description="信任度",
                higher_is_better=True
            ),
            "long_term_retention": Metric(
                name="long_term_retention",
                metric_type=MetricType.ENGAGEMENT,
                description="长期留存率",
                higher_is_better=True
            )
        }
        
        metrics = [metric_map[m] for m in template["metrics"] if m in metric_map]
        
        # 生成测试ID
        if test_id is None:
            test_id = f"{template_name}_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}"
        
        test = ABTest(
            test_id=test_id,
            name=template["name"],
            description=template["description"],
            variants=variants,
            metrics=metrics
        )
        
        self.tests[test_id] = test
        logger.info(f"创建测试: {test_id}")
        
        return test
    
    def create_custom_test(
        self,
        test_id: str,
        name: str,
        description: str,
        variants: List[Dict],
        metrics: List[str],
        min_duration_days: int = 7,
        min_samples_per_variant: int = 1000
    ) -> ABTest:
        """创建自定义测试"""
        variant_objects = [Variant(**v) for v in variants]
        
        metric_objects = []
        for m in metrics:
            metric_objects.append(Metric(
                name=m,
                metric_type=MetricType.ENGAGEMENT,
                description=m,
                higher_is_better=True
            ))
        
        test = ABTest(
            test_id=test_id,
            name=name,
            description=description,
            variants=variant_objects,
            metrics=metric_objects,
            min_duration_days=min_duration_days,
            min_samples_per_variant=min_samples_per_variant
        )
        
        self.tests[test_id] = test
        return test
    
    def start_test(self, test_id: str) -> bool:
        """启动测试"""
        if test_id not in self.tests:
            logger.error(f"测试不存在: {test_id}")
            return False
        
        test = self.tests[test_id]
        
        if test.status != TestStatus.DRAFT:
            logger.error(f"测试状态不允许启动: {test.status}")
            return False
        
        test.status = TestStatus.RUNNING
        test.start_time = datetime.utcnow()
        self.active_tests[test_id] = test
        
        logger.info(f"测试启动: {test_id}")
        return True
    
    def stop_test(self, test_id: str) -> bool:
        """停止测试"""
        if test_id not in self.active_tests:
            return False
        
        test = self.active_tests[test_id]
        test.status = TestStatus.COMPLETED
        test.end_time = datetime.utcnow()
        
        del self.active_tests[test_id]
        
        # 生成最终报告
        self._generate_final_report(test)
        
        logger.info(f"测试停止: {test_id}")
        return True
    
    def assign_user_to_variant(
        self,
        test_id: str,
        user_id: int,
        method: AllocationMethod = AllocationMethod.HASH
    ) -> str:
        """
        将用户分配到测试变体
        
        Args:
            test_id: 测试ID
            user_id: 用户ID
            method: 分配方法
        
        Returns:
            分配的变体名称
        """
        if test_id not in self.tests:
            raise ValueError(f"测试不存在: {test_id}")
        
        test = self.tests[test_id]
        
        # 检查是否已分配
        if user_id in test.user_assignments:
            return test.user_assignments[user_id]
        
        # 根据分配方法选择变体
        if method == AllocationMethod.HASH:
            variant = self._hash_allocation(test, user_id)
        elif method == AllocationMethod.RANDOM:
            variant = self._random_allocation(test)
        elif method == AllocationMethod.ROUND_ROBIN:
            variant = self._round_robin_allocation(test)
        else:
            variant = self._hash_allocation(test, user_id)
        
        test.user_assignments[user_id] = variant.name
        
        return variant.name
    
    def _hash_allocation(self, test: ABTest, user_id: int) -> Variant:
        """基于哈希的一致性分配"""
        hash_input = f"{test.test_id}:{user_id}"
        hash_value = int(hashlib.md5(hash_input.encode()).hexdigest(), 16)
        
        # 根据流量百分比分配
        normalized = (hash_value % 1000) / 1000.0
        cumulative = 0.0
        
        for variant in test.variants:
            cumulative += variant.traffic_percentage
            if normalized < cumulative:
                return variant
        
        return test.variants[-1]
    
    def _random_allocation(self, test: ABTest) -> Variant:
        """随机分配"""
        weights = [v.traffic_percentage for v in test.variants]
        return np.random.choice(test.variants, p=weights)
    
    def _round_robin_allocation(self, test: ABTest) -> Variant:
        """轮询分配"""
        total_assigned = len(test.user_assignments)
        variant_index = total_assigned % len(test.variants)
        return test.variants[variant_index]
    
    def record_event(
        self,
        test_id: str,
        user_id: int,
        event_type: str,
        value: float,
        metadata: Optional[Dict] = None
    ):
        """记录测试事件"""
        if test_id not in self.active_tests:
            return
        
        test = self.active_tests[test_id]
        variant = test.user_assignments.get(user_id, "unknown")
        
        event = {
            "timestamp": datetime.utcnow().isoformat(),
            "user_id": user_id,
            "variant": variant,
            "event_type": event_type,
            "value": value,
            "metadata": metadata or {}
        }
        
        test.event_log.append(event)
        
        # 存储到指标存储
        key = f"{test_id}:{variant}:{event_type}"
        self.metrics_store[key].append(value)
    
    def get_test_results(self, test_id: str) -> Dict[str, Any]:
        """获取测试结果"""
        if test_id not in self.tests:
            return {"error": "测试不存在"}
        
        test = self.tests[test_id]
        
        results = {
            "test_id": test_id,
            "name": test.name,
            "status": test.status.value,
            "start_time": test.start_time.isoformat() if test.start_time else None,
            "end_time": test.end_time.isoformat() if test.end_time else None,
            "variants": [],
            "sample_sizes": {},
            "metrics_comparison": {},
            "statistical_significance": {},
            "recommendation": None
        }
        
        # 计算各变体的指标
        for variant in test.variants:
            variant_results = self._calculate_variant_metrics(
                test_id, variant.name, test.metrics
            )
            results["variants"].append({
                "name": variant.name,
                "description": variant.description,
                "config": variant.config,
                "results": variant_results
            })
            
            results["sample_sizes"][variant.name] = variant_results.get("sample_size", 0)
        
        # 统计检验
        if len(test.variants) >= 2:
            results["statistical_significance"] = self._statistical_analysis(
                test_id, test.variants, test.metrics
            )
            
            # 生成建议
            results["recommendation"] = self._generate_recommendation(
                results["variants"],
                results["statistical_significance"],
                test.metrics
            )
        
        return results
    
    def _calculate_variant_metrics(
        self,
        test_id: str,
        variant_name: str,
        metrics: List[Metric]
    ) -> Dict[str, Any]:
        """计算单个变体的指标"""
        results = {"sample_size": 0}
        
        for metric in metrics:
            key = f"{test_id}:{variant_name}:{metric.name}"
            values = self.metrics_store.get(key, [])
            
            if values:
                results["sample_size"] = len(values)
                results[metric.name] = {
                    "mean": np.mean(values),
                    "median": np.median(values),
                    "std": np.std(values),
                    "min": np.min(values),
                    "max": np.max(values),
                    "ci_95": self._calculate_ci(values)
                }
        
        return results
    
    def _calculate_ci(self, values: List[float], confidence: float = 0.95) -> Tuple[float, float]:
        """计算置信区间"""
        if not values:
            return (0.0, 0.0)
        
        mean = np.mean(values)
        std = np.std(values)
        n = len(values)
        
        if n < 2:
            return (mean, mean)
        
        # 使用t分布
        t_value = stats.t.ppf((1 + confidence) / 2, n - 1)
        margin = t_value * std / np.sqrt(n)
        
        return (mean - margin, mean + margin)
    
    def _statistical_analysis(
        self,
        test_id: str,
        variants: List[Variant],
        metrics: List[Metric]
    ) -> Dict[str, Any]:
        """执行统计显著性检验"""
        analysis = {}
        
        # 使用控制组（第一个变体）作为基准
        control_name = variants[0].name
        
        for metric in metrics:
            control_key = f"{test_id}:{control_name}:{metric.name}"
            control_values = self.metrics_store.get(control_key, [])
            
            if not control_values:
                continue
            
            metric_analysis = {}
            
            for variant in variants[1:]:
                variant_key = f"{test_id}:{variant.name}:{metric.name}"
                variant_values = self.metrics_store.get(variant_key, [])
                
                if not variant_values:
                    continue
                
                # t检验
                t_stat, p_value = stats.ttest_ind(
                    variant_values, control_values, equal_var=False
                )
                
                # 效应量 (Cohen's d)
                pooled_std = np.sqrt(
                    (np.std(variant_values) ** 2 + np.std(control_values) ** 2) / 2
                )
                cohens_d = (np.mean(variant_values) - np.mean(control_values)) / (pooled_std + 1e-8)
                
                # 相对提升
                relative_lift = (np.mean(variant_values) - np.mean(control_values)) / (np.mean(control_values) + 1e-8)
                
                metric_analysis[variant.name] = {
                    "p_value": p_value,
                    "is_significant": p_value < 0.05,
                    "cohens_d": cohens_d,
                    "effect_size": self._interpret_effect_size(cohens_d),
                    "relative_lift": relative_lift,
                    "winner": variant.name if (p_value < 0.05 and 
                        (metric.higher_is_better and relative_lift > 0 or 
                         not metric.higher_is_better and relative_lift < 0)) else control_name
                }
            
            analysis[metric.name] = metric_analysis
        
        return analysis
    
    def _interpret_effect_size(self, cohens_d: float) -> str:
        """解释效应量"""
        abs_d = abs(cohens_d)
        if abs_d < 0.2:
            return "negligible"
        elif abs_d < 0.5:
            return "small"
        elif abs_d < 0.8:
            return "medium"
        else:
            return "large"
    
    def _generate_recommendation(
        self,
        variants: List[Dict],
        significance: Dict,
        metrics: List[Metric]
    ) -> Dict[str, Any]:
        """生成测试建议"""
        if len(variants) < 2:
            return {"message": "需要至少两个变体进行比较"}
        
        control = variants[0]
        treatment = variants[1]
        
        # 统计各变体的胜利次数
        wins = defaultdict(int)
        significant_wins = defaultdict(int)
        
        for metric_name, metric_results in significance.items():
            for variant_name, result in metric_results.items():
                winner = result.get("winner", control["name"])
                wins[winner] += 1
                if result.get("is_significant", False):
                    significant_wins[winner] += 1
        
        # 生成建议
        control_wins = wins.get(control["name"], 0)
        treatment_wins = wins.get(treatment["name"], 0)
        
        if significant_wins.get(treatment["name"], 0) > significant_wins.get(control["name"], 0):
            recommendation = {
                "action": "rollout_treatment",
                "confidence": "high" if significant_wins[treatment["name"]] > 1 else "medium",
                "reason": f"实验组在{significant_wins[treatment['name']]}个关键指标上显著优于控制组",
                "winning_variant": treatment["name"]
            }
        elif significant_wins.get(control["name"], 0) > 0:
            recommendation = {
                "action": "keep_control",
                "confidence": "high",
                "reason": "控制组表现更稳定，建议维持现状",
                "winning_variant": control["name"]
            }
        else:
            recommendation = {
                "action": "continue_test",
                "confidence": "low",
                "reason": "尚未达到统计显著性，建议继续测试或增加样本量",
                "winning_variant": None
            }
        
        recommendation["wins_summary"] = dict(wins)
        recommendation["significant_wins"] = dict(significant_wins)
        
        return recommendation
    
    def _generate_final_report(self, test: ABTest):
        """生成最终报告"""
        report = {
            "test_id": test.test_id,
            "name": test.name,
            "report_type": "final",
            "generated_at": datetime.utcnow().isoformat(),
            "duration_days": (test.end_time - test.start_time).days if test.end_time and test.start_time else 0,
            "total_users": len(test.user_assignments),
            "results": self.get_test_results(test.test_id)
        }
        
        self.test_history.append(report)
        logger.info(f"生成最终报告: {test.test_id}")
    
    def _merge_config(self, template: Dict, custom: Dict) -> Dict:
        """合并模板和自定义配置"""
        merged = template.copy()
        for key, value in custom.items():
            if key in merged and isinstance(merged[key], dict) and isinstance(value, dict):
                merged[key] = {**merged[key], **value}
            else:
                merged[key] = value
        return merged
    
    def get_active_tests(self) -> List[Dict]:
        """获取所有活跃测试"""
        return [
            {
                "test_id": test.test_id,
                "name": test.name,
                "status": test.status.value,
                "start_time": test.start_time.isoformat() if test.start_time else None,
                "assigned_users": len(test.user_assignments)
            }
            for test in self.active_tests.values()
        ]
    
    def get_test_history(self, limit: int = 10) -> List[Dict]:
        """获取测试历史"""
        return self.test_history[-limit:]


# ============================================================================
# 便捷函数
# ============================================================================

def create_default_manager() -> ABTestingManager:
    """创建默认的A/B测试管理器"""
    return ABTestingManager()


# 全局管理器实例
_default_manager: Optional[ABTestingManager] = None


def get_ab_testing_manager() -> ABTestingManager:
    """获取全局A/B测试管理器"""
    global _default_manager
    if _default_manager is None:
        _default_manager = create_default_manager()
    return _default_manager
