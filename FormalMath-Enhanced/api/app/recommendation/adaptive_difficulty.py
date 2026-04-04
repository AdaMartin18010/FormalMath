"""
自适应难度调整系统
实时评估、动态调整、挑战级别匹配
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import math


class DifficultyLevel(str, Enum):
    """难度级别"""
    BEGINNER = "beginner"
    ELEMENTARY = "elementary"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"
    EXPERT = "expert"


class PerformanceZone(str, Enum):
    """表现区域"""
    FRUSTRATION = "frustration"  # 过于困难
    LEARNING = "learning"        # 学习区（最佳）
    BOREDOM = "boredom"          # 过于简单


@dataclass
class DifficultyCalibration:
    """难度校准数据"""
    user_id: str
    base_difficulty: float = 0.5  # 基础难度水平
    current_difficulty: float = 0.5
    difficulty_history: List[Tuple[datetime, float]] = field(default_factory=list)
    
    # 难度调整参数
    adjustment_rate: float = 0.1
    min_difficulty: float = 0.1
    max_difficulty: float = 1.0
    
    # 表现窗口
    performance_window: List[float] = field(default_factory=list)
    window_size: int = 10
    
    def update_performance(self, performance: float):
        """更新表现窗口"""
        self.performance_window.append(performance)
        if len(self.performance_window) > self.window_size:
            self.performance_window.pop(0)
    
    def get_average_performance(self) -> float:
        """获取平均表现"""
        if not self.performance_window:
            return 0.5
        return np.mean(self.performance_window)
    
    def get_performance_trend(self) -> float:
        """获取表现趋势"""
        if len(self.performance_window) < 3:
            return 0.0
        
        # 简单线性回归
        x = np.arange(len(self.performance_window))
        y = np.array(self.performance_window)
        
        # 计算斜率
        slope = np.corrcoef(x, y)[0, 1] * np.std(y) / (np.std(x) + 1e-8)
        return slope


@dataclass
class ChallengeAssessment:
    """挑战评估"""
    difficulty_score: float  # 难度分数
    challenge_level: str     # 挑战级别
    performance_prediction: float  # 表现预测
    match_quality: float     # 匹配质量
    recommendation: str      # 建议


class AdaptiveDifficultyManager:
    """
    自适应难度管理器
    
    基于表现实时调整难度，维持在学习区内
    """
    
    # 难度级别映射
    DIFFICULTY_LEVELS = {
        DifficultyLevel.BEGINNER: (0.0, 0.2),
        DifficultyLevel.ELEMENTARY: (0.2, 0.4),
        DifficultyLevel.INTERMEDIATE: (0.4, 0.6),
        DifficultyLevel.ADVANCED: (0.6, 0.8),
        DifficultyLevel.EXPERT: (0.8, 1.0),
    }
    
    # 最佳学习区参数
    OPTIMAL_ZONE = {
        'min_success_rate': 0.6,
        'target_success_rate': 0.75,
        'max_success_rate': 0.9
    }
    
    def __init__(self):
        self.calibrations: Dict[str, DifficultyCalibration] = {}
        self.concept_difficulties: Dict[str, float] = {}
        
        # 调整参数
        self.adjustment_sensitivity = 0.15
        self.momentum = 0.3
    
    def get_or_create_calibration(self, user_id: str) -> DifficultyCalibration:
        """获取或创建用户难度校准"""
        if user_id not in self.calibrations:
            self.calibrations[user_id] = DifficultyCalibration(user_id=user_id)
        return self.calibrations[user_id]
    
    def assess_performance_zone(
        self,
        user_id: str,
        current_performance: Optional[float] = None
    ) -> PerformanceZone:
        """
        评估当前表现区域
        
        Args:
            user_id: 用户ID
            current_performance: 当前表现，None使用历史平均
        
        Returns:
            表现区域
        """
        calibration = self.get_or_create_calibration(user_id)
        
        if current_performance is None:
            performance = calibration.get_average_performance()
        else:
            performance = current_performance
        
        if performance < self.OPTIMAL_ZONE['min_success_rate']:
            return PerformanceZone.FRUSTRATION
        elif performance > self.OPTIMAL_ZONE['max_success_rate']:
            return PerformanceZone.BOREDOM
        else:
            return PerformanceZone.LEARNING
    
    def calculate_difficulty_adjustment(
        self,
        user_id: str,
        performance: float,
        time_spent: Optional[int] = None,
        expected_time: Optional[int] = None
    ) -> float:
        """
        计算难度调整量
        
        Args:
            user_id: 用户ID
            performance: 表现 0-1
            time_spent: 实际用时（秒）
            expected_time: 预期用时（秒）
        
        Returns:
            调整量（正数增加难度，负数降低）
        """
        calibration = self.get_or_create_calibration(user_id)
        
        # 更新表现历史
        calibration.update_performance(performance)
        
        # 计算与目标的差距
        target = self.OPTIMAL_ZONE['target_success_rate']
        error = performance - target
        
        # 基础调整
        base_adjustment = -error * self.adjustment_sensitivity
        
        # 考虑表现趋势
        trend = calibration.get_performance_trend()
        trend_adjustment = trend * self.momentum
        
        # 考虑时间效率
        time_factor = 0.0
        if time_spent and expected_time and expected_time > 0:
            time_ratio = time_spent / expected_time
            if time_ratio < 0.7 and performance > 0.8:
                time_factor = 0.05  # 快速完成且表现好，可以增加难度
            elif time_ratio > 1.5 and performance < 0.5:
                time_factor = -0.05  # 超时且表现差，降低难度
        
        total_adjustment = base_adjustment + trend_adjustment + time_factor
        
        return max(-0.2, min(0.2, total_adjustment))  # 限制单次调整幅度
    
    def adjust_difficulty(
        self,
        user_id: str,
        performance: float,
        time_spent: Optional[int] = None,
        expected_time: Optional[int] = None
    ) -> float:
        """
        调整用户难度级别
        
        Returns:
            新的难度级别
        """
        calibration = self.get_or_create_calibration(user_id)
        
        adjustment = self.calculate_difficulty_adjustment(
            user_id, performance, time_spent, expected_time
        )
        
        # 应用调整
        new_difficulty = calibration.current_difficulty + adjustment
        new_difficulty = max(calibration.min_difficulty, 
                           min(calibration.max_difficulty, new_difficulty))
        
        # 更新校准
        calibration.current_difficulty = new_difficulty
        calibration.difficulty_history.append((datetime.utcnow(), new_difficulty))
        
        # 限制历史长度
        if len(calibration.difficulty_history) > 100:
            calibration.difficulty_history = calibration.difficulty_history[-100:]
        
        return new_difficulty
    
    def get_recommended_difficulty(
        self,
        user_id: str,
        concept_id: Optional[str] = None
    ) -> float:
        """
        获取推荐难度
        
        Args:
            user_id: 用户ID
            concept_id: 可选概念ID，用于概念特定调整
        
        Returns:
            推荐难度 0-1
        """
        calibration = self.get_or_create_calibration(user_id)
        base_difficulty = calibration.current_difficulty
        
        if concept_id and concept_id in self.concept_difficulties:
            # 考虑概念固有难度进行相对调整
            concept_diff = self.concept_difficulties[concept_id]
            # 概念越难，实际给予的难度相对降低
            relative_difficulty = base_difficulty * (1 - concept_diff * 0.3)
            return max(0.1, min(1.0, relative_difficulty))
        
        return base_difficulty
    
    def assess_challenge(
        self,
        user_id: str,
        item_difficulty: float,
        user_ability: Optional[float] = None
    ) -> ChallengeAssessment:
        """
        评估挑战匹配度
        
        Args:
            user_id: 用户ID
            item_difficulty: 项目难度
            user_ability: 用户能力估计（可选）
        
        Returns:
            挑战评估结果
        """
        calibration = self.get_or_create_calibration(user_id)
        
        if user_ability is None:
            user_ability = calibration.current_difficulty
        
        # 计算差距
        gap = item_difficulty - user_ability
        
        # 使用项目反应理论(IRT)简化版预测表现
        # P(正确) = 1 / (1 + exp(-(ability - difficulty)))
        prediction = 1 / (1 + math.exp(-(user_ability - item_difficulty) * 4))
        
        # 评估匹配质量
        if -0.1 <= gap <= 0.1:
            match_quality = 1.0
            challenge_level = 'optimal'
        elif -0.2 <= gap < -0.1:
            match_quality = 0.8
            challenge_level = 'easy'
        elif 0.1 < gap <= 0.2:
            match_quality = 0.8
            challenge_level = 'challenging'
        elif gap < -0.2:
            match_quality = 0.4
            challenge_level = 'too_easy'
        else:
            match_quality = 0.4
            challenge_level = 'too_hard'
        
        # 生成建议
        if challenge_level == 'optimal':
            recommendation = '当前难度非常适合，继续保持'
        elif challenge_level == 'easy':
            recommendation = '可以适当增加难度或加快进度'
        elif challenge_level == 'challenging':
            recommendation = '挑战性适中，有助于成长'
        elif challenge_level == 'too_easy':
            recommendation = '建议提升难度以避免无聊'
        else:
            recommendation = '建议降低难度或提供额外支持'
        
        return ChallengeAssessment(
            difficulty_score=item_difficulty,
            challenge_level=challenge_level,
            performance_prediction=prediction,
            match_quality=match_quality,
            recommendation=recommendation
        )
    
    def select_optimal_items(
        self,
        user_id: str,
        available_items: List[Dict],
        target_count: int = 5,
        diversity_weight: float = 0.2
    ) -> List[Dict]:
        """
        选择最优学习项目
        
        Args:
            user_id: 用户ID
            available_items: 可用项目列表
            target_count: 目标数量
            diversity_weight: 多样性权重
        
        Returns:
            选中的项目列表
        """
        calibration = self.get_or_create_calibration(user_id)
        target_difficulty = calibration.current_difficulty
        
        scored_items = []
        for item in available_items:
            item_diff = item.get('difficulty', 0.5)
            
            # 计算与目标的匹配度
            difficulty_match = 1 - abs(item_diff - target_difficulty)
            
            # 评估挑战质量
            assessment = self.assess_challenge(user_id, item_diff)
            
            # 综合分数
            score = (
                0.4 * difficulty_match +
                0.4 * assessment.match_quality +
                0.2 * item.get('quality_score', 0.5)
            )
            
            scored_items.append({
                **item,
                'selection_score': score,
                'challenge_assessment': assessment
            })
        
        # 按分数排序
        scored_items.sort(key=lambda x: x['selection_score'], reverse=True)
        
        # 选择，考虑多样性
        selected = []
        concept_types = set()
        
        for item in scored_items:
            if len(selected) >= target_count:
                break
            
            item_type = item.get('type', 'unknown')
            
            # 如果该类型已有很多，根据多样性权重决定是否跳过
            type_count = sum(1 for s in selected if s.get('type') == item_type)
            if type_count > 0 and np.random.random() > diversity_weight:
                continue
            
            selected.append(item)
            concept_types.add(item_type)
        
        return selected
    
    def get_learning_zone_recommendation(self, user_id: str) -> Dict:
        """
        获取学习区建议
        
        Returns:
            包含建议和参数的字典
        """
        calibration = self.get_or_create_calibration(user_id)
        zone = self.assess_performance_zone(user_id)
        avg_performance = calibration.get_average_performance()
        
        recommendations = {
            'current_zone': zone.value,
            'average_performance': avg_performance,
            'target_performance': self.OPTIMAL_ZONE['target_success_rate'],
            'current_difficulty': calibration.current_difficulty,
            'suggestions': []
        }
        
        if zone == PerformanceZone.FRUSTRATION:
            recommendations['suggestions'] = [
                '当前难度可能过高，建议降低10-20%',
                '回顾前置知识，填补基础漏洞',
                '尝试更多样化的学习资源',
                '考虑寻求同伴或导师帮助'
            ]
            recommendations['recommended_action'] = 'decrease_difficulty'
        
        elif zone == PerformanceZone.BOREDOM:
            recommendations['suggestions'] = [
                '当前内容对您来说过于简单，建议提升难度',
                '尝试更具挑战性的问题',
                '探索相关拓展内容',
                '加快学习进度'
            ]
            recommendations['recommended_action'] = 'increase_difficulty'
        
        else:  # LEARNING
            recommendations['suggestions'] = [
                '当前难度非常适合您的水平',
                '继续保持当前的学习节奏',
                '偶尔尝试略难的挑战以促进成长'
            ]
            recommendations['recommended_action'] = 'maintain'
        
        return recommendations
    
    def get_difficulty_progression_path(
        self,
        user_id: str,
        num_steps: int = 10,
        target_ability: Optional[float] = None
    ) -> List[Dict]:
        """
        生成难度进阶路径
        
        Args:
            user_id: 用户ID
            num_steps: 步数
            target_ability: 目标能力水平
        
        Returns:
            难度进阶路径
        """
        calibration = self.get_or_create_calibration(user_id)
        current = calibration.current_difficulty
        
        if target_ability is None:
            target_ability = min(1.0, current + 0.3)
        
        path = []
        for i in range(num_steps):
            progress = i / (num_steps - 1) if num_steps > 1 else 1
            target_diff = current + (target_ability - current) * progress
            
            # 添加小幅波动以保持挑战性
            variation = np.sin(progress * np.pi * 2) * 0.05
            
            path.append({
                'step': i + 1,
                'target_difficulty': round(max(0.1, min(1.0, target_diff + variation)), 2),
                'expected_performance': self.OPTIMAL_ZONE['target_success_rate'],
                'milestone': self._get_difficulty_milestone(target_diff)
            })
        
        return path
    
    def _get_difficulty_milestone(self, difficulty: float) -> str:
        """获取难度里程碑名称"""
        for level, (min_val, max_val) in self.DIFFICULTY_LEVELS.items():
            if min_val <= difficulty < max_val:
                return level.value
        return DifficultyLevel.EXPERT.value
    
    def calibrate_from_assessment(
        self,
        user_id: str,
        assessment_results: List[Dict]
    ) -> DifficultyCalibration:
        """
        从评估结果校准难度
        
        Args:
            user_id: 用户ID
            assessment_results: 评估结果列表
                [{difficulty, performance, time_spent}, ...]
        
        Returns:
            更新后的校准数据
        """
        calibration = self.get_or_create_calibration(user_id)
        
        if not assessment_results:
            return calibration
        
        # 计算加权平均表现
        weighted_performance = 0
        total_weight = 0
        
        for result in assessment_results:
            diff = result.get('difficulty', 0.5)
            perf = result.get('performance', 0.5)
            
            # 难度越高，权重越大
            weight = 0.5 + diff
            weighted_performance += perf * weight
            total_weight += weight
            
            calibration.update_performance(perf)
        
        avg_performance = weighted_performance / total_weight if total_weight > 0 else 0.5
        
        # 根据表现调整基础难度
        if avg_performance > 0.8:
            calibration.base_difficulty = min(1.0, calibration.base_difficulty + 0.1)
            calibration.current_difficulty = calibration.base_difficulty
        elif avg_performance < 0.4:
            calibration.base_difficulty = max(0.1, calibration.base_difficulty - 0.1)
            calibration.current_difficulty = calibration.base_difficulty
        
        return calibration


class ItemResponseTheory:
    """
    项目反应理论(IRT)简化实现
    用于更精确的能力估计
    """
    
    def __init__(self, num_parameters: int = 2):
        self.num_parameters = num_parameters  # 1PL, 2PL, or 3PL
    
    def probability_correct(
        self,
        ability: float,
        difficulty: float,
        discrimination: float = 1.0,
        guessing: float = 0.0
    ) -> float:
        """
        计算答对概率
        
        Args:
            ability: 被试能力
            difficulty: 项目难度
            discrimination: 区分度（2PL/3PL）
            guessing: 猜测参数（3PL）
        
        Returns:
            答对概率
        """
        # 2PL模型: P = 1 / (1 + exp(-a(θ - b)))
        # a: discrimination, θ: ability, b: difficulty
        
        logit = discrimination * (ability - difficulty)
        prob = 1 / (1 + math.exp(-logit))
        
        if self.num_parameters >= 3:
            # 3PL: 加入猜测参数
            prob = guessing + (1 - guessing) * prob
        
        return prob
    
    def estimate_ability(
        self,
        responses: List[Tuple[float, bool]],
        initial_guess: float = 0.0,
        max_iterations: int = 50
    ) -> Tuple[float, float]:
        """
        估计能力参数
        
        Args:
            responses: [(item_difficulty, is_correct), ...]
            initial_guess: 初始猜测
            max_iterations: 最大迭代次数
        
        Returns:
            (能力估计, 标准误)
        """
        ability = initial_guess
        
        for _ in range(max_iterations):
            # 计算一阶和二阶导数（Fisher scoring）
            first_derivative = 0
            second_derivative = 0
            
            for diff, correct in responses:
                p = self.probability_correct(ability, diff)
                q = 1 - p
                
                first_derivative += (1 if correct else 0) - p
                second_derivative += p * q
            
            if second_derivative < 1e-10:
                break
            
            # 更新
            delta = first_derivative / second_derivative
            ability += delta
            
            if abs(delta) < 1e-5:
                break
        
        # 计算标准误
        information = 0
        for diff, _ in responses:
            p = self.probability_correct(ability, diff)
            information += p * (1 - p)
        
        se = 1 / math.sqrt(information + 1e-10)
        
        return ability, se
    
    def select_next_item(
        self,
        current_ability: float,
        available_items: List[Dict],
        administered_items: List[str]
    ) -> Optional[Dict]:
        """
        计算机自适应测试(CAT)选择下一题
        
        使用最大信息量准则
        """
        best_item = None
        max_info = -1
        
        for item in available_items:
            item_id = item.get('id')
            if item_id in administered_items:
                continue
            
            diff = item.get('difficulty', 0)
            disc = item.get('discrimination', 1.0)
            
            # 计算在当前能力水平的信息量
            p = self.probability_correct(current_ability, diff, disc)
            info = disc ** 2 * p * (1 - p)
            
            if info > max_info:
                max_info = info
                best_item = item
        
        return best_item
