"""
反馈分类服务
使用关键词匹配和简单规则进行自动分类
"""
import re
from typing import Dict, List, Tuple
from enum import Enum
import logging

from ..models.models import FeedbackType

logger = logging.getLogger(__name__)


class FeedbackClassifier:
    """反馈自动分类器"""
    
    # 分类关键词规则
    KEYWORD_RULES = {
        FeedbackType.BUG_REPORT: [
            # 中文关键词
            'bug', '错误', '崩溃', '闪退', '异常', '报错', '出错', '失败', '无法',
            '不能', '卡住', '无响应', '白屏', '黑屏', '崩溃', 'bug', 'error',
            'crash', 'freeze', 'stuck', 'broken', 'not working', 'failed',
            'exception', 'timeout', 'connection error', '加载失败', '页面错误'
        ],
        FeedbackType.FEATURE_REQUEST: [
            '功能', '建议', '增加', '添加', '希望', '想要', '需求', '改进', '优化',
            'feature', 'request', 'add', 'suggest', 'improvement', 'enhancement',
            'would like', 'need', 'wish', 'proposal', 'idea', '能否', '是否可以'
        ],
        FeedbackType.CONTENT_ERROR: [
            '内容错误', '概念错误', '公式错误', '定理错误', '证明错误', '定义错误',
            '描述错误', '信息有误', '不正确', '不准确', 'content error', 'wrong',
            'incorrect', 'inaccurate', 'mistake', 'typo', '错字', '错别字', '错误'
        ],
        FeedbackType.PERFORMANCE: [
            '慢', '卡顿', '延迟', '加载慢', '响应慢', '性能', '速度', '优化',
            'slow', 'lag', 'delay', 'performance', 'loading', 'speed', 'fast',
            'optimize', 'sluggish', 'unresponsive', '耗时', '长时间'
        ],
        FeedbackType.USABILITY: [
            '难用', '不方便', '不直观', '界面', '操作', '体验', '交互', '导航',
            'usability', 'ui', 'interface', 'difficult', 'confusing', 'hard to use',
            'user experience', 'ux', 'navigation', 'layout', 'design', '找不到'
        ],
        FeedbackType.COMPLAINT: [
            '失望', '不满', '糟糕', '差劲', '气愤', '愤怒', '投诉', '退款',
            'disappointed', 'frustrated', 'terrible', 'awful', 'bad', 'worst',
            'hate', 'angry', 'complaint', 'unacceptable', 'ridiculous', '垃圾'
        ],
        FeedbackType.COMPLIMENT: [
            '好评', '赞', '优秀', '很棒', '感谢', '喜欢', '满意', '完美',
            'good', 'great', 'excellent', 'awesome', 'amazing', 'love', 'like',
            'perfect', 'wonderful', 'fantastic', 'best', 'helpful', '谢谢'
        ],
        FeedbackType.GENERAL: [
            '咨询', '问题', '疑问', '请问', '想了解', '如何', '怎么', '什么',
            'question', 'ask', 'wonder', 'curious', 'help', 'general'
        ]
    }
    
    # 优先级判定规则
    PRIORITY_RULES = {
        'critical': {
            'keywords': ['崩溃', '无法访问', '数据丢失', '安全', '紧急', '严重',
                        'crash', 'down', 'data loss', 'security', 'urgent', 'critical',
                        'broken', 'not working at all', 'emergency'],
            'score': 4
        },
        'high': {
            'keywords': ['重要', '影响', '错误', 'bug', 'important', 'significant',
                        'error', 'wrong', 'serious'],
            'score': 3
        },
        'medium': {
            'keywords': ['建议', '改进', '希望', 'suggest', 'improve', 'would like'],
            'score': 2
        },
        'low': {
            'keywords': ['小', '轻微', 'minor', 'small', 'tiny'],
            'score': 1
        }
    }
    
    def __init__(self):
        """初始化分类器"""
        self._compile_patterns()
    
    def _compile_patterns(self):
        """编译关键词匹配模式"""
        self.patterns = {}
        for feedback_type, keywords in self.KEYWORD_RULES.items():
            # 创建不区分大小写的正则模式
            escaped_keywords = [re.escape(kw) for kw in keywords]
            pattern = re.compile('|'.join(escaped_keywords), re.IGNORECASE)
            self.patterns[feedback_type] = pattern
    
    def classify(self, title: str, content: str) -> Tuple[FeedbackType, float]:
        """
        对反馈进行分类
        
        Args:
            title: 反馈标题
            content: 反馈内容
            
        Returns:
            (分类类型, 置信度)
        """
        text = f"{title} {content}".lower()
        
        # 统计各类型的匹配得分
        scores = {}
        for feedback_type, pattern in self.patterns.items():
            matches = len(pattern.findall(text))
            # 加权：标题匹配权重更高
            title_matches = len(pattern.findall(title.lower()))
            weighted_score = matches + title_matches * 2
            if weighted_score > 0:
                scores[feedback_type] = weighted_score
        
        if not scores:
            # 没有匹配到关键词，返回GENERAL
            return FeedbackType.GENERAL, 0.5
        
        # 找出得分最高的类型
        best_type = max(scores, key=scores.get)
        max_score = scores[best_type]
        total_score = sum(scores.values())
        
        # 计算置信度
        confidence = min(0.5 + (max_score / total_score) * 0.5, 1.0) if total_score > 0 else 0.5
        
        # 如果有多个类型得分相同且较高，降低置信度
        top_types = [t for t, s in scores.items() if s == max_score]
        if len(top_types) > 1:
            confidence *= 0.8
        
        return best_type, round(confidence, 2)
    
    def determine_priority(self, title: str, content: str, 
                          feedback_type: FeedbackType) -> str:
        """
        确定反馈优先级
        
        Args:
            title: 反馈标题
            content: 反馈内容
            feedback_type: 反馈类型
            
        Returns:
            优先级字符串
        """
        text = f"{title} {content}".lower()
        
        # 计算各优先级得分
        scores = {}
        for priority, rule in self.PRIORITY_RULES.items():
            score = 0
            for keyword in rule['keywords']:
                if keyword.lower() in text:
                    score += rule['score']
            if score > 0:
                scores[priority] = score
        
        # 根据反馈类型调整优先级
        type_priority_boost = {
            FeedbackType.BUG_REPORT: 1,
            FeedbackType.PERFORMANCE: 1,
            FeedbackType.CONTENT_ERROR: 0.5,
            FeedbackType.COMPLAINT: 0.5
        }
        
        if feedback_type in type_priority_boost:
            for priority in scores:
                scores[priority] += type_priority_boost[feedback_type]
        
        if not scores:
            # 默认中优先级
            return 'medium'
        
        # 返回得分最高的优先级
        return max(scores, key=scores.get)
    
    def extract_keywords(self, title: str, content: str) -> List[str]:
        """
        提取反馈关键词
        
        Args:
            title: 反馈标题
            content: 反馈内容
            
        Returns:
            关键词列表
        """
        text = f"{title} {content}"
        
        # 简单的关键词提取：找出出现频率较高的词
        # 实际应用中可以使用更复杂的NLP技术
        words = re.findall(r'\b[\u4e00-\u9fa5]{2,8}\b|\b[a-zA-Z]{4,}\b', text)
        
        # 统计词频
        word_freq = {}
        for word in words:
            word_lower = word.lower()
            if word_lower not in self._get_stop_words():
                word_freq[word_lower] = word_freq.get(word_lower, 0) + 1
        
        # 返回频率最高的前10个词
        sorted_words = sorted(word_freq.items(), key=lambda x: x[1], reverse=True)
        return [word for word, freq in sorted_words[:10] if freq >= 1]
    
    def _get_stop_words(self) -> set:
        """获取停用词"""
        return {
            'the', 'and', 'for', 'are', 'but', 'not', 'you', 'all', 'can',
            'had', 'her', 'was', 'one', 'our', 'out', 'day', 'get', 'has',
            'him', 'his', 'how', 'its', 'may', 'new', 'now', 'old', 'see',
            'two', 'who', 'boy', 'did', 'she', 'use', 'her', 'way', 'many',
            '这个', '那个', '然后', '所以', '因为', '虽然', '但是', '如果',
            '什么', '怎么', '如何', '可以', '需要', '希望', '建议'
        }
    
    def analyze_sentiment(self, title: str, content: str) -> Dict[str, float]:
        """
        简单的情感分析
        
        Args:
            title: 反馈标题
            content: 反馈内容
            
        Returns:
            情感分析结果
        """
        text = f"{title} {content}".lower()
        
        # 正面词
        positive_words = [
            'good', 'great', 'excellent', 'amazing', 'love', 'like', 'perfect',
            'wonderful', 'fantastic', 'best', 'helpful', 'nice', 'awesome',
            '优秀', '棒', '好', '喜欢', '感谢', '满意', '完美', '赞'
        ]
        
        # 负面词
        negative_words = [
            'bad', 'terrible', 'awful', 'hate', 'worst', 'horrible', 'broken',
            'disappointed', 'frustrated', 'angry', 'annoying', 'useless',
            '糟糕', '差劲', '失望', '不满', '愤怒', '讨厌', '难用', '垃圾'
        ]
        
        positive_count = sum(1 for word in positive_words if word in text)
        negative_count = sum(1 for word in negative_words if word in text)
        total = positive_count + negative_count
        
        if total == 0:
            return {
                'sentiment': 'neutral',
                'positive_score': 0.5,
                'negative_score': 0.5,
                'confidence': 0.0
            }
        
        positive_ratio = positive_count / total
        negative_ratio = negative_count / total
        
        if positive_ratio > negative_ratio:
            sentiment = 'positive'
        elif negative_ratio > positive_ratio:
            sentiment = 'negative'
        else:
            sentiment = 'neutral'
        
        return {
            'sentiment': sentiment,
            'positive_score': round(positive_ratio, 2),
            'negative_score': round(negative_ratio, 2),
            'confidence': round(total / len(text.split()), 2)
        }
    
    def get_classification_details(self, title: str, content: str) -> Dict:
        """
        获取详细的分类信息
        
        Args:
            title: 反馈标题
            content: 反馈内容
            
        Returns:
            详细分类信息
        """
        feedback_type, confidence = self.classify(title, content)
        priority = self.determine_priority(title, content, feedback_type)
        keywords = self.extract_keywords(title, content)
        sentiment = self.analyze_sentiment(title, content)
        
        return {
            'feedback_type': feedback_type.value,
            'confidence': confidence,
            'priority': priority,
            'keywords': keywords,
            'sentiment': sentiment
        }


# 全局分类器实例
_classifier = None


def get_feedback_classifier() -> FeedbackClassifier:
    """获取反馈分类器实例（单例模式）"""
    global _classifier
    if _classifier is None:
        _classifier = FeedbackClassifier()
    return _classifier
