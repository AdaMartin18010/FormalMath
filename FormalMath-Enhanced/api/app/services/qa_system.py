"""
问答系统
支持自然语言理解、答案抽取、多跳推理
"""
import re
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime
import numpy as np

from .vector_store import VectorStore, get_vector_store
from .hybrid_search import HybridSearchService, get_hybrid_search_service, HybridSearchResult
from .embedding import EmbeddingService, get_embedding_service


@dataclass
class Answer:
    """答案"""
    text: str
    confidence: float
    sources: List[Dict] = field(default_factory=list)
    reasoning_chain: List[str] = field(default_factory=list)
    answer_type: str = "direct"  # 'direct', 'multi_hop', 'aggregated'


@dataclass
class Question:
    """问题"""
    text: str
    question_type: str = "factual"  # 'factual', 'procedural', 'comparative', 'explanatory'
    entities: List[str] = field(default_factory=list)
    intent: str = ""
    constraints: Dict = field(default_factory=dict)


class QuestionAnalyzer:
    """问题分析器"""
    
    # 问题类型模式
    QUESTION_PATTERNS = {
        'definition': [
            r'什么是\s*(.+?)\??$',
            r'(.+?)\s*是什么\??$',
            r'定义\s*(.+?)',
            r'请解释\s*(.+?)',
            r'what is\s+(.+?)\??$',
            r'define\s+(.+?)',
            r'explain\s+(.+?)',
        ],
        'proof': [
            r'证明\s*(.+)',
            r'如何证明\s*(.+)',
            r'prove\s+(.+)',
            r'how to prove\s+(.+)',
        ],
        'theorem': [
            r'(.+?)定理',
            r'(.+?)公式',
            r'(.+?)法则',
            r'(.+?)theorem',
            r'(.+?)formula',
        ],
        'comparison': [
            r'(.+?)和(.+?)的区别',
            r'(.+?)与(.+?)的?比较',
            r'difference between\s+(.+?)\s+and\s+(.+)',
            r'compare\s+(.+?)\s+(?:with|and)\s+(.+)',
        ],
        'application': [
            r'(.+?)的应用',
            r'(.+?)有什么用',
            r'application of\s+(.+)',
            r'how is\s+(.+?)\s+used',
        ],
        'property': [
            r'(.+?)的性质',
            r'(.+?)有什么性质',
            r'properties of\s+(.+)',
            r'what are the properties of\s+(.+)',
        ],
    }
    
    # 数学实体模式
    MATH_ENTITY_PATTERNS = [
        r'[\u4e00-\u9fa5]{2,10}(?:定理|公式|引理|推论|定义|性质|算法)',  # 中文数学术语
        r'[A-Z][a-z]+(?:\'s)?\s+(?:theorem|formula|lemma|corollary|definition)',  # 英文人名+术语
        r'\\[a-zA-Z]+(?:\{[^}]+\})*',  # LaTeX命令
        r'\$[^$]+\$',  # 行内公式
    ]
    
    def __init__(self):
        self.compiled_patterns = {}
        for qtype, patterns in self.QUESTION_PATTERNS.items():
            self.compiled_patterns[qtype] = [re.compile(p, re.IGNORECASE) for p in patterns]
    
    def analyze(self, question_text: str) -> Question:
        """分析问题"""
        question = Question(text=question_text)
        
        # 检测问题类型
        question.question_type = self._detect_question_type(question_text)
        
        # 提取实体
        question.entities = self._extract_entities(question_text)
        
        # 识别意图
        question.intent = self._identify_intent(question_text)
        
        # 提取约束条件
        question.constraints = self._extract_constraints(question_text)
        
        return question
    
    def _detect_question_type(self, text: str) -> str:
        """检测问题类型"""
        for qtype, patterns in self.compiled_patterns.items():
            for pattern in patterns:
                if pattern.search(text):
                    return qtype
        
        # 默认类型
        if '?' in text or '？' in text or any(
            word in text.lower() for word in ['what', 'how', 'why', 'when', 'where']
        ):
            return 'factual'
        
        return 'general'
    
    def _extract_entities(self, text: str) -> List[str]:
        """提取数学实体"""
        entities = []
        
        for pattern in self.MATH_ENTITY_PATTERNS:
            matches = re.findall(pattern, text)
            entities.extend(matches)
        
        return list(set(entities))
    
    def _identify_intent(self, text: str) -> str:
        """识别用户意图"""
        # 简单的关键词匹配
        intent_keywords = {
            'seek_definition': ['是什么', '定义', 'what is', 'define'],
            'seek_explanation': ['解释', '说明', 'explain', 'describe'],
            'seek_proof': ['证明', 'proof', 'prove', 'show'],
            'seek_example': ['例子', '示例', 'example', 'demonstrate'],
            'seek_application': ['应用', '用途', 'application', 'use'],
            'seek_comparison': ['区别', '比较', 'difference', 'compare'],
        }
        
        for intent, keywords in intent_keywords.items():
            if any(kw in text.lower() for kw in keywords):
                return intent
        
        return 'seek_information'
    
    def _extract_constraints(self, text: str) -> Dict:
        """提取约束条件"""
        constraints = {}
        
        # 提取限制条件，如"在...情况下"、"对于..."
        constraint_patterns = [
            r'在(.+?)(?:中|下|时|情况下)',
            r'对于(.+?)(?:而言|来说|)',
            r'当(.+?)(?:时|的时候)',
            r'given\s+(.+?)(?:,|;)',
            r'for\s+(.+?)(?:,|;)',
        ]
        
        for pattern in constraint_patterns:
            matches = re.findall(pattern, text, re.IGNORECASE)
            if matches:
                constraints['context'] = matches
        
        return constraints


class AnswerExtractor:
    """答案抽取器"""
    
    def __init__(self, embedding_service: EmbeddingService = None):
        self.embedding_service = embedding_service or get_embedding_service()
    
    def extract(
        self,
        question: Question,
        search_results: List[HybridSearchResult]
    ) -> Answer:
        """从搜索结果中抽取答案"""
        if not search_results:
            return Answer(
                text="抱歉，未找到相关答案。",
                confidence=0.0,
                answer_type="direct"
            )
        
        # 根据问题类型选择抽取策略
        if question.question_type == 'definition':
            return self._extract_definition(question, search_results)
        elif question.question_type == 'comparison':
            return self._extract_comparison(question, search_results)
        elif question.question_type == 'proof':
            return self._extract_proof_strategy(question, search_results)
        else:
            return self._extract_general_answer(question, search_results)
    
    def _extract_definition(
        self,
        question: Question,
        results: List[HybridSearchResult]
    ) -> Answer:
        """抽取定义类答案"""
        # 查找包含定义的段落
        definition_patterns = [
            r'(.+?)被称为(.+?)。',
            r'(.+?)是指(.+?)。',
            r'(.+?)定义为(.+?)。',
            r'(.+?)is defined as(.+?)\.',
            r'(.+?)is called(.+?)\.',
        ]
        
        best_answer = None
        best_score = 0.0
        
        for result in results:
            content = result.content
            for pattern in definition_patterns:
                match = re.search(pattern, content, re.IGNORECASE)
                if match:
                    # 计算相关性分数
                    score = result.combined_score * 0.7 + 0.3  # 匹配到模式的加分
                    if score > best_score:
                        best_score = score
                        best_answer = match.group(0)
            
            # 如果没有匹配到模式，使用第一句作为答案
            if best_answer is None and result.rank == 1:
                sentences = content.split('。')[:2]
                best_answer = '。'.join(sentences) + '。'
                best_score = result.combined_score
        
        return Answer(
            text=best_answer or results[0].content[:200] + "...",
            confidence=best_score,
            sources=[{
                'id': r.id,
                'content': r.content[:100] + "...",
                'score': r.combined_score
            } for r in results[:3]],
            answer_type="direct"
        )
    
    def _extract_comparison(
        self,
        question: Question,
        results: List[HybridSearchResult]
    ) -> Answer:
        """抽取比较类答案"""
        # 聚合多个来源的信息
        comparison_points = []
        
        for result in results:
            content = result.content
            # 查找包含"区别"、"不同"等的句子
            sentences = re.split(r'[。！？]', content)
            for sent in sentences:
                if any(kw in sent for kw in ['区别', '不同', '差异', 'difference', 'whereas', 'while']):
                    comparison_points.append(sent.strip())
        
        if comparison_points:
            answer_text = "主要区别包括：\n" + "\n".join([f"- {p}" for p in comparison_points[:5]])
        else:
            answer_text = "根据相关资料：\n" + "\n".join([f"- {r.content[:100]}..." for r in results[:3]])
        
        return Answer(
            text=answer_text,
            confidence=results[0].combined_score if results else 0.0,
            sources=[{'id': r.id, 'score': r.combined_score} for r in results[:3]],
            answer_type="aggregated"
        )
    
    def _extract_proof_strategy(
        self,
        question: Question,
        results: List[HybridSearchResult]
    ) -> Answer:
        """抽取证明策略"""
        # 查找证明相关的段落
        proof_keywords = ['证明', '证法', 'proof', 'proof strategy', 'approach']
        
        strategies = []
        for result in results:
            content = result.content
            # 提取包含证明关键词的段落
            paragraphs = content.split('\n\n')
            for para in paragraphs:
                if any(kw in para.lower() for kw in proof_keywords):
                    strategies.append({
                        'text': para[:300],
                        'score': result.combined_score
                    })
        
        if strategies:
            # 按分数排序
            strategies.sort(key=lambda x: x['score'], reverse=True)
            answer_text = f"证明思路：\n{strategies[0]['text']}"
        else:
            answer_text = "建议使用标准证明方法，可参考相关文献。"
        
        return Answer(
            text=answer_text,
            confidence=strategies[0]['score'] if strategies else 0.5,
            sources=[{'id': r.id, 'score': r.combined_score} for r in results[:3]],
            answer_type="direct"
        )
    
    def _extract_general_answer(
        self,
        question: Question,
        results: List[HybridSearchResult]
    ) -> Answer:
        """抽取一般性答案"""
        # 综合多个结果
        top_results = results[:3]
        
        # 使用最相关的结果作为基础答案
        base_answer = top_results[0].content[:300]
        
        # 构建答案
        answer_text = base_answer
        if len(top_results) > 1:
            answer_text += "\n\n更多参考信息：\n"
            for i, r in enumerate(top_results[1:], 1):
                answer_text += f"{i}. {r.content[:150]}...\n"
        
        avg_confidence = np.mean([r.combined_score for r in top_results])
        
        return Answer(
            text=answer_text,
            confidence=avg_confidence,
            sources=[{
                'id': r.id,
                'preview': r.content[:100] + "...",
                'score': r.combined_score
            } for r in top_results],
            answer_type="direct"
        )


class MultiHopReasoner:
    """多跳推理器"""
    
    def __init__(
        self,
        search_service: HybridSearchService = None,
        embedding_service: EmbeddingService = None
    ):
        self.search_service = search_service or get_hybrid_search_service()
        self.embedding_service = embedding_service or get_embedding_service()
        self.max_hops = 3
    
    def reason(
        self,
        question: Question,
        initial_results: List[HybridSearchResult]
    ) -> Answer:
        """执行多跳推理"""
        reasoning_chain = []
        collected_results = list(initial_results)
        
        current_query = question.text
        
        for hop in range(self.max_hops):
            # 基于当前结果生成新的查询
            if hop > 0:
                current_query = self._generate_next_query(
                    question, 
                    collected_results,
                    reasoning_chain
                )
            
            # 搜索
            new_results = self.search_service.search(current_query, k=5)
            
            # 去重并合并
            existing_ids = {r.id for r in collected_results}
            for r in new_results:
                if r.id not in existing_ids:
                    collected_results.append(r)
            
            # 记录推理步骤
            reasoning_chain.append({
                'hop': hop + 1,
                'query': current_query,
                'results_found': len(new_results),
                'key_info': [r.content[:100] for r in new_results[:2]]
            })
            
            # 检查是否已有足够信息回答
            if self._can_answer(question, collected_results):
                break
        
        # 基于收集的所有结果生成答案
        answer = self._synthesize_answer(question, collected_results, reasoning_chain)
        answer.reasoning_chain = [str(step) for step in reasoning_chain]
        answer.answer_type = "multi_hop"
        
        return answer
    
    def _generate_next_query(
        self,
        question: Question,
        current_results: List[HybridSearchResult],
        reasoning_chain: List[Dict]
    ) -> str:
        """生成下一步查询"""
        # 基于当前结果提取关键信息
        key_terms = set()
        for r in current_results:
            # 简单提取关键词（名词）
            words = re.findall(r'[\u4e00-\u9fa5]{2,}|[a-zA-Z]{4,}', r.content)
            key_terms.update(words[:5])
        
        # 构建新查询
        base_query = question.text
        additional_terms = ' '.join(list(key_terms)[:3])
        
        return f"{base_query} {additional_terms}".strip()
    
    def _can_answer(
        self,
        question: Question,
        results: List[HybridSearchResult]
    ) -> bool:
        """检查是否有足够信息回答问题"""
        if not results:
            return False
        
        # 检查是否有高置信度的结果
        top_score = max(r.combined_score for r in results)
        
        # 如果找到非常高置信度的结果，可以回答
        if top_score > 0.85:
            return True
        
        # 检查是否有多个中等置信度的相关结果
        high_conf_results = [r for r in results if r.combined_score > 0.6]
        if len(high_conf_results) >= 3:
            return True
        
        return False
    
    def _synthesize_answer(
        self,
        question: Question,
        results: List[HybridSearchResult],
        reasoning_chain: List[Dict]
    ) -> Answer:
        """综合推理结果生成答案"""
        # 排序并取前几个结果
        results.sort(key=lambda x: x.combined_score, reverse=True)
        top_results = results[:5]
        
        # 基于问题类型生成答案
        if question.question_type == 'definition':
            # 查找定义性陈述
            for r in top_results:
                if '是' in r.content or '称为' in r.content or '定义为' in r.content:
                    return Answer(
                        text=r.content[:300],
                        confidence=r.combined_score,
                        sources=[{'id': r.id, 'score': r.combined_score} for r in top_results[:3]]
                    )
        
        # 默认综合答案
        answer_parts = []
        for r in top_results[:3]:
            # 提取关键句子
            sentences = re.split(r'[。！？]', r.content)
            if sentences:
                answer_parts.append(sentences[0])
        
        answer_text = '。'.join(answer_parts) + '。'
        avg_confidence = np.mean([r.combined_score for r in top_results])
        
        return Answer(
            text=answer_text,
            confidence=avg_confidence,
            sources=[{'id': r.id, 'score': r.combined_score} for r in top_results[:3]]
        )


class QASystem:
    """问答系统主类"""
    
    def __init__(
        self,
        search_service: HybridSearchService = None,
        embedding_service: EmbeddingService = None,
        enable_multi_hop: bool = True
    ):
        self.question_analyzer = QuestionAnalyzer()
        self.answer_extractor = AnswerExtractor(embedding_service)
        self.multi_hop_reasoner = MultiHopReasoner(search_service, embedding_service)
        self.search_service = search_service or get_hybrid_search_service()
        self.enable_multi_hop = enable_multi_hop
    
    def ask(
        self,
        question_text: str,
        use_multi_hop: bool = None
    ) -> Answer:
        """
        回答问题
        
        Args:
            question_text: 问题文本
            use_multi_hop: 是否使用多跳推理
        """
        if use_multi_hop is None:
            use_multi_hop = self.enable_multi_hop
        
        # 1. 分析问题
        question = self.question_analyzer.analyze(question_text)
        
        # 2. 执行初始搜索
        search_results = self.search_service.search(
            question_text,
            k=10,
            rerank=True
        )
        
        # 3. 检查是否需要多跳推理
        top_score = max([r.combined_score for r in search_results]) if search_results else 0
        
        if use_multi_hop and (top_score < 0.7 or question.question_type in ['comparison', 'proof']):
            # 使用多跳推理
            answer = self.multi_hop_reasoner.reason(question, search_results)
        else:
            # 直接从搜索结果抽取答案
            answer = self.answer_extractor.extract(question, search_results)
        
        return answer
    
    def ask_with_context(
        self,
        question_text: str,
        context: str = None,
        conversation_history: List[Dict] = None
    ) -> Answer:
        """带有上下文的问答"""
        # 构建增强查询
        enhanced_query = question_text
        
        if context:
            enhanced_query = f"{context} {question_text}"
        
        if conversation_history:
            # 提取历史中的关键信息
            recent_history = conversation_history[-3:]  # 最近3轮
            history_context = ' '.join([
                f"Q: {h.get('question', '')} A: {h.get('answer', '')}"
                for h in recent_history
            ])
            enhanced_query = f"{history_context} {enhanced_query}"
        
        return self.ask(enhanced_query)
    
    def batch_ask(self, questions: List[str]) -> List[Answer]:
        """批量回答问题"""
        return [self.ask(q) for q in questions]
    
    def get_suggested_questions(self, topic: str, k: int = 5) -> List[str]:
        """获取建议问题"""
        # 搜索相关文档
        results = self.search_service.search(topic, k=k*2)
        
        suggested = []
        question_templates = {
            'definition': [f'什么是{topic}？', f'{topic}的定义是什么？'],
            'property': [f'{topic}有什么性质？', f'{topic}的主要特点是什么？'],
            'application': [f'{topic}有哪些应用？', f'{topic}在数学中如何使用？'],
            'theorem': [f'关于{topic}有哪些重要定理？', f'{topic}定理的内容是什么？'],
        }
        
        # 基于搜索结果生成建议问题
        for template_list in question_templates.values():
            suggested.extend(template_list)
        
        return suggested[:k]


# 全局问答系统实例
_qa_system: Optional[QASystem] = None


def get_qa_system() -> QASystem:
    """获取全局问答系统实例"""
    global _qa_system
    if _qa_system is None:
        _qa_system = QASystem()
    return _qa_system
