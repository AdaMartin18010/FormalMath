"""
更新建议生成器模块

根据arXiv论文分析结果，生成FormalMath知识库更新建议
"""

import json
import logging
from typing import List, Dict, Optional, Set
from dataclasses import dataclass, field
from datetime import datetime
from collections import defaultdict
import yaml

from arxiv_client import ArxivPaper
from relevance_scorer import RelevanceScore, RelevanceScorer

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class UpdateSuggestion:
    """知识库更新建议"""
    suggestion_id: str
    type: str  # concept_update, new_concept, theorem_addition, reference_update, mathematician_addition
    title: str
    description: str
    
    # 相关论文
    related_papers: List[Dict] = field(default_factory=list)
    
    # 目标位置
    target_branch: str = ""
    target_concept: str = ""
    
    # 建议优先级
    priority: str = "medium"  # high, medium, low
    
    # 建议内容
    suggested_content: str = ""
    suggested_keywords: List[str] = field(default_factory=list)
    suggested_references: List[str] = field(default_factory=list)
    
    # 元数据
    created_at: datetime = field(default_factory=datetime.now)
    relevance_score: float = 0.0
    confidence: float = 0.5  # 置信度 0-1


@dataclass
class TrendingTopic:
    """热门话题"""
    topic: str
    frequency: int
    papers: List[Dict]
    related_concepts: List[str] = field(default_factory=list)
    trend_direction: str = "stable"  # rising, stable, declining


class UpdateSuggester:
    """更新建议生成器"""
    
    # 建议类型
    SUGGESTION_TYPES = {
        'concept_update': '概念内容更新',
        'new_concept': '新增概念',
        'theorem_addition': '新增定理/结果',
        'reference_update': '参考文献更新',
        'mathematician_addition': '新增数学家',
        'application_addition': '新增应用',
        'open_problem': '开放问题更新',
        'survey_addition': '综述推荐'
    }
    
    def __init__(self, config_path: str = "config.yaml"):
        """
        初始化建议生成器
        
        Args:
            config_path: 配置文件路径
        """
        with open(config_path, 'r', encoding='utf-8') as f:
            self.config = yaml.safe_load(f)
        
        # 加载知识库
        self.concepts = self._load_concepts()
        self.mathematicians = self._load_mathematicians()
        self.tracking_categories = {
            cat['id']: cat for cat in self.config.get('tracking_categories', [])
        }
        
        # 初始化评分器
        self.scorer = RelevanceScorer(config_path)
        
        # 建议阈值
        kb_config = self.config.get('knowledge_base', {})
        self.suggestion_threshold = kb_config.get('update_suggestion_threshold', 0.6)
    
    def _load_concepts(self) -> Dict:
        """加载概念数据"""
        concept_path = self.config.get('knowledge_base', {}).get('concept_graph_path')
        if concept_path:
            try:
                with open(concept_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        return {str(i): item for i, item in enumerate(data)}
                    return data
            except Exception as e:
                logger.warning(f"无法加载概念数据: {e}")
        return {}
    
    def _load_mathematicians(self) -> List[Dict]:
        """加载数学家数据"""
        math_path = self.config.get('knowledge_base', {}).get('mathematician_data_path')
        if math_path:
            try:
                with open(math_path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception as e:
                logger.warning(f"无法加载数学家数据: {e}")
        return []
    
    def generate_suggestions(
        self,
        papers_with_scores: List[tuple],
        category: Optional[str] = None
    ) -> List[UpdateSuggestion]:
        """
        生成更新建议
        
        Args:
            papers_with_scores: [(论文, 评分), ...]
            category: 分类（可选）
            
        Returns:
            建议列表
        """
        suggestions = []
        
        # 只处理高相关性的论文
        high_relevance = [
            (p, s) for p, s in papers_with_scores
            if s.overall_score >= self.suggestion_threshold
        ]
        
        logger.info(f"生成建议: {len(high_relevance)} 篇高相关性论文")
        
        # 生成各类建议
        suggestions.extend(self._suggest_concept_updates(high_relevance))
        suggestions.extend(self._suggest_new_concepts(high_relevance))
        suggestions.extend(self._suggest_theorem_additions(high_relevance))
        suggestions.extend(self._suggest_reference_updates(high_relevance))
        suggestions.extend(self._suggest_mathematician_additions(high_relevance))
        suggestions.extend(self._suggest_surveys(high_relevance))
        
        # 排序：按优先级和分数
        priority_order = {'high': 0, 'medium': 1, 'low': 2}
        suggestions.sort(
            key=lambda x: (priority_order.get(x.priority, 1), -x.relevance_score)
        )
        
        return suggestions
    
    def _suggest_concept_updates(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议概念内容更新"""
        suggestions = []
        
        # 按匹配的概念分组
        concept_papers = defaultdict(list)
        
        for paper, score in papers_with_scores:
            for concept_match in score.matched_concepts:
                concept = concept_match.get('concept', '')
                if concept:
                    concept_papers[concept].append((paper, score))
        
        # 为高频概念生成更新建议
        for concept, items in concept_papers.items():
            if len(items) >= 2:  # 至少2篇相关论文
                papers_info = [
                    {
                        'arxiv_id': p.arxiv_id,
                        'title': p.title,
                        'authors': p.authors[:3],
                        'score': s.overall_score
                    }
                    for p, s in items[:5]  # 限制数量
                ]
                
                avg_score = sum(s.overall_score for _, s in items) / len(items)
                
                suggestion = UpdateSuggestion(
                    suggestion_id=f"concept_update_{hash(concept) % 10000:04d}",
                    type='concept_update',
                    title=f"更新概念: {concept}",
                    description=f"基于{len(items)}篇最新论文，建议更新'{concept}'概念的内容",
                    related_papers=papers_info,
                    target_concept=concept,
                    priority='high' if avg_score > 0.8 else 'medium',
                    relevance_score=round(avg_score, 4),
                    confidence=min(0.9, 0.5 + len(items) * 0.1)
                )
                
                suggestions.append(suggestion)
        
        return suggestions
    
    def _suggest_new_concepts(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议新增概念"""
        suggestions = []
        
        # 查找论文中提到的但未在知识库中的新概念
        existing_concepts = set(self.concepts.keys())
        
        # 从论文标题和摘要中提取潜在新概念
        potential_concepts = self._extract_potential_concepts(papers_with_scores)
        
        for concept, papers in potential_concepts.items():
            if concept not in existing_concepts and len(papers) >= 2:
                papers_info = [
                    {
                        'arxiv_id': p.arxiv_id,
                        'title': p.title,
                        'abstract': p.abstract[:200] + '...' if len(p.abstract) > 200 else p.abstract
                    }
                    for p in papers[:3]
                ]
                
                suggestion = UpdateSuggestion(
                    suggestion_id=f"new_concept_{hash(concept) % 10000:04d}",
                    type='new_concept',
                    title=f"新增概念: {concept}",
                    description=f"在{len(papers)}篇论文中发现潜在新概念'{concept}'",
                    related_papers=papers_info,
                    priority='medium',
                    confidence=0.6
                )
                
                suggestions.append(suggestion)
        
        return suggestions
    
    def _extract_potential_concepts(
        self,
        papers_with_scores: List[tuple]
    ) -> Dict[str, List[ArxivPaper]]:
        """从论文中提取潜在新概念"""
        # 这是一个简化实现
        # 实际应该使用NLP技术提取
        
        potential = defaultdict(list)
        
        # 常见数学概念关键词模式
        concept_patterns = [
            r'\b(\w+\s+(?:theory|theorem|conjecture|hypothesis|principle))\b',
            r'\b(\w+\s+(?:space|manifold|variety|scheme|category|functor))\b',
            r'\b(\w+\s+(?:operator|transform|function|equation|inequality))\b',
        ]
        
        for paper, score in papers_with_scores:
            text = f"{paper.title} {paper.abstract[:500]}"
            
            # 简单提取：查找带引号的术语
            import re
            quoted = re.findall(r'"([^"]+)"', text)
            for term in quoted:
                if len(term) > 5 and len(term) < 50:
                    potential[term].append(paper)
        
        return potential
    
    def _suggest_theorem_additions(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议新增定理/结果"""
        suggestions = []
        
        # 查找标题中包含"theorem"、"proof"等关键词的论文
        theorem_keywords = ['theorem', 'proof', 'conjecture', 'result', 'formula']
        
        theorem_papers = []
        for paper, score in papers_with_scores:
            title_lower = paper.title.lower()
            if any(kw in title_lower for kw in theorem_keywords):
                theorem_papers.append((paper, score))
        
        if theorem_papers:
            papers_info = [
                {
                    'arxiv_id': p.arxiv_id,
                    'title': p.title,
                    'score': s.overall_score
                }
                for p, s in theorem_papers[:5]
            ]
            
            suggestion = UpdateSuggestion(
                suggestion_id=f"theorem_add_{datetime.now().strftime('%Y%m%d')}",
                type='theorem_addition',
                title="新增定理/结果",
                description=f"发现{len(theorem_papers)}篇包含新定理或重要结果的论文",
                related_papers=papers_info,
                priority='high',
                relevance_score=round(sum(s.overall_score for _, s in theorem_papers) / len(theorem_papers), 4),
                confidence=0.7
            )
            
            suggestions.append(suggestion)
        
        return suggestions
    
    def _suggest_reference_updates(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议参考文献更新"""
        suggestions = []
        
        # 收集所有高相关性论文作为潜在参考文献
        references = []
        for paper, score in papers_with_scores:
            if score.overall_score >= 0.7:
                references.append({
                    'arxiv_id': paper.arxiv_id,
                    'title': paper.title,
                    'authors': paper.authors,
                    'url': paper.abs_url,
                    'score': score.overall_score
                })
        
        if len(references) >= 3:
            # 按分类分组建议
            by_category = defaultdict(list)
            for ref in references:
                # 简化处理：基于arXiv ID前缀判断
                by_category['相关分支'].append(ref)
            
            for category, refs in by_category.items():
                suggestion = UpdateSuggestion(
                    suggestion_id=f"ref_update_{hash(category) % 10000:04d}",
                    type='reference_update',
                    title=f"更新参考文献列表 - {category}",
                    description=f"建议添加{len(refs)}篇最新相关论文到参考文献",
                    related_papers=refs[:10],
                    target_branch=category,
                    priority='medium',
                    confidence=0.8
                )
                
                suggestions.append(suggestion)
        
        return suggestions
    
    def _suggest_mathematician_additions(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议新增数学家"""
        suggestions = []
        
        # 收集所有作者
        all_authors = defaultdict(list)
        
        for paper, score in papers_with_scores:
            if score.overall_score >= 0.6:
                for author in paper.authors:
                    all_authors[author].append((paper, score))
        
        # 查找高频作者（可能是有影响力的新数学家）
        existing_names = set()
        for m in self.mathematicians:
            existing_names.add(m.get('EnglishName', '').lower())
            existing_names.add(m.get('ChineseName', ''))
        
        for author, papers in all_authors.items():
            if len(papers) >= 3:  # 至少3篇论文
                author_lower = author.lower()
                if not any(author_lower in existing.lower() for existing in existing_names if existing):
                    papers_info = [
                        {
                            'arxiv_id': p.arxiv_id,
                            'title': p.title,
                            'score': s.overall_score
                        }
                        for p, s in papers[:5]
                    ]
                    
                    suggestion = UpdateSuggestion(
                        suggestion_id=f"math_add_{hash(author) % 10000:04d}",
                        type='mathematician_addition',
                        title=f"关注数学家: {author}",
                        description=f"该作者在{len(papers)}篇高相关性论文中出现，可能是该领域活跃研究者",
                        related_papers=papers_info,
                        suggested_content=f"建议关注: {author}",
                        priority='low',
                        confidence=0.5
                    )
                    
                    suggestions.append(suggestion)
        
        return suggestions
    
    def _suggest_surveys(
        self,
        papers_with_scores: List[tuple]
    ) -> List[UpdateSuggestion]:
        """建议综述文章"""
        suggestions = []
        
        # 查找综述类论文
        survey_keywords = ['survey', 'review', 'overview', 'introduction', 'notes on']
        
        survey_papers = []
        for paper, score in papers_with_scores:
            title_lower = paper.title.lower()
            if any(kw in title_lower for kw in survey_keywords):
                survey_papers.append((paper, score))
        
        if survey_papers:
            papers_info = [
                {
                    'arxiv_id': p.arxiv_id,
                    'title': p.title,
                    'authors': p.authors,
                    'abstract': p.abstract[:300] + '...' if len(p.abstract) > 300 else p.abstract,
                    'score': s.overall_score
                }
                for p, s in survey_papers[:5]
            ]
            
            suggestion = UpdateSuggestion(
                suggestion_id=f"survey_{datetime.now().strftime('%Y%m%d')}",
                type='survey_addition',
                title="推荐综述文章",
                description=f"发现{len(survey_papers)}篇高质量综述文章，建议添加到学习资源",
                related_papers=papers_info,
                priority='medium',
                confidence=0.75
            )
            
            suggestions.append(suggestion)
        
        return suggestions
    
    def identify_trending_topics(
        self,
        papers_with_scores: List[tuple],
        top_n: int = 10
    ) -> List[TrendingTopic]:
        """
        识别热门话题
        
        Args:
            papers_with_scores: 带评分的论文列表
            top_n: 返回话题数量
            
        Returns:
            热门话题列表
        """
        # 收集所有关键词
        topic_counter = Counter()
        topic_papers = defaultdict(list)
        
        for paper, score in papers_with_scores:
            # 从标题提取关键词
            words = paper.title.lower().split()
            keywords = [w for w in words if len(w) > 4 and w.isalpha()]
            
            for kw in keywords:
                topic_counter[kw] += 1
                topic_papers[kw].append({
                    'arxiv_id': paper.arxiv_id,
                    'title': paper.title,
                    'score': score.overall_score
                })
        
        # 获取最频繁的话题
        trending = []
        for topic, freq in topic_counter.most_common(top_n * 2):  # 获取更多以过滤
            if freq >= 2:  # 至少出现2次
                papers_list = topic_papers[topic][:5]  # 限制数量
                
                trending.append(TrendingTopic(
                    topic=topic.capitalize(),
                    frequency=freq,
                    papers=papers_list,
                    trend_direction='rising' if freq >= 3 else 'stable'
                ))
        
        return trending[:top_n]
    
    def generate_weekly_summary(
        self,
        all_papers_by_category: Dict[str, List[tuple]]
    ) -> Dict:
        """
        生成周度总结
        
        Args:
            all_papers_by_category: {分类: [(论文, 评分), ...]}
            
        Returns:
            总结报告
        """
        summary = {
            'generated_at': datetime.now().isoformat(),
            'period': 'weekly',
            'total_papers': 0,
            'high_relevance_count': 0,
            'medium_relevance_count': 0,
            'by_category': {},
            'top_papers': [],
            'trending_topics': [],
            'update_suggestions': []
        }
        
        all_high_relevance = []
        
        for category, papers_with_scores in all_papers_by_category.items():
            cat_papers = len(papers_with_scores)
            high = sum(1 for _, s in papers_with_scores if s.overall_score >= 0.7)
            medium = sum(1 for _, s in papers_with_scores if 0.4 <= s.overall_score < 0.7)
            
            summary['total_papers'] += cat_papers
            summary['high_relevance_count'] += high
            summary['medium_relevance_count'] += medium
            
            cat_config = self.tracking_categories.get(category, {})
            summary['by_category'][category] = {
                'name': cat_config.get('name', category),
                'name_zh': cat_config.get('name_zh', ''),
                'total': cat_papers,
                'high': high,
                'medium': medium
            }
            
            # 收集高相关性论文
            high_rel = [(p, s) for p, s in papers_with_scores if s.overall_score >= 0.7]
            all_high_relevance.extend(high_rel)
        
        # 全局top论文
        all_high_relevance.sort(key=lambda x: x[1].overall_score, reverse=True)
        summary['top_papers'] = [
            {
                'arxiv_id': p.arxiv_id,
                'title': p.title,
                'authors': p.authors[:3],
                'category': p.primary_category,
                'score': s.overall_score
            }
            for p, s in all_high_relevance[:10]
        ]
        
        # 热门话题
        summary['trending_topics'] = [
            {
                'topic': t.topic,
                'frequency': t.frequency,
                'direction': t.trend_direction
            }
            for t in self.identify_trending_topics(all_high_relevance, top_n=10)
        ]
        
        # 生成更新建议
        suggestions = self.generate_suggestions(all_high_relevance)
        summary['update_suggestions'] = [
            {
                'id': s.suggestion_id,
                'type': s.type,
                'type_name': self.SUGGESTION_TYPES.get(s.type, s.type),
                'title': s.title,
                'priority': s.priority,
                'confidence': s.confidence,
                'paper_count': len(s.related_papers)
            }
            for s in suggestions[:20]  # 限制数量
        ]
        
        return summary


# 便捷函数
def generate_update_report(
    papers_with_scores: List[tuple],
    config_path: str = "config.yaml"
) -> List[UpdateSuggestion]:
    """生成更新建议报告"""
    suggester = UpdateSuggester(config_path)
    return suggester.generate_suggestions(papers_with_scores)


if __name__ == "__main__":
    # 测试代码
    from arxiv_client import create_client
    
    # 获取测试论文
    client = create_client()
    papers = client.search_by_category("math.CT", max_results=10)
    
    # 评分
    scorer = RelevanceScorer()
    scored = [(p, scorer.score_paper(p)) for p in papers]
    
    # 生成建议
    suggester = UpdateSuggester()
    suggestions = suggester.generate_suggestions(scored)
    
    print(f"\n生成 {len(suggestions)} 条更新建议:")
    for s in suggestions[:5]:
        print(f"\n[{s.priority.upper()}] {s.title}")
        print(f"  类型: {s.SUGGESTION_TYPES.get(s.type, s.type)}")
        print(f"  描述: {s.description}")
        print(f"  相关论文: {len(s.related_papers)} 篇")
