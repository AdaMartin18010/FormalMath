"""
相关性评分器模块

为arXiv论文计算与FormalMath知识库的相关性分数
"""

import json
import logging
import re
from typing import List, Dict, Optional, Tuple, Set
from dataclasses import dataclass, field
from collections import Counter
import yaml

from arxiv_client import ArxivPaper

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class RelevanceScore:
    """相关性评分结果"""
    overall_score: float  # 总体分数 0-1
    keyword_score: float  # 关键词匹配分数
    concept_score: float  # 概念匹配分数
    mathematician_score: float  # 数学家匹配分数
    msc_score: float  # MSC分类匹配分数
    
    # 详细信息
    matched_keywords: Dict[str, float] = field(default_factory=dict)  # 关键词及其权重
    matched_concepts: List[Dict] = field(default_factory=list)  # 匹配的概念
    matched_mathematicians: List[str] = field(default_factory=list)  # 匹配的数学家
    matched_msc: List[str] = field(default_factory=list)  # 匹配的MSC分类
    
    # 评分解释
    explanation: str = ""


class RelevanceScorer:
    """相关性评分器"""
    
    def __init__(self, config_path: str = "config.yaml"):
        """
        初始化评分器
        
        Args:
            config_path: 配置文件路径
        """
        with open(config_path, 'r', encoding='utf-8') as f:
            self.config = yaml.safe_load(f)
        
        self.scoring_config = self.config.get('relevance_scoring', {})
        self.weights = self.scoring_config.get('weights', {})
        
        # 加载知识库数据
        self.concepts = self._load_concepts()
        self.mathematicians = self._load_mathematicians()
        self.msc_data = self._load_msc_data()
        
        # 编译正则表达式缓存
        self._regex_cache = {}
    
    def _load_concepts(self) -> Dict:
        """加载概念数据"""
        concept_path = self.config.get('knowledge_base', {}).get('concept_graph_path')
        if concept_path:
            try:
                with open(concept_path, 'r', encoding='utf-8') as f:
                    return json.load(f)
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
    
    def _load_msc_data(self) -> Dict:
        """加载MSC分类数据"""
        msc_path = self.config.get('knowledge_base', {}).get('msc_data_path')
        if msc_path:
            try:
                with open(msc_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            except Exception as e:
                logger.warning(f"无法加载MSC数据: {e}")
        return {}
    
    def score_paper(
        self,
        paper: ArxivPaper,
        category: Optional[str] = None
    ) -> RelevanceScore:
        """
        为单篇论文计算相关性分数
        
        Args:
            paper: 论文
            category: 所属分类（可选）
            
        Returns:
            相关性评分
        """
        # 计算各维度分数
        keyword_result = self._score_keywords(paper, category)
        concept_result = self._score_concepts(paper)
        mathematician_result = self._score_mathematicians(paper)
        msc_result = self._score_msc(paper)
        
        # 计算加权总分
        weights = self.weights
        overall = (
            keyword_result['score'] * weights.get('keyword_match', 0.35) +
            concept_result['score'] * weights.get('concept_match', 0.30) +
            mathematician_result['score'] * weights.get('mathematician_match', 0.15) +
            msc_result['score'] * weights.get('msc_match', 0.20)
        )
        
        # 确保分数在0-1范围内
        overall = min(1.0, max(0.0, overall))
        
        # 生成解释
        explanation = self._generate_explanation(
            overall,
            keyword_result,
            concept_result,
            mathematician_result,
            msc_result
        )
        
        return RelevanceScore(
            overall_score=round(overall, 4),
            keyword_score=round(keyword_result['score'], 4),
            concept_score=round(concept_result['score'], 4),
            mathematician_score=round(mathematician_result['score'], 4),
            msc_score=round(msc_result['score'], 4),
            matched_keywords=keyword_result.get('matches', {}),
            matched_concepts=concept_result.get('matches', []),
            matched_mathematicians=mathematician_result.get('matches', []),
            matched_msc=msc_result.get('matches', []),
            explanation=explanation
        )
    
    def _score_keywords(
        self,
        paper: ArxivPaper,
        category: Optional[str] = None
    ) -> Dict:
        """
        关键词匹配评分
        
        基于标题和摘要中的关键词匹配
        """
        matches = {}
        
        # 获取该分类的关键词
        tracking_categories = {
            cat['id']: cat for cat in self.config.get('tracking_categories', [])
        }
        
        keywords = []
        if category and category in tracking_categories:
            keywords = tracking_categories[category].get('keywords', [])
        else:
            # 使用所有分类的关键词
            for cat in tracking_categories.values():
                keywords.extend(cat.get('keywords', []))
            keywords = list(set(keywords))  # 去重
        
        # 定义权重
        keyword_config = self.scoring_config.get('keyword_match', {})
        title_weight = keyword_config.get('title_weight', 3.0)
        abstract_weight = keyword_config.get('abstract_weight', 1.5)
        
        title_lower = paper.title.lower()
        abstract_lower = paper.abstract.lower()
        
        for keyword in keywords:
            keyword_lower = keyword.lower()
            score = 0.0
            
            # 标题匹配（完全匹配权重更高）
            if keyword_lower in title_lower:
                # 完全单词匹配
                if re.search(r'\b' + re.escape(keyword_lower) + r'\b', title_lower):
                    score += title_weight
                else:
                    score += title_weight * 0.5
            
            # 摘要匹配
            if keyword_lower in abstract_lower:
                count = abstract_lower.count(keyword_lower)
                score += min(abstract_weight * count, abstract_weight * 3)  # 限制上限
            
            if score > 0:
                matches[keyword] = round(score, 2)
        
        # 计算归一化分数
        if matches:
            raw_score = sum(matches.values())
            # 使用sigmoid-like函数归一化到0-1
            normalized_score = min(1.0, raw_score / 10.0)
        else:
            normalized_score = 0.0
        
        return {
            'score': normalized_score,
            'matches': matches,
            'total_keywords': len(keywords),
            'matched_count': len(matches)
        }
    
    def _score_concepts(self, paper: ArxivPaper) -> Dict:
        """
        概念匹配评分
        
        匹配论文中的数学概念
        """
        matches = []
        
        # 从概念表中提取概念名称
        concept_names = self._extract_concept_names()
        
        text = f"{paper.title} {paper.abstract}".lower()
        
        for concept in concept_names:
            concept_lower = concept.lower()
            
            if concept_lower in text:
                # 检查是否是完全单词匹配
                if re.search(r'\b' + re.escape(concept_lower) + r'\b', text):
                    matches.append({
                        'concept': concept,
                        'match_type': 'exact',
                        'weight': 1.0
                    })
                else:
                    matches.append({
                        'concept': concept,
                        'match_type': 'partial',
                        'weight': 0.5
                    })
        
        # 计算分数
        if matches:
            total_weight = sum(m['weight'] for m in matches)
            # 归一化
            score = min(1.0, total_weight / 5.0)  # 假设5个概念匹配为满分
        else:
            score = 0.0
        
        return {
            'score': score,
            'matches': matches[:10],  # 限制返回数量
            'total_concepts': len(concept_names),
            'matched_count': len(matches)
        }
    
    def _extract_concept_names(self) -> List[str]:
        """从概念数据中提取概念名称"""
        names = []
        
        # 尝试从多语言概念表中提取
        if isinstance(self.concepts, list):
            for item in self.concepts:
                if isinstance(item, dict):
                    # 尝试不同的字段名
                    for key in ['Chinese', 'English', 'concept', 'name']:
                        if key in item and item[key]:
                            names.append(str(item[key]))
        elif isinstance(self.concepts, dict):
            for key in self.concepts.keys():
                names.append(str(key))
        
        return list(set(names))  # 去重
    
    def _score_mathematicians(self, paper: ArxivPaper) -> Dict:
        """
        数学家匹配评分
        
        检查论文是否涉及已知数学家
        """
        matches = []
        
        text = f"{paper.title} {paper.abstract}".lower()
        
        for math_data in self.mathematicians:
            # 检查英文名
            eng_name = math_data.get('EnglishName', '')
            if eng_name:
                # 提取姓氏
                last_name = self._extract_last_name(eng_name)
                if last_name and last_name.lower() in text:
                    matches.append({
                        'name': eng_name,
                        'chinese_name': math_data.get('ChineseName', ''),
                        'match_type': 'name_in_text'
                    })
            
            # 检查中文名
            cn_name = math_data.get('ChineseName', '')
            if cn_name and cn_name in paper.title + paper.abstract:
                matches.append({
                    'name': eng_name or cn_name,
                    'chinese_name': cn_name,
                    'match_type': 'chinese_name'
                })
            
            # 检查作者匹配
            for author in paper.authors:
                if eng_name and self._match_author_name(author, eng_name):
                    matches.append({
                        'name': eng_name,
                        'chinese_name': cn_name,
                        'match_type': 'author'
                    })
                    break
        
        # 去重
        seen = set()
        unique_matches = []
        for m in matches:
            key = m.get('name', '')
            if key and key not in seen:
                seen.add(key)
                unique_matches.append(m)
        
        # 计算分数
        if unique_matches:
            score = min(1.0, len(unique_matches) * 0.2)  # 每个数学家0.2分，最高1分
        else:
            score = 0.0
        
        return {
            'score': score,
            'matches': unique_matches[:5],  # 限制返回数量
            'matched_count': len(unique_matches)
        }
    
    def _extract_last_name(self, full_name: str) -> Optional[str]:
        """从全名提取姓氏"""
        # 简单实现：取最后一个单词
        parts = full_name.replace('(', '').replace(')', '').split()
        if parts:
            return parts[-1]
        return None
    
    def _match_author_name(self, author: str, target_name: str) -> bool:
        """匹配作者名"""
        author_lower = author.lower()
        target_lower = target_name.lower()
        
        # 直接包含
        if target_lower in author_lower:
            return True
        
        # 姓氏匹配
        target_last = self._extract_last_name(target_name)
        if target_last and target_last.lower() in author_lower:
            return True
        
        return False
    
    def _score_msc(self, paper: ArxivPaper) -> Dict:
        """
        MSC分类匹配评分
        
        基于MSC分类匹配
        """
        matches = []
        
        if not paper.msc_classes:
            return {'score': 0.0, 'matches': [], 'matched_count': 0}
        
        # 获取相关MSC分类
        relevant_msc = self._get_relevant_msc_codes()
        
        for msc in paper.msc_classes:
            # 完全匹配
            if msc in relevant_msc:
                matches.append({
                    'msc': msc,
                    'match_type': 'exact',
                    'weight': 1.0
                })
            else:
                # 前缀匹配
                for ref_msc in relevant_msc:
                    if msc.startswith(ref_msc[:2]) or ref_msc.startswith(msc[:2]):
                        matches.append({
                            'msc': msc,
                            'match_type': 'prefix',
                            'weight': 0.5
                        })
                        break
        
        # 计算分数
        if matches:
            total_weight = sum(m['weight'] for m in matches)
            score = min(1.0, total_weight / 3.0)  # 3个匹配为满分
        else:
            score = 0.0
        
        return {
            'score': score,
            'matches': [m['msc'] for m in matches],
            'matched_count': len(matches)
        }
    
    def _get_relevant_msc_codes(self) -> Set[str]:
        """获取相关MSC分类代码"""
        codes = set()
        
        # 从配置中提取相关MSC分类
        # 这里简化处理，实际应该从MSC数据中提取
        # 主要数学领域的MSC代码前缀
        msc_prefixes = {
            'math.AG': ['14'],  # 代数几何
            'math.AT': ['55'],  # 代数拓扑
            'math.CT': ['18'],  # 范畴论
            'math.GR': ['20'],  # 群论
            'math.NT': ['11'],  # 数论
            'math.CV': ['30', '32'],  # 复分析
            'math.FA': ['46'],  # 泛函分析
            'math.DG': ['53'],  # 微分几何
            'math.GT': ['57'],  # 几何拓扑
            'math.LO': ['03'],  # 逻辑
            'math.PR': ['60'],  # 概率论
            'math.ST': ['62'],  # 统计
            'math.NA': ['65'],  # 数值分析
            'math.RA': ['16', '17'],  # 环与代数
            'math.RT': ['20', '22'],  # 表示论
        }
        
        for prefixes in msc_prefixes.values():
            codes.update(prefixes)
        
        return codes
    
    def _generate_explanation(
        self,
        overall: float,
        keyword_result: Dict,
        concept_result: Dict,
        mathematician_result: Dict,
        msc_result: Dict
    ) -> str:
        """生成评分解释"""
        explanations = []
        
        if overall >= 0.7:
            explanations.append("高相关性论文")
        elif overall >= 0.4:
            explanations.append("中等相关性论文")
        else:
            explanations.append("低相关性论文")
        
        # 关键词匹配
        if keyword_result['matched_count'] > 0:
            explanations.append(
                f"匹配{keyword_result['matched_count']}个关键词"
            )
        
        # 概念匹配
        if concept_result['matched_count'] > 0:
            explanations.append(
                f"涉及{concept_result['matched_count']}个数学概念"
            )
        
        # 数学家
        if mathematician_result['matched_count'] > 0:
            names = [m.get('chinese_name') or m.get('name', '').split()[0]
                     for m in mathematician_result['matches'][:2]]
            explanations.append(f"涉及数学家: {', '.join(names)}")
        
        return "; ".join(explanations)
    
    def score_batch(
        self,
        papers: List[ArxivPaper],
        min_score: float = 0.0
    ) -> List[Tuple[ArxivPaper, RelevanceScore]]:
        """
        批量评分
        
        Args:
            papers: 论文列表
            min_score: 最小分数阈值
            
        Returns:
            [(论文, 评分), ...] 按分数降序排列
        """
        results = []
        
        for paper in papers:
            score = self.score_paper(paper)
            
            if score.overall_score >= min_score:
                results.append((paper, score))
        
        # 按分数降序排列
        results.sort(key=lambda x: x[1].overall_score, reverse=True)
        
        return results
    
    def get_top_papers(
        self,
        papers: List[ArxivPaper],
        top_n: int = 10,
        min_score: float = 0.3
    ) -> List[Tuple[ArxivPaper, RelevanceScore]]:
        """
        获取top N相关论文
        
        Args:
            papers: 论文列表
            top_n: 返回数量
            min_score: 最小分数阈值
            
        Returns:
            Top N相关论文
        """
        scored = self.score_batch(papers, min_score)
        return scored[:top_n]


# 便捷函数
def quick_score(
    paper: ArxivPaper,
    config_path: str = "config.yaml"
) -> RelevanceScore:
    """快速评分"""
    scorer = RelevanceScorer(config_path)
    return scorer.score_paper(paper)


def categorize_by_relevance(
    papers: List[ArxivPaper],
    config_path: str = "config.yaml"
) -> Dict[str, List[Tuple[ArxivPaper, RelevanceScore]]]:
    """
    按相关性分类论文
    
    Returns:
        {
            'high': [...],    # score >= 0.7
            'medium': [...],  # 0.4 <= score < 0.7
            'low': [...]      # score < 0.4
        }
    """
    scorer = RelevanceScorer(config_path)
    scored = scorer.score_batch(papers, min_score=0.0)
    
    result = {'high': [], 'medium': [], 'low': []}
    
    for paper, score in scored:
        if score.overall_score >= 0.7:
            result['high'].append((paper, score))
        elif score.overall_score >= 0.4:
            result['medium'].append((paper, score))
        else:
            result['low'].append((paper, score))
    
    return result


if __name__ == "__main__":
    # 测试代码
    from arxiv_client import create_client
    
    # 获取测试论文
    client = create_client()
    papers = client.search_by_category("math.CT", max_results=5)
    
    # 评分
    scorer = RelevanceScorer()
    
    print("\n论文相关性评分测试:")
    for paper in papers:
        score = scorer.score_paper(paper)
        print(f"\n标题: {paper.title[:50]}...")
        print(f"  总体分数: {score.overall_score:.2f}")
        print(f"  关键词: {score.keyword_score:.2f}")
        print(f"  概念: {score.concept_score:.2f}")
        print(f"  解释: {score.explanation}")
