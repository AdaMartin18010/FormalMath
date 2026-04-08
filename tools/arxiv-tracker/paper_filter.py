"""
论文筛选器模块

基于关键词、MSC分类、日期等条件筛选arXiv论文
"""

import re
import logging
from typing import List, Dict, Optional, Callable, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
import yaml

from arxiv_client import ArxivPaper

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class FilterCriteria:
    """筛选条件数据类"""
    # 关键词筛选
    include_keywords: List[str] = field(default_factory=list)
    exclude_keywords: List[str] = field(default_factory=list)
    require_all_keywords: bool = False  # 是否需要包含所有关键词
    
    # 作者筛选
    include_authors: List[str] = field(default_factory=list)
    exclude_authors: List[str] = field(default_factory=list)
    
    # 分类筛选
    categories: List[str] = field(default_factory=list)
    
    # MSC分类筛选
    msc_classes: List[str] = field(default_factory=list)
    msc_match_prefix: bool = True  # 是否匹配前缀
    
    # 日期筛选
    date_from: Optional[datetime] = None
    date_to: Optional[datetime] = None
    
    # 其他筛选
    min_authors: Optional[int] = None
    max_authors: Optional[int] = None
    has_doi: Optional[bool] = None
    has_journal_ref: Optional[bool] = None


@dataclass
class FilterResult:
    """筛选结果"""
    paper: ArxivPaper
    passed: bool
    reasons: List[str] = field(default_factory=list)
    matched_keywords: List[str] = field(default_factory=list)
    relevance_hints: Dict = field(default_factory=dict)


class PaperFilter:
    """论文筛选器"""
    
    def __init__(self, config_path: str = "config.yaml"):
        """
        初始化筛选器
        
        Args:
            config_path: 配置文件路径
        """
        with open(config_path, 'r', encoding='utf-8') as f:
            self.config = yaml.safe_load(f)
        
        self.filter_config = self.config.get('filter', {})
        
        # 加载默认排除关键词
        self.default_exclude_keywords = self.filter_config.get('exclude_keywords', [])
        
        # 加载跟踪的分类配置
        self.tracking_categories = {
            cat['id']: cat for cat in self.config.get('tracking_categories', [])
        }
        
        # 编译正则表达式缓存
        self._regex_cache: Dict[str, re.Pattern] = {}
    
    def _get_regex(self, pattern: str, case_sensitive: bool = False) -> re.Pattern:
        """获取或编译正则表达式"""
        cache_key = f"{pattern}:{case_sensitive}"
        if cache_key not in self._regex_cache:
            flags = 0 if case_sensitive else re.IGNORECASE
            self._regex_cache[cache_key] = re.compile(pattern, flags)
        return self._regex_cache[cache_key]
    
    def filter_papers(
        self,
        papers: List[ArxivPaper],
        criteria: FilterCriteria,
        return_rejected: bool = False
    ) -> List[FilterResult]:
        """
        筛选论文列表
        
        Args:
            papers: 论文列表
            criteria: 筛选条件
            return_rejected: 是否返回被拒绝的论文
            
        Returns:
            筛选结果列表
        """
        results = []
        
        for paper in papers:
            result = self.evaluate_paper(paper, criteria)
            
            if result.passed or return_rejected:
                results.append(result)
        
        return results
    
    def evaluate_paper(self, paper: ArxivPaper, criteria: FilterCriteria) -> FilterResult:
        """
        评估单篇论文是否符合条件
        
        Args:
            paper: 论文
            criteria: 筛选条件
            
        Returns:
            筛选结果
        """
        reasons = []
        matched_keywords = []
        relevance_hints = {}
        passed = True
        
        # 1. 排除关键词检查
        exclude_keywords = criteria.exclude_keywords or self.default_exclude_keywords
        for keyword in exclude_keywords:
            if self._contains_keyword(paper, keyword):
                passed = False
                reasons.append(f"包含排除关键词: {keyword}")
                break
        
        # 2. 必须包含关键词检查
        if passed and criteria.include_keywords:
            matched = []
            for keyword in criteria.include_keywords:
                if self._contains_keyword(paper, keyword):
                    matched.append(keyword)
            
            if criteria.require_all_keywords:
                if len(matched) != len(criteria.include_keywords):
                    passed = False
                    reasons.append(f"未包含所有必须关键词")
            else:
                if not matched:
                    passed = False
                    reasons.append(f"未包含任何关键词")
            
            matched_keywords = matched
            relevance_hints['keyword_matches'] = len(matched)
        
        # 3. 作者筛选
        if passed and criteria.include_authors:
            author_matched = any(
                self._match_author(author, criteria.include_authors)
                for author in paper.authors
            )
            if not author_matched:
                passed = False
                reasons.append("作者不匹配")
        
        if passed and criteria.exclude_authors:
            author_excluded = any(
                self._match_author(author, criteria.exclude_authors)
                for author in paper.authors
            )
            if author_excluded:
                passed = False
                reasons.append("作者在排除列表中")
        
        # 4. 分类筛选
        if passed and criteria.categories:
            cat_matched = any(
                cat in criteria.categories for cat in paper.categories
            )
            if not cat_matched:
                passed = False
                reasons.append("分类不匹配")
        
        # 5. MSC分类筛选
        if passed and criteria.msc_classes:
            msc_matched = self._match_msc_classes(
                paper.msc_classes,
                criteria.msc_classes,
                criteria.msc_match_prefix
            )
            if not msc_matched:
                passed = False
                reasons.append("MSC分类不匹配")
        
        # 6. 日期筛选
        if passed and criteria.date_from:
            if paper.published and paper.published < criteria.date_from:
                passed = False
                reasons.append("发布日期早于指定范围")
        
        if passed and criteria.date_to:
            if paper.published and paper.published > criteria.date_to:
                passed = False
                reasons.append("发布日期晚于指定范围")
        
        # 7. 作者数量筛选
        if passed and criteria.min_authors is not None:
            if len(paper.authors) < criteria.min_authors:
                passed = False
                reasons.append(f"作者数量少于{criteria.min_authors}")
        
        if passed and criteria.max_authors is not None:
            if len(paper.authors) > criteria.max_authors:
                passed = False
                reasons.append(f"作者数量多于{criteria.max_authors}")
        
        # 8. DOI筛选
        if passed and criteria.has_doi is not None:
            has_doi = paper.doi is not None and paper.doi.strip() != ""
            if has_doi != criteria.has_doi:
                passed = False
                reasons.append("DOI条件不满足")
        
        # 9. 期刊引用筛选
        if passed and criteria.has_journal_ref is not None:
            has_ref = paper.journal_ref is not None and paper.journal_ref.strip() != ""
            if has_ref != criteria.has_journal_ref:
                passed = False
                reasons.append("期刊引用条件不满足")
        
        # 计算相关性提示
        if passed:
            relevance_hints = self._calculate_relevance_hints(paper, criteria)
        
        return FilterResult(
            paper=paper,
            passed=passed,
            reasons=reasons,
            matched_keywords=matched_keywords,
            relevance_hints=relevance_hints
        )
    
    def _contains_keyword(self, paper: ArxivPaper, keyword: str) -> bool:
        """
        检查论文是否包含关键词
        
        在标题、摘要、作者中搜索
        """
        pattern = self._get_regex(r'\b' + re.escape(keyword) + r'\b')
        
        # 检查标题
        if pattern.search(paper.title):
            return True
        
        # 检查摘要
        if pattern.search(paper.abstract):
            return True
        
        # 检查作者
        for author in paper.authors:
            if pattern.search(author):
                return True
        
        return False
    
    def _match_author(self, author: str, author_list: List[str]) -> bool:
        """匹配作者"""
        author_lower = author.lower()
        for target in author_list:
            if target.lower() in author_lower or author_lower in target.lower():
                return True
        return False
    
    def _match_msc_classes(
        self,
        paper_msc: List[str],
        target_msc: List[str],
        match_prefix: bool
    ) -> bool:
        """匹配MSC分类"""
        if not paper_msc:
            return False
        
        for target in target_msc:
            for msc in paper_msc:
                if match_prefix:
                    if msc.startswith(target) or target.startswith(msc):
                        return True
                else:
                    if msc == target:
                        return True
        
        return False
    
    def _calculate_relevance_hints(
        self,
        paper: ArxivPaper,
        criteria: FilterCriteria
    ) -> Dict:
        """计算相关性提示"""
        hints = {}
        
        # 关键词匹配数
        if criteria.include_keywords:
            hints['keyword_match_count'] = sum(
                1 for kw in criteria.include_keywords
                if self._contains_keyword(paper, kw)
            )
        
        # 标题关键词密度
        hints['title_word_count'] = len(paper.title.split())
        
        # 摘要长度
        hints['abstract_length'] = len(paper.abstract)
        
        # 作者数量
        hints['author_count'] = len(paper.authors)
        
        # 是否有DOI
        hints['has_doi'] = paper.doi is not None
        
        # 是否有期刊引用
        hints['has_journal_ref'] = paper.journal_ref is not None
        
        return hints
    
    def create_category_criteria(self, category: str) -> FilterCriteria:
        """
        为指定分类创建筛选条件
        
        Args:
            category: arXiv分类ID
            
        Returns:
            筛选条件
        """
        cat_config = self.tracking_categories.get(category, {})
        
        return FilterCriteria(
            categories=[category],
            include_keywords=cat_config.get('keywords', []),
            exclude_keywords=self.default_exclude_keywords,
            date_from=datetime.now() - timedelta(
                days=self.filter_config.get('lookback_days', 7)
            )
        )
    
    def batch_filter_by_categories(
        self,
        papers_by_category: Dict[str, List[ArxivPaper]]
    ) -> Dict[str, List[FilterResult]]:
        """
        批量按分类筛选论文
        
        Args:
            papers_by_category: {分类: 论文列表}
            
        Returns:
            {分类: 筛选结果列表}
        """
        results = {}
        
        for category, papers in papers_by_category.items():
            logger.info(f"筛选分类 {category}: {len(papers)} 篇论文")
            
            criteria = self.create_category_criteria(category)
            filtered = self.filter_papers(papers, criteria)
            
            # 只保留通过的
            passed = [r for r in filtered if r.passed]
            results[category] = passed
            
            logger.info(f"  通过筛选: {len(passed)} 篇")
        
        return results
    
    def deduplicate_papers(
        self,
        results_by_category: Dict[str, List[FilterResult]]
    ) -> Dict[str, List[FilterResult]]:
        """
        去重论文（一篇论文可能属于多个分类）
        
        Args:
            results_by_category: 按分类的筛选结果
            
        Returns:
            去重后的结果
        """
        seen_ids: Set[str] = set()
        deduplicated = {}
        
        for category, results in results_by_category.items():
            unique_results = []
            
            for result in results:
                if result.paper.arxiv_id not in seen_ids:
                    seen_ids.add(result.paper.arxiv_id)
                    unique_results.append(result)
            
            deduplicated[category] = unique_results
        
        return deduplicated
    
    def create_advanced_filter(
        self,
        category: str,
        custom_keywords: Optional[List[str]] = None,
        min_date: Optional[datetime] = None,
        require_journal: bool = False
    ) -> FilterCriteria:
        """
        创建高级筛选条件
        
        Args:
            category: 分类
            custom_keywords: 自定义关键词
            min_date: 最小日期
            require_journal: 是否要求期刊引用
            
        Returns:
            筛选条件
        """
        cat_config = self.tracking_categories.get(category, {})
        keywords = custom_keywords or cat_config.get('keywords', [])
        
        return FilterCriteria(
            categories=[category],
            include_keywords=keywords,
            exclude_keywords=self.default_exclude_keywords,
            date_from=min_date or datetime.now() - timedelta(
                days=self.filter_config.get('lookback_days', 7)
            ),
            has_journal_ref=require_journal if require_journal else None
        )


# 便捷函数
def quick_filter(
    papers: List[ArxivPaper],
    keywords: List[str],
    exclude: List[str] = None,
    config_path: str = "config.yaml"
) -> List[ArxivPaper]:
    """
    快速筛选论文
    
    Args:
        papers: 论文列表
        keywords: 关键词列表
        exclude: 排除关键词
        config_path: 配置文件路径
        
    Returns:
        筛选后的论文列表
    """
    filter_ = PaperFilter(config_path)
    criteria = FilterCriteria(
        include_keywords=keywords,
        exclude_keywords=exclude or []
    )
    
    results = filter_.filter_papers(papers, criteria)
    return [r.paper for r in results if r.passed]


def filter_by_date_range(
    papers: List[ArxivPaper],
    days: int = 7
) -> List[ArxivPaper]:
    """
    按日期范围筛选
    
    Args:
        papers: 论文列表
        days: 天数
        
    Returns:
        筛选后的论文列表
    """
    cutoff = datetime.now() - timedelta(days=days)
    return [p for p in papers if p.published and p.published >= cutoff]


if __name__ == "__main__":
    # 测试代码
    from arxiv_client import create_client
    
    # 获取一些测试论文
    client = create_client()
    papers = client.search_by_category("math.AG", max_results=10)
    
    # 测试筛选器
    filter_ = PaperFilter()
    criteria = FilterCriteria(
        include_keywords=["algebraic", "geometry", "variety"],
        exclude_keywords=["withdrawn"]
    )
    
    results = filter_.filter_papers(papers, criteria, return_rejected=True)
    
    print(f"\n共评估 {len(results)} 篇论文:")
    print(f"通过: {sum(1 for r in results if r.passed)}")
    print(f"拒绝: {sum(1 for r in results if not r.passed)}")
    
    for result in results[:3]:
        status = "✓" if result.passed else "✗"
        print(f"\n{status} {result.paper.title[:60]}...")
        if result.matched_keywords:
            print(f"   匹配关键词: {', '.join(result.matched_keywords)}")
        if result.reasons:
            print(f"   原因: {', '.join(result.reasons)}")
