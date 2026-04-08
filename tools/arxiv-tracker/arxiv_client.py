"""
arXiv API客户端模块

提供与arXiv API交互的功能，包括：
- 搜索论文
- 获取论文元数据
- 处理API响应
- 速率限制管理

arXiv API文档: https://arxiv.org/help/api/
"""

import time
import logging
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass, field
from datetime import datetime, timedelta
import xml.etree.ElementTree as ET
from urllib.parse import urlencode, quote
import requests
import yaml

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class ArxivPaper:
    """arXiv论文数据类"""
    arxiv_id: str
    title: str
    authors: List[str]
    abstract: str
    categories: List[str]
    primary_category: str
    published: datetime
    updated: datetime
    doi: Optional[str] = None
    journal_ref: Optional[str] = None
    comment: Optional[str] = None
    pdf_url: Optional[str] = None
    abs_url: Optional[str] = None
    msc_classes: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict:
        """转换为字典格式"""
        return {
            "arxiv_id": self.arxiv_id,
            "title": self.title,
            "authors": self.authors,
            "abstract": self.abstract,
            "categories": self.categories,
            "primary_category": self.primary_category,
            "published": self.published.isoformat() if self.published else None,
            "updated": self.updated.isoformat() if self.updated else None,
            "doi": self.doi,
            "journal_ref": self.journal_ref,
            "comment": self.comment,
            "pdf_url": self.pdf_url,
            "abs_url": self.abs_url,
            "msc_classes": self.msc_classes
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'ArxivPaper':
        """从字典创建实例"""
        return cls(
            arxiv_id=data["arxiv_id"],
            title=data["title"],
            authors=data["authors"],
            abstract=data["abstract"],
            categories=data["categories"],
            primary_category=data["primary_category"],
            published=datetime.fromisoformat(data["published"]) if data.get("published") else None,
            updated=datetime.fromisoformat(data["updated"]) if data.get("updated") else None,
            doi=data.get("doi"),
            journal_ref=data.get("journal_ref"),
            comment=data.get("comment"),
            pdf_url=data.get("pdf_url"),
            abs_url=data.get("abs_url"),
            msc_classes=data.get("msc_classes", [])
        )


class ArxivClient:
    """arXiv API客户端"""
    
    # arXiv API命名空间
    ATOM_NS = "{http://www.w3.org/2005/Atom}"
    ARXIV_NS = "{http://arxiv.org/schemas/atom}"
    
    def __init__(self, config_path: str = "config.yaml"):
        """
        初始化arXiv客户端
        
        Args:
            config_path: 配置文件路径
        """
        with open(config_path, 'r', encoding='utf-8') as f:
            self.config = yaml.safe_load(f)
        
        self.arxiv_config = self.config['arxiv']
        self.base_url = self.arxiv_config['api_base_url']
        self.rate_limit = self.arxiv_config['rate_limit']
        self.timeout = self.arxiv_config['timeout']
        self.max_results = self.arxiv_config['max_results_per_query']
        self.retry_attempts = self.arxiv_config['retry_attempts']
        self.retry_delay = self.arxiv_config['retry_delay']
        
        # 速率限制控制
        self._last_request_time = 0
        self._min_interval = 1.0 / self.rate_limit
    
    def _wait_for_rate_limit(self):
        """等待以遵守速率限制"""
        current_time = time.time()
        time_since_last = current_time - self._last_request_time
        
        if time_since_last < self._min_interval:
            sleep_time = self._min_interval - time_since_last
            time.sleep(sleep_time)
        
        self._last_request_time = time.time()
    
    def _make_request(self, url: str) -> Optional[str]:
        """
        发送HTTP请求，带重试机制
        
        Args:
            url: 请求URL
            
        Returns:
            响应内容或None
        """
        for attempt in range(self.retry_attempts):
            try:
                self._wait_for_rate_limit()
                
                response = requests.get(url, timeout=self.timeout)
                response.raise_for_status()
                
                return response.text
                
            except requests.exceptions.RequestException as e:
                logger.warning(f"请求失败 (尝试 {attempt + 1}/{self.retry_attempts}): {e}")
                
                if attempt < self.retry_attempts - 1:
                    time.sleep(self.retry_delay * (attempt + 1))  # 指数退避
                else:
                    logger.error(f"请求最终失败: {url}")
                    return None
        
        return None
    
    def search(
        self,
        query: str,
        start: int = 0,
        max_results: int = None,
        sort_by: str = "submittedDate",
        sort_order: str = "descending"
    ) -> Tuple[List[ArxivPaper], int]:
        """
        搜索arXiv论文
        
        Args:
            query: 搜索查询
            start: 起始位置
            max_results: 最大结果数
            sort_by: 排序字段 (relevance, lastUpdatedDate, submittedDate)
            sort_order: 排序顺序 (ascending, descending)
            
        Returns:
            (论文列表, 总结果数)
        """
        if max_results is None:
            max_results = self.max_results
        
        # 构建查询参数
        params = {
            "search_query": query,
            "start": start,
            "max_results": max_results,
            "sortBy": sort_by,
            "sortOrder": sort_order
        }
        
        url = f"{self.base_url}?{urlencode(params)}"
        logger.info(f"搜索arXiv: {query}")
        
        response_text = self._make_request(url)
        if not response_text:
            return [], 0
        
        try:
            return self._parse_feed(response_text)
        except ET.ParseError as e:
            logger.error(f"解析XML失败: {e}")
            return [], 0
    
    def search_by_category(
        self,
        category: str,
        date_from: Optional[datetime] = None,
        date_to: Optional[datetime] = None,
        max_results: int = None
    ) -> List[ArxivPaper]:
        """
        按分类搜索论文
        
        Args:
            category: arXiv分类 (如 math.AG)
            date_from: 起始日期
            date_to: 结束日期
            max_results: 最大结果数
            
        Returns:
            论文列表
        """
        # 构建查询
        query_parts = [f"cat:{category}"]
        
        if date_from:
            date_str = date_from.strftime("%Y%m%d")
            query_parts.append(f"submittedDate:[{date_str}0000 TO NOW]")
        
        query = " AND ".join(query_parts)
        
        papers = []
        start = 0
        batch_size = min(max_results or self.max_results, self.max_results)
        total = float('inf')
        
        while start < total and len(papers) < (max_results or self.max_results):
            batch_papers, total = self.search(query, start, batch_size)
            
            if not batch_papers:
                break
            
            # 过滤日期范围
            for paper in batch_papers:
                if date_to and paper.published > date_to:
                    continue
                papers.append(paper)
                
                if len(papers) >= (max_results or self.max_results):
                    break
            
            start += batch_size
            
            # 如果已经获取了足够的结果，停止
            if len(papers) >= (max_results or self.max_results):
                break
        
        return papers[:max_results] if max_results else papers
    
    def search_multiple_categories(
        self,
        categories: List[str],
        date_from: Optional[datetime] = None,
        date_to: Optional[datetime] = None,
        max_results_per_category: int = 50
    ) -> Dict[str, List[ArxivPaper]]:
        """
        搜索多个分类的论文
        
        Args:
            categories: 分类列表
            date_from: 起始日期
            date_to: 结束日期
            max_results_per_category: 每分类最大结果数
            
        Returns:
            {分类: 论文列表}
        """
        results = {}
        
        for category in categories:
            logger.info(f"搜索分类: {category}")
            papers = self.search_by_category(
                category,
                date_from,
                date_to,
                max_results_per_category
            )
            results[category] = papers
            logger.info(f"  找到 {len(papers)} 篇论文")
        
        return results
    
    def _parse_feed(self, xml_text: str) -> Tuple[List[ArxivPaper], int]:
        """
        解析arXiv Atom feed
        
        Args:
            xml_text: XML文本
            
        Returns:
            (论文列表, 总结果数)
        """
        root = ET.fromstring(xml_text.encode('utf-8'))
        
        # 获取总结果数
        total_results_elem = root.find(f".//{self.ATOM_NS}totalResults")
        total_results = int(total_results_elem.text) if total_results_elem is not None else 0
        
        papers = []
        
        for entry in root.findall(f".//{self.ATOM_NS}entry"):
            paper = self._parse_entry(entry)
            if paper:
                papers.append(paper)
        
        return papers, total_results
    
    def _parse_entry(self, entry: ET.Element) -> Optional[ArxivPaper]:
        """
        解析单个entry元素
        
        Args:
            entry: XML entry元素
            
        Returns:
            ArxivPaper实例或None
        """
        try:
            # arXiv ID
            id_elem = entry.find(f"{self.ATOM_NS}id")
            arxiv_id = id_elem.text.split('/')[-1] if id_elem is not None else ""
            
            # 标题
            title_elem = entry.find(f"{self.ATOM_NS}title")
            title = self._clean_text(title_elem.text) if title_elem is not None else ""
            
            # 作者
            authors = []
            for author in entry.findall(f"{self.ATOM_NS}author"):
                name_elem = author.find(f"{self.ATOM_NS}name")
                if name_elem is not None:
                    authors.append(name_elem.text)
            
            # 摘要
            summary_elem = entry.find(f"{self.ATOM_NS}summary")
            abstract = self._clean_text(summary_elem.text) if summary_elem is not None else ""
            
            # 分类
            categories = []
            primary_category = ""
            for cat in entry.findall(f"{self.ATOM_NS}category"):
                scheme = cat.get("scheme", "")
                if "arxiv.org" in scheme:
                    term = cat.get("term", "")
                    categories.append(term)
                    if not primary_category:
                        primary_category = term
            
            # 日期
            published_elem = entry.find(f"{self.ATOM_NS}published")
            published = datetime.fromisoformat(published_elem.text.replace('Z', '+00:00')) if published_elem is not None else None
            
            updated_elem = entry.find(f"{self.ATOM_NS}updated")
            updated = datetime.fromisoformat(updated_elem.text.replace('Z', '+00:00')) if updated_elem is not None else published
            
            # arXiv特定元数据
            doi = None
            journal_ref = None
            comment = None
            msc_classes = []
            
            for elem in entry.findall(f"{self.ARXIV_NS}doi"):
                doi = elem.text
            
            for elem in entry.findall(f"{self.ARXIV_NS}journal_ref"):
                journal_ref = elem.text
            
            for elem in entry.findall(f"{self.ARXIV_NS}comment"):
                comment = elem.text
            
            # MSC分类（通常在评论中）
            if comment and "MSC" in comment:
                # 尝试提取MSC分类
                import re
                msc_matches = re.findall(r'\d{2}[A-Z]\d{2}', comment)
                msc_classes = msc_matches
            
            # 链接
            pdf_url = None
            abs_url = None
            for link in entry.findall(f"{self.ATOM_NS}link"):
                href = link.get("href", "")
                rel = link.get("rel", "")
                title_attr = link.get("title", "")
                type_attr = link.get("type", "")
                
                if rel == "alternate" and not type_attr:
                    abs_url = href
                elif title_attr == "pdf" or type_attr == "application/pdf":
                    pdf_url = href
            
            # 构建URL（如果未从feed获取）
            if not abs_url and arxiv_id:
                abs_url = f"https://arxiv.org/abs/{arxiv_id}"
            if not pdf_url and arxiv_id:
                pdf_url = f"https://arxiv.org/pdf/{arxiv_id}.pdf"
            
            return ArxivPaper(
                arxiv_id=arxiv_id,
                title=title,
                authors=authors,
                abstract=abstract,
                categories=categories,
                primary_category=primary_category,
                published=published,
                updated=updated,
                doi=doi,
                journal_ref=journal_ref,
                comment=comment,
                pdf_url=pdf_url,
                abs_url=abs_url,
                msc_classes=msc_classes
            )
            
        except Exception as e:
            logger.error(f"解析entry失败: {e}")
            return None
    
    def _clean_text(self, text: str) -> str:
        """清理文本"""
        if not text:
            return ""
        # 移除多余空白
        return " ".join(text.split())
    
    def get_paper_by_id(self, arxiv_id: str) -> Optional[ArxivPaper]:
        """
        通过ID获取单篇论文
        
        Args:
            arxiv_id: arXiv ID
            
        Returns:
            ArxivPaper实例或None
        """
        query = f"id:{arxiv_id}"
        papers, _ = self.search(query, max_results=1)
        
        return papers[0] if papers else None


# 便捷函数
def create_client(config_path: str = "config.yaml") -> ArxivClient:
    """创建arXiv客户端实例"""
    return ArxivClient(config_path)


def fetch_recent_papers(
    categories: List[str],
    days: int = 7,
    config_path: str = "config.yaml"
) -> Dict[str, List[ArxivPaper]]:
    """
    获取最近N天的论文
    
    Args:
        categories: 分类列表
        days: 天数
        config_path: 配置文件路径
        
    Returns:
        {分类: 论文列表}
    """
    client = create_client(config_path)
    
    date_from = datetime.now() - timedelta(days=days)
    
    return client.search_multiple_categories(
        categories,
        date_from=date_from
    )


if __name__ == "__main__":
    # 测试代码
    client = ArxivClient()
    
    # 测试搜索
    papers, total = client.search("cat:math.AG", max_results=5)
    print(f"找到 {total} 篇论文，显示前 {len(papers)} 篇:")
    
    for paper in papers:
        print(f"\n标题: {paper.title}")
        print(f"ID: {paper.arxiv_id}")
        print(f"作者: {', '.join(paper.authors[:3])}")
        print(f"分类: {paper.primary_category}")
        print(f"发布日期: {paper.published}")
