"""
FormalMath arXiv前沿跟踪系统 - 主程序

命令行入口，支持以下功能：
- 运行完整跟踪流程
- 生成周度报告
- 测试单个模块
- 配置管理
"""

import argparse
import logging
import sys
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional

from arxiv_client import ArxivClient, fetch_recent_papers
from paper_filter import PaperFilter
from relevance_scorer import RelevanceScorer, categorize_by_relevance
from update_suggester import UpdateSuggester
from report_generator import ReportGenerator

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)


def load_config(config_path: str = "config.yaml"):
    """加载配置文件"""
    import yaml
    with open(config_path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f)


def run_full_tracking(
    config_path: str = "config.yaml",
    days: int = 7,
    generate_report: bool = True,
    report_format: str = "markdown"
) -> dict:
    """
    运行完整的跟踪流程
    
    Args:
        config_path: 配置文件路径
        days: 跟踪天数
        generate_report: 是否生成报告
        report_format: 报告格式
        
    Returns:
        执行结果统计
    """
    logger.info("=" * 60)
    logger.info("FormalMath arXiv前沿跟踪系统启动")
    logger.info("=" * 60)
    
    config = load_config(config_path)
    
    # 获取跟踪的分类
    categories = [cat['id'] for cat in config.get('tracking_categories', [])]
    logger.info(f"跟踪 {len(categories)} 个数学领域")
    
    # 1. 获取论文
    logger.info(f"\n[1/5] 获取最近 {days} 天的论文...")
    client = ArxivClient(config_path)
    
    papers_by_category = client.search_multiple_categories(
        categories,
        date_from=datetime.now() - timedelta(days=days),
        max_results_per_category=50
    )
    
    total_papers = sum(len(papers) for papers in papers_by_category.values())
    logger.info(f"共获取 {total_papers} 篇论文")
    
    # 2. 筛选论文
    logger.info("\n[2/5] 筛选论文...")
    filter_ = PaperFilter(config_path)
    
    filtered_by_category = {}
    for category, papers in papers_by_category.items():
        criteria = filter_.create_category_criteria(category)
        results = filter_.filter_papers(papers, criteria)
        passed = [r for r in results if r.passed]
        filtered_by_category[category] = [r.paper for r in passed]
        logger.info(f"  {category}: {len(papers)} -> {len(passed)} 篇")
    
    total_filtered = sum(len(papers) for papers in filtered_by_category.values())
    logger.info(f"筛选后: {total_filtered} 篇")
    
    # 3. 相关性评分
    logger.info("\n[3/5] 计算相关性分数...")
    scorer = RelevanceScorer(config_path)
    
    scored_by_category = {}
    for category, papers in filtered_by_category.items():
        scored = [(p, scorer.score_paper(p, category)) for p in papers]
        scored_by_category[category] = scored
        avg_score = sum(s.overall_score for _, s in scored) / len(scored) if scored else 0
        logger.info(f"  {category}: {len(scored)} 篇, 平均分数: {avg_score:.2f}")
    
    # 4. 生成更新建议
    logger.info("\n[4/5] 生成知识库更新建议...")
    suggester = UpdateSuggester(config_path)
    
    all_scored = []
    for scored in scored_by_category.values():
        all_scored.extend(scored)
    
    suggestions = suggester.generate_suggestions(all_scored)
    logger.info(f"生成 {len(suggestions)} 条更新建议")
    
    # 按类型统计
    by_type = {}
    for s in suggestions:
        by_type[s.type] = by_type.get(s.type, 0) + 1
    for type_name, count in by_type.items():
        logger.info(f"  {type_name}: {count} 条")
    
    # 5. 生成报告
    report_path = None
    suggestions_path = None
    
    if generate_report:
        logger.info("\n[5/5] 生成报告...")
        generator = ReportGenerator(config_path)
        
        report_path = generator.generate_weekly_report(
            scored_by_category,
            output_format=report_format
        )
        logger.info(f"  周度报告: {report_path}")
        
        if suggestions:
            suggestions_path = generator.generate_suggestions_report(
                suggestions,
                output_format="markdown"
            )
            logger.info(f"  建议报告: {suggestions_path}")
    
    # 统计结果
    result = {
        'total_papers_fetched': total_papers,
        'total_papers_filtered': total_filtered,
        'categories_processed': len(categories),
        'suggestions_generated': len(suggestions),
        'report_path': report_path,
        'suggestions_path': suggestions_path
    }
    
    # 各分类统计
    for category, scored in scored_by_category.items():
        high = sum(1 for _, s in scored if s.overall_score >= 0.7)
        medium = sum(1 for _, s in scored if 0.4 <= s.overall_score < 0.7)
        result[f'{category}_high'] = high
        result[f'{category}_medium'] = medium
    
    logger.info("\n" + "=" * 60)
    logger.info("跟踪完成!")
    logger.info(f"获取论文: {total_papers}")
    logger.info(f"通过筛选: {total_filtered}")
    logger.info(f"生成建议: {len(suggestions)}")
    if report_path:
        logger.info(f"报告位置: {report_path}")
    logger.info("=" * 60)
    
    return result


def run_test_mode(config_path: str = "config.yaml"):
    """运行测试模式"""
    logger.info("运行测试模式...")
    
    # 测试单个分类
    test_category = "math.CT"  # 范畴论
    logger.info(f"测试分类: {test_category}")
    
    # 获取论文
    client = ArxivClient(config_path)
    papers = client.search_by_category(test_category, max_results=5)
    logger.info(f"获取 {len(papers)} 篇论文")
    
    if papers:
        # 测试筛选
        filter_ = PaperFilter(config_path)
        criteria = filter_.create_category_criteria(test_category)
        results = filter_.filter_papers(papers, criteria)
        passed = [r for r in results if r.passed]
        logger.info(f"筛选通过: {len(passed)}/{len(papers)}")
        
        # 测试评分
        scorer = RelevanceScorer(config_path)
        for paper in [r.paper for r in passed[:3]]:
            score = scorer.score_paper(paper, test_category)
            logger.info(f"  '{paper.title[:40]}...' - 分数: {score.overall_score:.2f}")
    
    logger.info("测试完成!")


def run_single_category(
    category: str,
    days: int = 7,
    config_path: str = "config.yaml"
):
    """运行单个分类跟踪"""
    logger.info(f"跟踪分类: {category}")
    
    # 验证分类
    config = load_config(config_path)
    valid_categories = [cat['id'] for cat in config.get('tracking_categories', [])]
    
    if category not in valid_categories:
        logger.error(f"无效分类: {category}")
        logger.info(f"有效分类: {', '.join(valid_categories)}")
        return
    
    # 获取论文
    client = ArxivClient(config_path)
    papers = client.search_by_category(
        category,
        date_from=datetime.now() - timedelta(days=days),
        max_results=50
    )
    
    logger.info(f"获取 {len(papers)} 篇论文")
    
    # 筛选和评分
    filter_ = PaperFilter(config_path)
    criteria = filter_.create_category_criteria(category)
    results = filter_.filter_papers(papers, criteria)
    passed = [r.paper for r in results if r.passed]
    
    logger.info(f"筛选通过: {len(passed)} 篇")
    
    # 评分
    scorer = RelevanceScorer(config_path)
    scored = [(p, scorer.score_paper(p, category)) for p in passed]
    scored.sort(key=lambda x: x[1].overall_score, reverse=True)
    
    # 输出结果
    print("\n" + "=" * 60)
    print(f"分类 {category} 的Top论文:")
    print("=" * 60)
    
    for i, (paper, score) in enumerate(scored[:10], 1):
        print(f"\n{i}. {paper.title}")
        print(f"   作者: {', '.join(paper.authors[:3])}")
        print(f"   分数: {score.overall_score:.2f} (关键词: {score.keyword_score:.2f}, 概念: {score.concept_score:.2f})")
        print(f"   链接: {paper.abs_url}")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="FormalMath arXiv前沿跟踪系统",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                          # 运行完整跟踪流程
  %(prog)s --test                   # 运行测试模式
  %(prog)s --category math.CT       # 跟踪单个分类
  %(prog)s --days 14 --format json  # 跟踪14天，输出JSON格式
        """
    )
    
    parser.add_argument(
        '-c', '--config',
        default='config.yaml',
        help='配置文件路径 (默认: config.yaml)'
    )
    
    parser.add_argument(
        '-d', '--days',
        type=int,
        default=7,
        help='跟踪天数 (默认: 7)'
    )
    
    parser.add_argument(
        '--category',
        help='只跟踪指定分类 (如: math.CT, math.AG)'
    )
    
    parser.add_argument(
        '-f', '--format',
        choices=['markdown', 'json', 'html'],
        default='markdown',
        help='报告输出格式 (默认: markdown)'
    )
    
    parser.add_argument(
        '--no-report',
        action='store_true',
        help='不生成报告'
    )
    
    parser.add_argument(
        '--test',
        action='store_true',
        help='运行测试模式'
    )
    
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='详细输出'
    )
    
    args = parser.parse_args()
    
    # 设置日志级别
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    try:
        if args.test:
            run_test_mode(args.config)
        elif args.category:
            run_single_category(args.category, args.days, args.config)
        else:
            result = run_full_tracking(
                args.config,
                args.days,
                not args.no_report,
                args.format
            )
            
            # 输出摘要
            print("\n" + "=" * 60)
            print("执行摘要")
            print("=" * 60)
            print(f"获取论文总数: {result['total_papers_fetched']}")
            print(f"通过筛选: {result['total_papers_filtered']}")
            print(f"处理领域数: {result['categories_processed']}")
            print(f"生成建议: {result['suggestions_generated']}")
            if result.get('report_path'):
                print(f"报告位置: {result['report_path']}")
            print("=" * 60)
        
        return 0
        
    except KeyboardInterrupt:
        logger.info("用户中断")
        return 130
    except Exception as e:
        logger.error(f"执行错误: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
