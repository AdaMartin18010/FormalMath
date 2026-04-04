"""
反馈系统初始化脚本
用于创建反馈系统所需的表和初始数据
"""
import sys
import os

# 添加项目路径
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from datetime import datetime, timedelta
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker

from core.database import db_manager, Base
from models.models import (
    FeedbackType, FeedbackStatus, FeedbackPriority,
    UserFeedback, FeedbackResponse, FeedbackProcessingLog, FeedbackAnalytics
)
from services.feedback_classifier import get_feedback_classifier


def init_feedback_tables():
    """初始化反馈系统表"""
    print("=" * 60)
    print("用户反馈系统初始化")
    print("=" * 60)
    
    # 初始化数据库连接
    print("\n[1/4] 初始化数据库连接...")
    db_manager.init_engine()
    
    # 创建表
    print("\n[2/4] 创建反馈系统表...")
    db_manager.create_tables()
    print("  ✓ 表创建完成")
    
    # 创建索引
    print("\n[3/4] 创建数据库索引...")
    db_manager.create_indexes()
    print("  ✓ 索引创建完成")
    
    # 创建示例数据（可选）
    print("\n[4/4] 创建示例数据...")
    create_sample_data()
    print("  ✓ 示例数据创建完成")
    
    print("\n" + "=" * 60)
    print("反馈系统初始化完成！")
    print("=" * 60)
    
    return True


def create_sample_data():
    """创建示例反馈数据"""
    with db_manager.session_scope() as db:
        # 检查是否已有数据
        existing = db.query(UserFeedback).first()
        if existing:
            print("  - 已存在反馈数据，跳过示例数据创建")
            return
        
        classifier = get_feedback_classifier()
        
        # 示例反馈数据
        sample_feedbacks = [
            {
                "title": "搜索功能无法使用",
                "content": "在搜索框输入关键词后，页面一直显示加载中，没有任何结果返回。",
                "type": FeedbackType.BUG_REPORT
            },
            {
                "title": "建议增加公式导出功能",
                "content": "希望能够将搜索结果中的数学公式导出为LaTeX或MathML格式，方便在论文中使用。",
                "type": FeedbackType.FEATURE_REQUEST
            },
            {
                "title": "群论章节有错误",
                "content": "拉格朗日定理的描述中，子群的定义不够准确，建议修正。",
                "type": FeedbackType.CONTENT_ERROR
            },
            {
                "title": "页面加载速度太慢",
                "content": "知识图谱页面加载需要等待很长时间，体验不好。",
                "type": FeedbackType.PERFORMANCE
            },
            {
                "title": "界面设计很棒",
                "content": "新的UI设计非常清晰，使用起来很方便，特别是夜间模式！",
                "type": FeedbackType.COMPLIMENT
            }
        ]
        
        for i, data in enumerate(sample_feedbacks):
            # 自动分类
            auto_type, confidence = classifier.classify(data["title"], data["content"])
            priority = classifier.determine_priority(data["title"], data["content"], auto_type)
            
            # 创建反馈
            feedback = UserFeedback(
                user_id=1 if i % 2 == 0 else None,  # 部分匿名
                title=data["title"],
                content=data["content"],
                feedback_type=data["type"],
                auto_classified_type=auto_type,
                classification_confidence=confidence,
                status=FeedbackStatus.CLASSIFIED,
                priority=FeedbackPriority.HIGH if priority == 'high' else 
                        FeedbackPriority.MEDIUM if priority == 'medium' else FeedbackPriority.LOW,
                related_page="/search" if i == 0 else "/concepts" if i == 2 else "/dashboard",
                browser_info={
                    "browser": "Chrome",
                    "version": "120.0"
                },
                device_info={
                    "type": "desktop"
                },
                satisfaction_rating=3 if i == 0 else 4 if i == 4 else None,
                created_at=datetime.utcnow() - timedelta(days=i, hours=i*2)
            )
            db.add(feedback)
            db.flush()  # 获取ID
            
            # 添加处理日志
            log = FeedbackProcessingLog(
                feedback_id=feedback.id,
                action='created',
                new_status=FeedbackStatus.CLASSIFIED,
                notes=f'自动分类: {auto_type.value}, 置信度: {confidence:.2f}'
            )
            db.add(log)
            
            # 部分添加回复
            if i % 2 == 0:
                response = FeedbackResponse(
                    feedback_id=feedback.id,
                    responder_id=1,
                    content=f"感谢您的反馈，我们已经收到并正在处理中。",
                    is_internal=False
                )
                db.add(response)
        
        db.commit()
        print(f"  - 创建了 {len(sample_feedbacks)} 条示例反馈")


def test_classifier():
    """测试分类器"""
    print("\n" + "=" * 60)
    print("测试反馈分类器")
    print("=" * 60)
    
    classifier = get_feedback_classifier()
    
    test_cases = [
        {
            "title": "搜索功能崩溃",
            "content": "点击搜索按钮后页面直接崩溃了，请尽快修复！"
        },
        {
            "title": "建议添加收藏功能",
            "content": "希望能够收藏感兴趣的概念，方便以后查看。"
        },
        {
            "title": "页面加载太慢",
            "content": "每次打开知识图谱都需要等很久，希望能优化性能。"
        }
    ]
    
    for case in test_cases:
        result = classifier.get_classification_details(case["title"], case["content"])
        print(f"\n标题: {case['title']}")
        print(f"  分类: {result['feedback_type']} (置信度: {result['confidence']})")
        print(f"  优先级: {result['priority']}")
        print(f"  关键词: {', '.join(result['keywords'][:5])}")
        print(f"  情感: {result['sentiment']['sentiment']}")


def show_stats():
    """显示反馈系统统计"""
    print("\n" + "=" * 60)
    print("反馈系统统计")
    print("=" * 60)
    
    with db_manager.session_scope() as db:
        from services.feedback_service import FeedbackService
        service = FeedbackService(db)
        
        stats = service.get_statistics()
        
        print(f"\n总反馈数: {stats['total_feedbacks']}")
        print(f"\n按类型分布:")
        for type_name, count in stats['by_type'].items():
            print(f"  - {type_name}: {count}")
        
        print(f"\n按状态分布:")
        for status_name, count in stats['by_status'].items():
            print(f"  - {status_name}: {count}")
        
        print(f"\n平均解决时间: {stats['avg_resolution_hours']:.2f} 小时")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='反馈系统初始化工具')
    parser.add_argument('--init', action='store_true', help='初始化表和数据')
    parser.add_argument('--test', action='store_true', help='测试分类器')
    parser.add_argument('--stats', action='store_true', help='显示统计')
    parser.add_argument('--all', action='store_true', help='执行所有操作')
    
    args = parser.parse_args()
    
    if args.all or args.init:
        init_feedback_tables()
    
    if args.all or args.test:
        test_classifier()
    
    if args.all or args.stats:
        show_stats()
    
    if not any([args.init, args.test, args.stats, args.all]):
        parser.print_help()
        print("\n示例:")
        print("  python init_feedback_system.py --init    # 初始化系统")
        print("  python init_feedback_system.py --test    # 测试分类器")
        print("  python init_feedback_system.py --all     # 执行所有操作")
