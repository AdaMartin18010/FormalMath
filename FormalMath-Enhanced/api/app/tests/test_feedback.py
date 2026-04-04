"""
反馈系统测试
"""
import pytest
from datetime import datetime, timedelta
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker

# 假设的测试配置
# 实际项目中应从测试配置导入
from ..models.models import (
    Base, UserFeedback, FeedbackResponse, FeedbackProcessingLog,
    FeedbackType, FeedbackStatus, FeedbackPriority
)
from ..services.feedback_classifier import FeedbackClassifier
from ..services.feedback_service import FeedbackService


class TestFeedbackClassifier:
    """测试反馈分类器"""
    
    def setup_method(self):
        """每个测试方法前执行"""
        self.classifier = FeedbackClassifier()
    
    def test_classify_bug_report(self):
        """测试错误报告分类"""
        title = "搜索功能崩溃"
        content = "点击搜索按钮后页面直接崩溃了"
        
        feedback_type, confidence = self.classifier.classify(title, content)
        
        assert feedback_type == FeedbackType.BUG_REPORT
        assert confidence > 0.5
    
    def test_classify_feature_request(self):
        """测试功能请求分类"""
        title = "建议添加收藏功能"
        content = "希望能够收藏感兴趣的概念"
        
        feedback_type, confidence = self.classifier.classify(title, content)
        
        assert feedback_type == FeedbackType.FEATURE_REQUEST
    
    def test_determine_priority(self):
        """测试优先级判定"""
        title = "系统崩溃无法使用"
        content = "整个网站都打不开了，非常紧急！"
        
        priority = self.classifier.determine_priority(
            title, content, FeedbackType.BUG_REPORT
        )
        
        assert priority in ['critical', 'high', 'medium', 'low']
    
    def test_extract_keywords(self):
        """测试关键词提取"""
        title = "搜索功能无法使用"
        content = "搜索框输入关键词后没有任何结果"
        
        keywords = self.classifier.extract_keywords(title, content)
        
        assert isinstance(keywords, list)
        assert len(keywords) > 0
    
    def test_analyze_sentiment(self):
        """测试情感分析"""
        title = "界面设计很棒"
        content = "新的UI设计非常清晰，使用起来很方便！"
        
        sentiment = self.classifier.analyze_sentiment(title, content)
        
        assert 'sentiment' in sentiment
        assert 'positive_score' in sentiment
        assert 'negative_score' in sentiment


class TestFeedbackService:
    """测试反馈服务"""
    
    @pytest.fixture(scope="function")
    def db_session(self):
        """创建测试数据库会话"""
        # 使用内存数据库进行测试
        engine = create_engine('sqlite:///:memory:')
        Base.metadata.create_all(engine)
        
        Session = sessionmaker(bind=engine)
        session = Session()
        
        yield session
        
        session.close()
    
    def test_create_feedback(self, db_session):
        """测试创建反馈"""
        service = FeedbackService(db_session)
        
        feedback = service.create_feedback(
            title="测试反馈标题",
            content="这是一个测试反馈的内容",
            feedback_type=FeedbackType.GENERAL,
            user_id=1
        )
        
        assert feedback.id is not None
        assert feedback.title == "测试反馈标题"
        assert feedback.status == FeedbackStatus.PENDING
    
    def test_create_feedback_auto_classify(self, db_session):
        """测试自动分类创建反馈"""
        service = FeedbackService(db_session)
        
        feedback = service.create_feedback(
            title="搜索功能崩溃",
            content="点击搜索按钮后页面直接崩溃了"
        )
        
        assert feedback.id is not None
        assert feedback.auto_classified_type is not None
        assert feedback.classification_confidence > 0
    
    def test_get_feedback(self, db_session):
        """测试获取反馈"""
        service = FeedbackService(db_session)
        
        created = service.create_feedback(
            title="测试反馈",
            content="测试内容"
        )
        
        fetched = service.get_feedback(created.id)
        
        assert fetched is not None
        assert fetched.id == created.id
        assert fetched.title == created.title
    
    def test_update_feedback(self, db_session):
        """测试更新反馈"""
        service = FeedbackService(db_session)
        
        feedback = service.create_feedback(
            title="测试反馈",
            content="测试内容"
        )
        
        updated = service.update_feedback(
            feedback_id=feedback.id,
            status=FeedbackStatus.IN_PROGRESS,
            priority=FeedbackPriority.HIGH
        )
        
        assert updated.status == FeedbackStatus.IN_PROGRESS
        assert updated.priority == FeedbackPriority.HIGH
    
    def test_add_response(self, db_session):
        """测试添加回复"""
        service = FeedbackService(db_session)
        
        feedback = service.create_feedback(
            title="测试反馈",
            content="测试内容"
        )
        
        response = service.add_response(
            feedback_id=feedback.id,
            content="感谢您的反馈",
            responder_id=1,
            is_internal=False
        )
        
        assert response is not None
        assert response.content == "感谢您的反馈"
        assert response.is_internal == False
    
    def test_list_feedbacks(self, db_session):
        """测试查询反馈列表"""
        service = FeedbackService(db_session)
        
        # 创建多个反馈
        for i in range(5):
            service.create_feedback(
                title=f"测试反馈{i}",
                content=f"测试内容{i}",
                feedback_type=FeedbackType.BUG_REPORT if i % 2 == 0 else FeedbackType.FEATURE_REQUEST
            )
        
        feedbacks, total = service.list_feedbacks(
            feedback_type=FeedbackType.BUG_REPORT
        )
        
        assert total >= 3  # 至少3个BUG_REPORT
        for f in feedbacks:
            assert f.feedback_type == FeedbackType.BUG_REPORT
    
    def test_delete_feedback(self, db_session):
        """测试删除反馈"""
        service = FeedbackService(db_session)
        
        feedback = service.create_feedback(
            title="待删除反馈",
            content="将被删除"
        )
        
        success = service.delete_feedback(feedback.id)
        assert success == True
        
        deleted = service.get_feedback(feedback.id)
        assert deleted is None
    
    def test_get_statistics(self, db_session):
        """测试获取统计"""
        service = FeedbackService(db_session)
        
        # 创建一些反馈
        for i in range(3):
            service.create_feedback(
                title=f"反馈{i}",
                content=f"内容{i}"
            )
        
        stats = service.get_statistics()
        
        assert 'total_feedbacks' in stats
        assert stats['total_feedbacks'] >= 3
        assert 'by_type' in stats
        assert 'by_status' in stats
    
    def test_get_dashboard_summary(self, db_session):
        """测试仪表板摘要"""
        service = FeedbackService(db_session)
        
        # 创建反馈
        service.create_feedback(title="今日反馈", content="内容")
        
        summary = service.get_dashboard_summary()
        
        assert 'today_count' in summary
        assert 'pending_count' in summary
        assert 'recent_feedbacks' in summary


class TestFeedbackAPI:
    """测试反馈API端点（集成测试）"""
    
    # 这里使用pytest和fastapi的TestClient进行集成测试
    # 实际项目中需要配置测试客户端
    
    def test_create_feedback_endpoint(self):
        """测试创建反馈API"""
        # client = TestClient(app)
        # response = client.post(
        #     "/api/v1/feedback/feedbacks",
        #     json={
        #         "title": "测试",
        #         "content": "测试内容"
        #     }
        # )
        # assert response.status_code == 200
        # assert response.json()["success"] == True
        pass
    
    def test_get_feedbacks_endpoint(self):
        """测试获取反馈列表API"""
        pass
    
    def test_classify_endpoint(self):
        """测试分类API"""
        pass


class TestFeedbackWorkflow:
    """测试反馈完整工作流"""
    
    @pytest.fixture(scope="function")
    def db_session(self):
        """创建测试数据库会话"""
        engine = create_engine('sqlite:///:memory:')
        Base.metadata.create_all(engine)
        
        Session = sessionmaker(bind=engine)
        session = Session()
        
        yield session
        
        session.close()
    
    def test_complete_workflow(self, db_session):
        """测试完整反馈流程"""
        service = FeedbackService(db_session)
        
        # 1. 用户提交反馈
        feedback = service.create_feedback(
            title="搜索功能无法使用",
            content="点击搜索后页面一直加载中"
        )
        assert feedback.status == FeedbackStatus.CLASSIFIED
        
        # 2. 管理员审核并开始处理
        service.update_feedback(
            feedback_id=feedback.id,
            status=FeedbackStatus.IN_PROGRESS,
            assigned_to=1
        )
        
        # 3. 添加回复
        service.add_response(
            feedback_id=feedback.id,
            content="正在修复中",
            responder_id=1
        )
        
        # 4. 标记解决
        service.update_feedback(
            feedback_id=feedback.id,
            status=FeedbackStatus.RESOLVED,
            resolution_notes="已修复搜索超时问题"
        )
        
        # 验证最终状态
        final = service.get_feedback(feedback.id)
        assert final.status == FeedbackStatus.RESOLVED
        assert final.resolved_at is not None
        assert len(final.responses) == 1
        assert len(final.processing_logs) >= 3  # 创建、更新、回复


# 运行测试的命令
# pytest tests/test_feedback.py -v
