"""
诊断服务
"""

from typing import Dict, List, Optional, Any
from datetime import datetime

from app.models.diagnosis import DiagnosisSession, DiagnosisResponse, DiagnosisStatus
from app.models.question import Question
from app.models.knowledge_graph import KnowledgeGraph
from app.diagnosis.hcd_engine import HCDEngine, HCDResult
from app.diagnosis.test_generator import TestGenerator
from app.diagnosis.report_generator import ReportGenerator
from app.database.in_memory_db import InMemoryDatabase


class DiagnosisService:
    """诊断服务"""
    
    def __init__(self):
        self.db = InMemoryDatabase()
        self.knowledge_graph = self._init_knowledge_graph()
        self.test_generator = TestGenerator(
            self.knowledge_graph,
            self.db.get_all_questions()
        )
        self.hcd_engine = HCDEngine(self.knowledge_graph)
        self.report_generator = ReportGenerator(self.knowledge_graph)
    
    def _init_knowledge_graph(self) -> KnowledgeGraph:
        """初始化知识图谱"""
        return self.db.get_knowledge_graph()
    
    def start_diagnosis(
        self,
        user_id: str,
        question_count: int = 20,
        target_levels: Optional[List[int]] = None
    ) -> DiagnosisSession:
        """开始诊断"""
        # 生成诊断测试
        session = self.test_generator.generate_diagnosis_test(
            user_id=user_id,
            question_count=question_count,
            target_levels=target_levels
        )
        
        session.status = DiagnosisStatus.IN_PROGRESS
        session.started_at = datetime.now()
        
        # 保存会话
        self.db.save_session(session)
        
        return session
    
    def get_current_question(self, session_id: str) -> Optional[dict]:
        """获取当前题目"""
        session = self.db.get_session(session_id)
        if not session or session.status != DiagnosisStatus.IN_PROGRESS:
            return None
        
        question = self.test_generator.get_next_question(session, adaptive=False)
        if not question:
            return None
        
        # 返回题目（隐藏正确答案）
        return {
            "id": question.id,
            "type": question.type.value,
            "content": question.content,
            "options": question.options,
            "knowledge_level": question.knowledge_level,
            "estimated_time": question.estimated_time
        }
    
    def submit_answer(
        self,
        session_id: str,
        question_id: str,
        answer: any,
        time_spent: int,
        confidence: Optional[float] = None
    ) -> Dict[str, Any]:
        """提交答案"""
        session = self.db.get_session(session_id)
        if not session:
            return {"success": False, "message": "诊断会话不存在"}
        
        if session.status != DiagnosisStatus.IN_PROGRESS:
            return {"success": False, "message": "诊断会话已结束"}
        
        # 获取题目
        question = self.test_generator.get_question_by_id(question_id)
        if not question:
            return {"success": False, "message": "题目不存在"}
        
        # 评分
        is_correct, score = self.test_generator.score_response(question, answer)
        
        # 记录响应
        response = DiagnosisResponse(
            question_id=question_id,
            answer=answer,
            is_correct=is_correct,
            time_spent=time_spent,
            confidence=confidence
        )
        session.responses.append(response)
        session.current_question_index += 1
        
        # 保存更新
        self.db.save_session(session)
        
        # 计算进度
        progress = {
            "current": session.current_question_index,
            "total": len(session.question_ids),
            "percentage": round(session.current_question_index / len(session.question_ids) * 100, 1)
        }
        
        result = {
            "success": True,
            "is_correct": is_correct,
            "score": score,
            "progress": progress
        }
        
        # 检查是否完成
        if session.current_question_index >= len(session.question_ids):
            # 完成诊断，生成报告
            report_result = self._complete_and_generate_report(session)
            result["completed"] = True
            result["report_id"] = report_result.get("report_id")
        else:
            # 获取下一题
            next_question = self.test_generator.get_next_question(session)
            if next_question:
                result["next_question"] = {
                    "id": next_question.id,
                    "type": next_question.type.value,
                    "content": next_question.content,
                    "options": next_question.options,
                    "knowledge_level": next_question.knowledge_level,
                    "estimated_time": next_question.estimated_time
                }
        
        return result
    
    def _complete_and_generate_report(self, session: DiagnosisSession) -> Dict[str, Any]:
        """完成诊断并生成报告"""
        session.status = DiagnosisStatus.COMPLETED
        session.completed_at = datetime.now()
        self.db.save_session(session)
        
        # 执行HCD诊断
        questions = {
            q.id: q for q in self.test_generator.get_questions_for_session(session)
        }
        
        hcd_result = self.hcd_engine.diagnose(
            responses=session.responses,
            questions=questions
        )
        
        # 生成报告
        report = self.report_generator.generate_report(
            session=session,
            hcd_result=hcd_result,
            questions=questions
        )
        
        # 保存报告
        self.db.save_report(report)
        
        # 更新用户知识状态
        self._update_user_knowledge_state(session.user_id, hcd_result)
        
        return {
            "report_id": report.id,
            "summary": {
                "ability_level": hcd_result.ability_level,
                "total_questions": len(session.responses),
                "correct_count": sum(1 for r in session.responses if r.is_correct)
            }
        }
    
    def _update_user_knowledge_state(self, user_id: str, hcd_result: HCDResult):
        """更新用户知识状态"""
        user = self.db.get_user(user_id)
        if user:
            user.knowledge_state.update(hcd_result.knowledge_state)
            user.ability_level.update(hcd_result.ability_level)
            self.db.save_user(user)
    
    def complete_diagnosis(self, session_id: str) -> Dict[str, Any]:
        """手动完成诊断"""
        session = self.db.get_session(session_id)
        if not session:
            return {"success": False, "message": "诊断会话不存在"}
        
        if session.status == DiagnosisStatus.COMPLETED:
            # 已经生成过报告
            report = self.db.get_report_by_diagnosis_id(session_id)
            if report:
                return {
                    "success": True,
                    "report_id": report.id,
                    "summary": {
                        "ability_level": report.ability_level,
                        "total_questions": report.total_questions,
                        "correct_count": report.correct_count
                    }
                }
        
        # 生成报告
        return self._complete_and_generate_report(session)
    
    def get_session(self, session_id: str) -> Optional[DiagnosisSession]:
        """获取诊断会话"""
        return self.db.get_session(session_id)
