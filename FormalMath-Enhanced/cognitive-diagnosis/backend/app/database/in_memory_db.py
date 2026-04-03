"""
内存数据库（用于演示）
生产环境应替换为PostgreSQL等持久化数据库
"""

from typing import Dict, List, Optional
from datetime import datetime

from app.models.user import User, UserProfile
from app.models.question import Question, QuestionType, KnowledgeTag
from app.models.diagnosis import DiagnosisSession, DiagnosisReport
from app.models.knowledge_graph import (
    KnowledgeGraph, KnowledgeNode, KnowledgeEdge, 
    KnowledgeLevel, ConstraintType
)


class InMemoryDatabase:
    """内存数据库（单例模式）"""
    
    _instance = None
    _initialized = False
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance
    
    def __init__(self):
        if InMemoryDatabase._initialized:
            return
        
        InMemoryDatabase._initialized = True
        
        # 数据存储
        self.users: Dict[str, User] = {}
        self.questions: Dict[str, Question] = {}
        self.sessions: Dict[str, DiagnosisSession] = {}
        self.reports: Dict[str, DiagnosisReport] = {}
        self.knowledge_tags: Dict[str, KnowledgeTag] = {}
        self.knowledge_graph: Optional[KnowledgeGraph] = None
        
        # 初始化示例数据
        self._init_sample_data()
    
    def _init_sample_data(self):
        """初始化示例数据"""
        self._init_knowledge_graph_data()
        self._init_questions_data()
        self._init_sample_user()
    
    def _init_knowledge_graph_data(self):
        """初始化知识图谱数据"""
        # 创建知识节点
        nodes = [
            # L0: 基础层
            KnowledgeNode(id="set_basic", name="集合的基本概念", level=KnowledgeLevel.L0, 
                         description="集合的直观理解", content_length=1500, category="集合论"),
            KnowledgeNode(id="function_basic", name="函数的基本概念", level=KnowledgeLevel.L0,
                         description="函数的直观理解", content_length=1800, category="函数论"),
            KnowledgeNode(id="number_basic", name="数的基本概念", level=KnowledgeLevel.L0,
                         description="自然数、整数的直观理解", content_length=1200, category="数论"),
            KnowledgeNode(id="logic_basic", name="逻辑的基本概念", level=KnowledgeLevel.L0,
                         description="命题、逻辑的直观理解", content_length=1400, category="逻辑"),
            
            # L1: 中级层
            KnowledgeNode(id="set_axioms", name="集合公理", level=KnowledgeLevel.L1,
                         description="ZFC公理系统", content_length=3500, category="集合论"),
            KnowledgeNode(id="function_formal", name="函数的严格定义", level=KnowledgeLevel.L1,
                         description="函数的形式化定义", content_length=3200, category="函数论"),
            KnowledgeNode(id="real_numbers", name="实数理论", level=KnowledgeLevel.L1,
                         description="Dedekind分割构造实数", content_length=4000, category="数论"),
            KnowledgeNode(id="propositional_logic", name="命题逻辑", level=KnowledgeLevel.L1,
                         description="命题逻辑的形式系统", content_length=3000, category="逻辑"),
            
            # L2: 高级层
            KnowledgeNode(id="cardinal_numbers", name="基数理论", level=KnowledgeLevel.L2,
                         description="无限基数、连续统假设", content_length=5500, category="集合论"),
            KnowledgeNode(id="continuum_hypothesis", name="连续统假设", level=KnowledgeLevel.L2,
                         description="CH及其独立性", content_length=5800, category="集合论"),
            KnowledgeNode(id="axiom_of_choice", name="选择公理", level=KnowledgeLevel.L2,
                         description="AC及其等价形式", content_length=5200, category="集合论"),
            
            # L3: 研究层
            KnowledgeNode(id="large_cardinals", name="大基数公理", level=KnowledgeLevel.L3,
                         description="可测基数、超紧基数", content_length=8000, category="集合论"),
            KnowledgeNode(id="forcing", name="力迫法", level=KnowledgeLevel.L3,
                         description="Cohen的力迫技术", content_length=9000, category="集合论"),
        ]
        
        # 创建边（先修关系）
        edges = [
            KnowledgeEdge(id="e1", source_id="set_basic", target_id="set_axioms",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.9),
            KnowledgeEdge(id="e2", source_id="set_axioms", target_id="cardinal_numbers",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.85),
            KnowledgeEdge(id="e3", source_id="cardinal_numbers", target_id="continuum_hypothesis",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.9),
            KnowledgeEdge(id="e4", source_id="set_axioms", target_id="axiom_of_choice",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.8),
            KnowledgeEdge(id="e5", source_id="continuum_hypothesis", target_id="forcing",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.9),
            KnowledgeEdge(id="e6", source_id="axiom_of_choice", target_id="large_cardinals",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.85),
            KnowledgeEdge(id="e7", source_id="number_basic", target_id="real_numbers",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.9),
            KnowledgeEdge(id="e8", source_id="logic_basic", target_id="propositional_logic",
                         constraint_type=ConstraintType.PREREQUISITE, strength=0.9),
        ]
        
        # 构建层次结构
        level_structure = {0: [], 1: [], 2: [], 3: []}
        for node in nodes:
            level_structure[node.level].append(node.id)
        
        # 创建知识图谱
        self.knowledge_graph = KnowledgeGraph(
            id="math_foundation",
            name="数学基础概念图谱",
            description="FormalMath项目数学基础概念层次结构",
            nodes={n.id: n for n in nodes},
            edges={e.id: e for e in edges},
            level_structure=level_structure
        )
        
        # 保存知识点标签
        for node in nodes:
            tag = KnowledgeTag(
                id=node.id,
                name=node.name,
                level=node.level
            )
            self.knowledge_tags[node.id] = tag
    
    def _init_questions_data(self):
        """初始化题目数据"""
        questions = [
            # L0 题目
            Question(
                id="q001",
                type=QuestionType.SINGLE_CHOICE,
                content="集合的基本性质包括哪些？",
                options=[
                    {"id": "A", "text": "确定性"},
                    {"id": "B", "text": "互异性"},
                    {"id": "C", "text": "无序性"},
                    {"id": "D", "text": "以上都是"}
                ],
                correct_answer="D",
                explanation="集合具有确定性、互异性和无序性三个基本性质",
                knowledge_tags=["set_basic"],
                knowledge_level=0,
                difficulty=-0.5,
                discrimination=1.0,
                q_matrix={"set_basic": 1.0}
            ),
            Question(
                id="q002",
                type=QuestionType.TRUE_FALSE,
                content="空集是任何集合的子集。",
                correct_answer=True,
                explanation="根据子集定义，空集是所有集合的子集",
                knowledge_tags=["set_basic"],
                knowledge_level=0,
                difficulty=-0.3,
                discrimination=1.1,
                q_matrix={"set_basic": 1.0}
            ),
            Question(
                id="q003",
                type=QuestionType.SINGLE_CHOICE,
                content="函数 f: A→B 的定义要求什么？",
                options=[
                    {"id": "A", "text": "A中的每个元素对应B中的多个元素"},
                    {"id": "B", "text": "A中的每个元素对应B中的唯一元素"},
                    {"id": "C", "text": "B中的每个元素都必须是像"},
                    {"id": "D", "text": "A和B必须是数集"}
                ],
                correct_answer="B",
                explanation="函数要求定义域中每个元素对应值域中的唯一元素",
                knowledge_tags=["function_basic"],
                knowledge_level=0,
                difficulty=-0.2,
                discrimination=1.2,
                q_matrix={"function_basic": 1.0}
            ),
            
            # L1 题目
            Question(
                id="q101",
                type=QuestionType.SINGLE_CHOICE,
                content="ZFC公理系统中，哪个公理保证了无限集的存在？",
                options=[
                    {"id": "A", "text": "空集公理"},
                    {"id": "B", "text": "无限公理"},
                    {"id": "C", "text": "幂集公理"},
                    {"id": "D", "text": "选择公理"}
                ],
                correct_answer="B",
                explanation="无限公理直接断言了无限集的存在",
                knowledge_tags=["set_axioms"],
                knowledge_level=1,
                difficulty=0.2,
                discrimination=1.3,
                q_matrix={"set_axioms": 1.0}
            ),
            Question(
                id="q102",
                type=QuestionType.FILL_BLANK,
                content="Dedekind分割将有理数集Q划分为两个非空子集A和B，使得____。",
                correct_answer="A中所有元素小于B中所有元素",
                explanation="Dedekind分割的核心是有序划分",
                knowledge_tags=["real_numbers"],
                knowledge_level=1,
                difficulty=0.5,
                discrimination=1.2,
                q_matrix={"real_numbers": 1.0}
            ),
            
            # L2 题目
            Question(
                id="q201",
                type=QuestionType.SINGLE_CHOICE,
                content="连续统假设(CH)与ZFC公理系统的关系是？",
                options=[
                    {"id": "A", "text": "CH可由ZFC证明"},
                    {"id": "B", "text": "CH的否定可由ZFC证明"},
                    {"id": "C", "text": "CH与ZFC独立"},
                    {"id": "D", "text": "CH与ZFC矛盾"}
                ],
                correct_answer="C",
                explanation="Cohen证明了CH与ZFC独立",
                knowledge_tags=["continuum_hypothesis"],
                knowledge_level=2,
                difficulty=1.2,
                discrimination=1.5,
                q_matrix={"continuum_hypothesis": 1.0, "set_axioms": 0.3}
            ),
            Question(
                id="q202",
                type=QuestionType.SINGLE_CHOICE,
                content="下列哪个命题与选择公理等价？",
                options=[
                    {"id": "A", "text": "良序定理"},
                    {"id": "B", "text": "鸽笼原理"},
                    {"id": "C", "text": "数学归纳法"},
                    {"id": "D", "text": "抽屉原理"}
                ],
                correct_answer="A",
                explanation="良序定理、Zorn引理、Tukey引理都与AC等价",
                knowledge_tags=["axiom_of_choice"],
                knowledge_level=2,
                difficulty=1.0,
                discrimination=1.4,
                q_matrix={"axiom_of_choice": 1.0}
            ),
            
            # L3 题目
            Question(
                id="q301",
                type=QuestionType.SINGLE_CHOICE,
                content="力迫法(forcing)主要用于解决什么问题？",
                options=[
                    {"id": "A", "text": "证明定理"},
                    {"id": "B", "text": "证明独立性"},
                    {"id": "C", "text": "构造模型"},
                    {"id": "D", "text": "以上都是"}
                ],
                correct_answer="D",
                explanation="力迫法是一种构造模型证明独立性的强有力工具",
                knowledge_tags=["forcing"],
                knowledge_level=3,
                difficulty=1.8,
                discrimination=1.6,
                q_matrix={"forcing": 1.0, "continuum_hypothesis": 0.5}
            ),
            Question(
                id="q302",
                type=QuestionType.SINGLE_CHOICE,
                content="可测基数(measurable cardinal)的存在性意味着什么？",
                options=[
                    {"id": "A", "text": "V = L"},
                    {"id": "B", "text": "存在非可构造集"},
                    {"id": "C", "text": "ZFC不一致"},
                    {"id": "D", "text": "CH成立"}
                ],
                correct_answer="B",
                explanation="可测基数的存在性超越可构造宇宙L",
                knowledge_tags=["large_cardinals"],
                knowledge_level=3,
                difficulty=2.0,
                discrimination=1.7,
                q_matrix={"large_cardinals": 1.0}
            ),
        ]
        
        for q in questions:
            self.questions[q.id] = q
    
    def _init_sample_user(self):
        """初始化示例用户"""
        user = User(
            id="user_demo",
            username="demo_user",
            email="demo@example.com",
            profile=UserProfile(
                nickname="数学学习者",
                grade="大学",
                major="数学",
                learning_goal="掌握数学基础概念"
            )
        )
        self.users[user.id] = user
    
    # 用户相关方法
    def get_user(self, user_id: str) -> Optional[User]:
        return self.users.get(user_id)
    
    def save_user(self, user: User):
        self.users[user.id] = user
    
    # 题目相关方法
    def get_question(self, question_id: str) -> Optional[Question]:
        return self.questions.get(question_id)
    
    def get_all_questions(self) -> List[Question]:
        return list(self.questions.values())
    
    def save_question(self, question: Question):
        self.questions[question.id] = question
    
    # 会话相关方法
    def get_session(self, session_id: str) -> Optional[DiagnosisSession]:
        return self.sessions.get(session_id)
    
    def save_session(self, session: DiagnosisSession):
        self.sessions[session.id] = session
    
    # 报告相关方法
    def get_report(self, report_id: str) -> Optional[DiagnosisReport]:
        return self.reports.get(report_id)
    
    def get_report_by_diagnosis_id(self, diagnosis_id: str) -> Optional[DiagnosisReport]:
        for report in self.reports.values():
            if report.diagnosis_id == diagnosis_id:
                return report
        return None
    
    def get_user_reports(self, user_id: str, limit: int = 10, offset: int = 0) -> List[DiagnosisReport]:
        reports = [r for r in self.reports.values() if r.user_id == user_id]
        reports.sort(key=lambda x: x.created_at, reverse=True)
        return reports[offset:offset + limit]
    
    def count_user_reports(self, user_id: str) -> int:
        return len([r for r in self.reports.values() if r.user_id == user_id])
    
    def save_report(self, report: DiagnosisReport):
        self.reports[report.id] = report
    
    # 知识图谱相关方法
    def get_knowledge_graph(self) -> KnowledgeGraph:
        return self.knowledge_graph
    
    def get_all_knowledge_tags(self) -> List[KnowledgeTag]:
        return list(self.knowledge_tags.values())
