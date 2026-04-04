"""
异步任务模块
"""
from .celery_app import celery_app
from .path_tasks import calculate_learning_path, optimize_learning_path
from .diagnosis_tasks import perform_cognitive_diagnosis
from .graph_tasks import analyze_knowledge_graph

__all__ = [
    "celery_app",
    "calculate_learning_path",
    "optimize_learning_path",
    "perform_cognitive_diagnosis",
    "analyze_knowledge_graph",
]
