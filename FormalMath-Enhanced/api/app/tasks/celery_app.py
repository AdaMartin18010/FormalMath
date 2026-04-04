"""
Celery异步任务配置
用于处理耗时操作：学习路径计算、认知诊断等
"""
import os
from celery import Celery
from celery.signals import task_prerun, task_postrun, task_failure
from kombu import Queue, Exchange
from ..core.config import settings

# 创建Celery应用
celery_app = Celery(
    "formalmath",
    broker=settings.CELERY_BROKER_URL,
    backend=settings.CELERY_RESULT_BACKEND,
    include=[
        "app.tasks.path_tasks",
        "app.tasks.diagnosis_tasks",
        "app.tasks.graph_tasks",
        "app.notifications.email_tasks",
    ]
)

# Celery配置
celery_app.conf.update(
    # 序列化
    task_serializer=settings.CELERY_TASK_SERIALIZER,
    accept_content=settings.CELERY_ACCEPT_CONTENT,
    result_serializer=settings.CELERY_RESULT_SERIALIZER,
    
    # 时区
    timezone=settings.CELERY_TIMEZONE,
    enable_utc=settings.CELERY_ENABLE_UTC,
    
    # 任务跟踪
    task_track_started=settings.CELERY_TASK_TRACK_STARTED,
    task_time_limit=settings.CELERY_TASK_TIME_LIMIT,
    worker_prefetch_multiplier=settings.CELERY_WORKER_PREFETCH_MULTIPLIER,
    
    # 结果后端配置
    result_expires=3600 * 24,  # 结果保存24小时
    result_extended=True,
    
    # 任务队列配置
    task_default_queue='default',
    task_queues=(
        Queue('default', Exchange('default'), routing_key='default'),
        Queue('path_calculation', Exchange('path_calculation'), routing_key='path.calculation'),
        Queue('diagnosis', Exchange('diagnosis'), routing_key='diagnosis'),
        Queue('graph_analysis', Exchange('graph_analysis'), routing_key='graph.analysis'),
        Queue('email_notifications', Exchange('email_notifications'), routing_key='email.notifications'),
    ),
    
    # 路由配置
    task_routes={
        'app.tasks.path_tasks.*': {'queue': 'path_calculation'},
        'app.tasks.diagnosis_tasks.*': {'queue': 'diagnosis'},
        'app.tasks.graph_tasks.*': {'queue': 'graph_analysis'},
        'app.notifications.email_tasks.*': {'queue': 'email_notifications'},
    },
    
    # 重试配置
    task_acks_late=True,
    task_reject_on_worker_lost=True,
    
    # 并发配置
    worker_concurrency=4,
    worker_max_tasks_per_child=1000,
)


# ============ 任务信号处理 ============

@task_prerun.connect
def task_prerun_handler(task_id, task, args, kwargs, **extras):
    """任务开始前的处理"""
    print(f"任务开始: {task.name}[{task_id}]")


@task_postrun.connect
def task_postrun_handler(task_id, task, args, kwargs, retval, state, **extras):
    """任务完成后的处理"""
    print(f"任务完成: {task.name}[{task_id}] - 状态: {state}")


@task_failure.connect
def task_failure_handler(task_id, exception, args, kwargs, traceback, einfo, **extras):
    """任务失败时的处理"""
    print(f"任务失败: {task_id} - 错误: {exception}")


# ============ 健康检查任务 ============

@celery_app.task(bind=True, max_retries=3)
def health_check_task(self):
    """健康检查任务"""
    return {
        "status": "ok",
        "task_id": self.request.id,
        "worker": self.request.hostname,
    }
