"""
Celery Beat 定时任务调度器

使用方法:
    python celery_beat.py
    
或使用Celery命令:
    celery -A app.tasks.celery_app beat --loglevel=info
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from app.tasks.celery_app import celery_app
from celery.schedules import crontab


# 配置定时任务
celery_app.conf.beat_schedule = {
    # 每小时清理过期缓存
    'cleanup-expired-cache': {
        'task': 'app.tasks.graph_tasks.analyze_knowledge_graph',
        'schedule': 3600.0,  # 每小时
        'args': (None, 'full'),
    },
    # 每天凌晨2点生成统计报告
    'daily-stats': {
        'task': 'app.tasks.graph_tasks.analyze_knowledge_graph',
        'schedule': crontab(hour=2, minute=0),
        'args': (None, 'full'),
    },
}

celery_app.conf.timezone = 'Asia/Shanghai'


if __name__ == "__main__":
    import subprocess
    
    cmd = [
        "celery",
        "-A", "app.tasks.celery_app",
        "beat",
        "--loglevel", "info"
    ]
    
    print("启动Celery Beat...")
    print("=" * 50)
    
    subprocess.run(cmd)
