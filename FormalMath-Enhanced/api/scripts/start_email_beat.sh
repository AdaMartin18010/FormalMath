#!/bin/bash
# ============================================
# 启动邮件通知定时任务调度器 (Celery Beat)
# ============================================

cd "$(dirname "$0")/.."

echo "Starting FormalMath Email Beat Scheduler..."
echo "============================================"

celery -A app.tasks.celery_app beat \
    -l info \
    --scheduler celery.beat.PersistentScheduler \
    --schedulefile celerybeat-schedule

echo "Email beat scheduler stopped."
