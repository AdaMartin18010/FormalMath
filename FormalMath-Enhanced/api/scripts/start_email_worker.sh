#!/bin/bash
# ============================================
# 启动邮件通知 Celery Worker
# ============================================

cd "$(dirname "$0")/.."

echo "Starting FormalMath Email Notification Worker..."
echo "Queue: email_notifications"
echo "Log Level: info"
echo "============================================"

celery -A app.tasks.celery_app worker \
    -Q email_notifications \
    -n email_worker@%h \
    -l info \
    --concurrency=4 \
    --prefetch-multiplier=1 \
    -E  # 启用事件

echo "Email worker stopped."
