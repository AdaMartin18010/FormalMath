"""
Celery Worker 启动脚本

使用方法:
    python celery_worker.py
    
或使用Celery命令:
    celery -A app.tasks.celery_app worker --loglevel=info --queues=default,path_calculation,diagnosis,graph_analysis
    
启动多个队列:
    celery -A app.tasks.celery_app worker -Q path_calculation -n path_worker@%h --loglevel=info
    celery -A app.tasks.celery_app worker -Q diagnosis -n diagnosis_worker@%h --loglevel=info
"""
import os
import sys

# 添加项目根目录到路径
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from app.tasks.celery_app import celery_app


if __name__ == "__main__":
    # 使用Celery命令行启动
    import subprocess
    
    # 默认队列配置
    queues = "default,path_calculation,diagnosis,graph_analysis"
    concurrency = 4
    loglevel = "info"
    
    # 解析命令行参数
    args = sys.argv[1:]
    if "--queues" in args:
        idx = args.index("--queues")
        queues = args[idx + 1]
    
    if "--concurrency" in args:
        idx = args.index("--concurrency")
        concurrency = int(args[idx + 1])
    
    if "--loglevel" in args:
        idx = args.index("--loglevel")
        loglevel = args[idx + 1]
    
    # 构建命令
    cmd = [
        "celery",
        "-A", "app.tasks.celery_app",
        "worker",
        "--queues", queues,
        "--concurrency", str(concurrency),
        "--loglevel", loglevel,
        "-n", "formalmath_worker@%h"
    ]
    
    print(f"启动Celery Worker...")
    print(f"队列: {queues}")
    print(f"并发数: {concurrency}")
    print(f"日志级别: {loglevel}")
    print("=" * 50)
    
    # 启动Worker
    subprocess.run(cmd)
