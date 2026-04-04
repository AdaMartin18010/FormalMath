"""
学习路径计算异步任务
"""
import logging
from typing import List, Dict, Any
from celery import current_task
from .celery_app import celery_app

logger = logging.getLogger(__name__)


@celery_app.task(bind=True, max_retries=3, default_retry_delay=60)
def calculate_learning_path(
    self,
    user_id: int,
    target_concepts: List[str],
    algorithm: str = "astar",
    constraints: Dict[str, Any] = None
) -> Dict[str, Any]:
    """
    计算学习路径的异步任务
    
    Args:
        user_id: 用户ID
        target_concepts: 目标概念列表
        algorithm: 路径算法 (astar, dp, dijkstra)
        constraints: 约束条件
    
    Returns:
        计算结果包含路径、估计时间、难度分布等
    """
    try:
        # 更新任务状态
        self.update_state(
            state='PROGRESS',
            meta={'progress': 10, 'message': '正在加载知识图谱...'}
        )
        
        # 模拟知识图谱加载
        import time
        time.sleep(1)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 30, 'message': '分析用户当前水平...'}
        )
        
        # 模拟用户水平分析
        time.sleep(1)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 50, 'message': f'使用{algorithm}算法计算最优路径...'}
        )
        
        # 执行路径计算
        path_result = _compute_path_internal(
            user_id=user_id,
            target_concepts=target_concepts,
            algorithm=algorithm,
            constraints=constraints
        )
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 90, 'message': '保存计算结果...'}
        )
        
        # 保存到数据库
        _save_path_result(user_id, path_result)
        
        self.update_state(
            state='SUCCESS',
            meta={'progress': 100, 'message': '计算完成'}
        )
        
        return {
            "status": "completed",
            "task_id": self.request.id,
            "path_id": path_result.get("path_id"),
            "nodes_count": len(path_result.get("nodes", [])),
            "estimated_duration": path_result.get("estimated_duration"),
            "difficulty_distribution": path_result.get("difficulty_distribution"),
        }
        
    except Exception as exc:
        logger.error(f"路径计算失败: {exc}")
        # 重试逻辑
        if self.request.retries < self.max_retries:
            raise self.retry(exc=exc, countdown=60)
        raise


@celery_app.task(bind=True, max_retries=2)
def optimize_learning_path(
    self,
    path_id: int,
    optimization_type: str = "difficulty"
) -> Dict[str, Any]:
    """
    优化现有学习路径
    
    Args:
        path_id: 路径ID
        optimization_type: 优化类型 (difficulty, time, balance)
    """
    try:
        self.update_state(state='PROGRESS', meta={'progress': 20, 'message': '加载路径数据...'})
        
        # 加载路径
        path_data = _load_path_data(path_id)
        
        self.update_state(state='PROGRESS', meta={'progress': 50, 'message': '执行优化...'})
        
        # 执行优化
        optimized = _optimize_path_internal(path_data, optimization_type)
        
        self.update_state(state='PROGRESS', meta={'progress': 80, 'message': '保存优化结果...'})
        
        # 保存结果
        _save_optimized_path(path_id, optimized)
        
        return {
            "status": "completed",
            "task_id": self.request.id,
            "path_id": path_id,
            "improvements": optimized.get("improvements", []),
            "new_estimated_duration": optimized.get("estimated_duration"),
        }
        
    except Exception as exc:
        logger.error(f"路径优化失败: {exc}")
        raise self.retry(exc=exc, countdown=30)


@celery_app.task(bind=True)
def batch_generate_paths(
    self,
    user_ids: List[int],
    target_branch: str,
    algorithm: str = "astar"
) -> Dict[str, Any]:
    """
    批量生成学习路径
    
    Args:
        user_ids: 用户ID列表
        target_branch: 目标学科分支
        algorithm: 路径算法
    """
    total = len(user_ids)
    results = []
    
    for i, user_id in enumerate(user_ids):
        progress = int((i / total) * 100)
        self.update_state(
            state='PROGRESS',
            meta={
                'progress': progress,
                'message': f'处理用户 {user_id} ({i+1}/{total})...',
                'current': i + 1,
                'total': total
            }
        )
        
        try:
            # 获取用户目标概念
            target_concepts = _get_branch_concepts(target_branch)
            
            # 计算路径
            result = calculate_learning_path.apply_async(
                args=[user_id, target_concepts, algorithm],
                queue='path_calculation'
            )
            
            results.append({
                "user_id": user_id,
                "task_id": result.id,
                "status": "queued"
            })
            
        except Exception as e:
            results.append({
                "user_id": user_id,
                "error": str(e),
                "status": "failed"
            })
    
    return {
        "status": "completed",
        "total": total,
        "successful": len([r for r in results if r.get("status") == "queued"]),
        "failed": len([r for r in results if r.get("status") == "failed"]),
        "results": results
    }


# ============ 内部辅助函数 ============

def _compute_path_internal(
    user_id: int,
    target_concepts: List[str],
    algorithm: str,
    constraints: Dict[str, Any]
) -> Dict[str, Any]:
    """内部路径计算逻辑"""
    # 这里应该是实际的路径计算算法
    # 现在使用模拟数据
    import random
    
    nodes = []
    for i, concept in enumerate(target_concepts):
        nodes.append({
            "id": f"node_{i}",
            "concept_id": concept,
            "order": i,
            "estimated_time": random.randint(30, 120)
        })
    
    total_time = sum(n["estimated_time"] for n in nodes)
    
    return {
        "path_id": random.randint(1000, 9999),
        "user_id": user_id,
        "algorithm": algorithm,
        "nodes": nodes,
        "estimated_duration": total_time,
        "difficulty_distribution": {
            "basic": random.randint(2, 5),
            "intermediate": random.randint(3, 7),
            "advanced": random.randint(1, 4)
        }
    }


def _save_path_result(user_id: int, result: Dict[str, Any]):
    """保存路径结果到数据库"""
    # 实际实现应写入数据库
    logger.info(f"保存用户 {user_id} 的路径计算结果")


def _load_path_data(path_id: int) -> Dict[str, Any]:
    """加载路径数据"""
    # 从数据库加载
    return {"path_id": path_id, "nodes": []}


def _optimize_path_internal(path_data: Dict[str, Any], optimization_type: str) -> Dict[str, Any]:
    """路径优化逻辑"""
    return {
        "improvements": [f"基于{optimization_type}的优化"],
        "estimated_duration": path_data.get("estimated_duration", 0) * 0.9
    }


def _save_optimized_path(path_id: int, optimized: Dict[str, Any]):
    """保存优化后的路径"""
    logger.info(f"保存优化后的路径 {path_id}")


def _get_branch_concepts(branch: str) -> List[str]:
    """获取学科分支的概念列表"""
    # 从知识图谱获取
    return [f"{branch}_concept_{i}" for i in range(1, 6)]
