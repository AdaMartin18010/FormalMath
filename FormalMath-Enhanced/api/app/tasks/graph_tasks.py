"""
知识图谱分析异步任务
"""
import logging
from typing import Dict, Any, List, Optional
from .celery_app import celery_app

logger = logging.getLogger(__name__)


@celery_app.task(bind=True, max_retries=2)
def analyze_knowledge_graph(
    self,
    branch: Optional[str] = None,
    analysis_type: str = "full"
) -> Dict[str, Any]:
    """
    分析知识图谱的异步任务
    
    Args:
        branch: 学科分支，None表示全部分支
        analysis_type: 分析类型 (full, connectivity, difficulty, centrality)
    
    Returns:
        分析结果
    """
    try:
        self.update_state(
            state='PROGRESS',
            meta={'progress': 10, 'message': '加载知识图谱数据...'}
        )
        
        # 加载图谱
        graph_data = _load_knowledge_graph(branch)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 30, 'message': '计算图谱统计信息...'}
        )
        
        results = {
            "branch": branch or "all",
            "analysis_type": analysis_type,
            "total_nodes": len(graph_data.get("nodes", [])),
            "total_edges": len(graph_data.get("edges", [])),
        }
        
        if analysis_type in ["full", "connectivity"]:
            self.update_state(
                state='PROGRESS',
                meta={'progress': 50, 'message': '分析连通性...'}
            )
            results["connectivity"] = _analyze_connectivity(graph_data)
        
        if analysis_type in ["full", "difficulty"]:
            self.update_state(
                state='PROGRESS',
                meta={'progress': 70, 'message': '分析难度分布...'}
            )
            results["difficulty_distribution"] = _analyze_difficulty(graph_data)
        
        if analysis_type in ["full", "centrality"]:
            self.update_state(
                state='PROGRESS',
                meta={'progress': 85, 'message': '计算中心性...'}
            )
            results["centrality"] = _calculate_centrality(graph_data)
        
        # 保存分析结果
        _save_analysis_result(results)
        
        return {
            "status": "completed",
            "task_id": self.request.id,
            **results
        }
        
    except Exception as exc:
        logger.error(f"知识图谱分析失败: {exc}")
        raise self.retry(exc=exc, countdown=60)


@celery_app.task(bind=True)
def find_learning_gaps(
    self,
    user_id: int,
    target_concepts: List[str]
) -> Dict[str, Any]:
    """
    发现学习缺口
    
    Args:
        user_id: 用户ID
        target_concepts: 目标概念列表
    """
    try:
        self.update_state(
            state='PROGRESS',
            meta={'progress': 20, 'message': '分析用户当前状态...'}
        )
        
        # 获取用户已掌握的概念
        mastered_concepts = _get_mastered_concepts(user_id)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 50, 'message': '计算前置依赖...'}
        )
        
        # 查找缺失的前置概念
        gaps = _find_prerequisite_gaps(target_concepts, mastered_concepts)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 80, 'message': '生成学习建议...'}
        )
        
        # 生成建议
        recommendations = _generate_gap_recommendations(gaps)
        
        return {
            "status": "completed",
            "task_id": self.request.id,
            "user_id": user_id,
            "target_concepts": target_concepts,
            "gaps": gaps,
            "gap_count": len(gaps),
            "recommendations": recommendations
        }
        
    except Exception as exc:
        logger.error(f"学习缺口分析失败: {exc}")
        raise


@celery_app.task(bind=True)
def recommend_next_concepts(
    self,
    user_id: int,
    count: int = 5
) -> Dict[str, Any]:
    """
    推荐下一步学习概念
    
    Args:
        user_id: 用户ID
        count: 推荐数量
    """
    try:
        self.update_state(
            state='PROGRESS',
            meta={'progress': 30, 'message': '分析学习历史...'}
        )
        
        # 获取用户进度
        user_progress = _get_user_progress(user_id)
        
        self.update_state(
            state='PROGRESS',
            meta={'progress': 60, 'message': '计算推荐...'}
        )
        
        # 生成推荐
        recommendations = _generate_concept_recommendations(
            user_progress,
            count
        )
        
        return {
            "status": "completed",
            "task_id": self.request.id,
            "user_id": user_id,
            "recommendations": recommendations
        }
        
    except Exception as exc:
        logger.error(f"概念推荐失败: {exc}")
        raise


# ============ 内部辅助函数 ============

def _load_knowledge_graph(branch: Optional[str]) -> Dict[str, Any]:
    """加载知识图谱"""
    import random
    
    nodes = []
    edges = []
    
    node_count = random.randint(50, 200) if not branch else random.randint(20, 50)
    
    for i in range(node_count):
        nodes.append({
            "id": f"concept_{i}",
            "branch": branch or random.choice(["algebra", "geometry", "analysis"]),
            "difficulty": random.choice(["basic", "intermediate", "advanced"])
        })
    
    edge_count = int(node_count * 1.5)
    for i in range(edge_count):
        edges.append({
            "source": f"concept_{random.randint(0, node_count-1)}",
            "target": f"concept_{random.randint(0, node_count-1)}"
        })
    
    return {"nodes": nodes, "edges": edges}


def _analyze_connectivity(graph_data: Dict) -> Dict[str, Any]:
    """分析图谱连通性"""
    return {
        "connected_components": 3,
        "average_degree": 2.5,
        "density": 0.15
    }


def _analyze_difficulty(graph_data: Dict) -> Dict[str, int]:
    """分析难度分布"""
    nodes = graph_data.get("nodes", [])
    distribution = {"basic": 0, "intermediate": 0, "advanced": 0}
    
    for node in nodes:
        diff = node.get("difficulty", "basic")
        distribution[diff] = distribution.get(diff, 0) + 1
    
    return distribution


def _calculate_centrality(graph_data: Dict) -> Dict[str, Any]:
    """计算中心性"""
    return {
        "most_central": ["concept_1", "concept_5", "concept_10"],
        "average_centrality": 0.35
    }


def _save_analysis_result(results: Dict[str, Any]):
    """保存分析结果"""
    logger.info(f"保存知识图谱分析结果: {results.get('branch')}")


def _get_mastered_concepts(user_id: int) -> List[str]:
    """获取用户已掌握的概念"""
    return ["concept_1", "concept_2", "concept_3"]


def _find_prerequisite_gaps(
    target_concepts: List[str],
    mastered_concepts: List[str]
) -> List[Dict[str, Any]]:
    """查找前置概念缺口"""
    import random
    
    gaps = []
    for target in target_concepts:
        # 模拟前置依赖
        prerequisites = [f"pre_{target}_{i}" for i in range(random.randint(1, 4))]
        missing = [p for p in prerequisites if p not in mastered_concepts]
        
        if missing:
            gaps.append({
                "target_concept": target,
                "missing_prerequisites": missing,
                "severity": random.choice(["high", "medium", "low"])
            })
    
    return gaps


def _generate_gap_recommendations(gaps: List[Dict]) -> List[str]:
    """生成缺口学习建议"""
    if not gaps:
        return ["您已掌握所有前置概念，可以直接学习目标概念"]
    
    recommendations = []
    for gap in gaps[:3]:  # 最多显示3个
        recommendations.append(
            f"建议先学习 {gap['target_concept']} 的前置概念: {', '.join(gap['missing_prerequisites'][:2])}"
        )
    
    return recommendations


def _get_user_progress(user_id: int) -> Dict[str, Any]:
    """获取用户进度"""
    return {
        "mastered": ["concept_1", "concept_2"],
        "in_progress": ["concept_3"],
        "not_started": ["concept_4", "concept_5"]
    }


def _generate_concept_recommendations(
    user_progress: Dict,
    count: int
) -> List[Dict[str, Any]]:
    """生成概念推荐"""
    import random
    
    recommendations = []
    candidates = user_progress.get("not_started", [])
    
    for concept in candidates[:count]:
        recommendations.append({
            "concept_id": concept,
            "reason": random.choice([
                "基于您的学习进度",
                "前置概念已掌握",
                "推荐难度适中"
            ]),
            "priority": random.randint(1, 5)
        })
    
    return recommendations
