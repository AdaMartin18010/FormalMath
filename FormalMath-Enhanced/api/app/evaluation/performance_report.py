"""
推荐系统性能评估报告
"""
import numpy as np
import pandas as pd
from typing import Dict, List, Any
from dataclasses import dataclass
from datetime import datetime
import json


@dataclass
class EvaluationMetrics:
    """评估指标"""
    precision_at_k: Dict[int, float]
    recall_at_k: Dict[int, float]
    ndcg_at_k: Dict[int, float]
    coverage: float
    diversity: float
    novelty: float


class PerformanceEvaluator:
    """性能评估器"""
    
    def __init__(self):
        self.results = {}
    
    def calculate_precision_at_k(self, recommendations: List[List[str]], 
                                  ground_truth: List[List[str]], k: int) -> float:
        """计算Precision@K"""
        precisions = []
        for rec, truth in zip(recommendations, ground_truth):
            if len(rec) == 0:
                continue
            hits = len(set(rec[:k]) & set(truth))
            precisions.append(hits / min(k, len(rec)))
        return np.mean(precisions) if precisions else 0.0
    
    def calculate_recall_at_k(self, recommendations: List[List[str]], 
                              ground_truth: List[List[str]], k: int) -> float:
        """计算Recall@K"""
        recalls = []
        for rec, truth in zip(recommendations, ground_truth):
            if len(truth) == 0:
                continue
            hits = len(set(rec[:k]) & set(truth))
            recalls.append(hits / len(truth))
        return np.mean(recalls) if recalls else 0.0
    
    def calculate_ndcg_at_k(self, recommendations: List[List[str]], 
                            ground_truth: List[List[str]], k: int) -> float:
        """计算NDCG@K"""
        ndcgs = []
        for rec, truth in zip(recommendations, ground_truth):
            if not rec or not truth:
                continue
            
            # DCG
            dcg = 0.0
            for i, item in enumerate(rec[:k]):
                if item in truth:
                    dcg += 1.0 / np.log2(i + 2)
            
            # IDCG
            idcg = sum(1.0 / np.log2(i + 2) for i in range(min(len(truth), k)))
            
            ndcg = dcg / idcg if idcg > 0 else 0.0
            ndcgs.append(ndcg)
        
        return np.mean(ndcgs) if ndcgs else 0.0
    
    def calculate_coverage(self, all_recommendations: List[List[str]], 
                          all_items: set) -> float:
        """计算覆盖率"""
        recommended_items = set()
        for recs in all_recommendations:
            recommended_items.update(recs)
        return len(recommended_items) / len(all_items) if all_items else 0.0
    
    def calculate_diversity(self, recommendations: List[List[str]],
                           item_features: Dict[str, np.ndarray]) -> float:
        """计算推荐多样性（基于物品特征的平均相似度）"""
        diversities = []
        for rec in recommendations:
            if len(rec) < 2:
                continue
            
            similarities = []
            for i in range(len(rec)):
                for j in range(i + 1, len(rec)):
                    feat_i = item_features.get(rec[i])
                    feat_j = item_features.get(rec[j])
                    if feat_i is not None and feat_j is not None:
                        sim = np.dot(feat_i, feat_j) / (np.linalg.norm(feat_i) * np.linalg.norm(feat_j) + 1e-8)
                        similarities.append(sim)
            
            if similarities:
                # 多样性 = 1 - 平均相似度
                diversities.append(1 - np.mean(similarities))
        
        return np.mean(diversities) if diversities else 0.0
    
    def generate_report(self, metrics: EvaluationMetrics, 
                       output_path: str = None) -> str:
        """生成评估报告"""
        report = []
        report.append("# 推荐系统性能评估报告")
        report.append(f"\n生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        
        report.append("## 准确性指标\n")
        report.append("| 指标 | @5 | @10 | @20 |")
        report.append("|------|-----|-----|-----|")
        
        precision_row = "| Precision |"
        recall_row = "| Recall |"
        ndcg_row = "| NDCG |"
        
        for k in [5, 10, 20]:
            precision_row += f" {metrics.precision_at_k.get(k, 0):.4f} |"
            recall_row += f" {metrics.recall_at_k.get(k, 0):.4f} |"
            ndcg_row += f" {metrics.ndcg_at_k.get(k, 0):.4f} |"
        
        report.append(precision_row)
        report.append(recall_row)
        report.append(ndcg_row)
        
        report.append("\n## 覆盖性与多样性\n")
        report.append(f"- **覆盖率**: {metrics.coverage:.4f}")
        report.append(f"- **多样性**: {metrics.diversity:.4f}")
        report.append(f"- **新颖性**: {metrics.novelty:.4f}")
        
        report.append("\n## 指标说明\n")
        report.append("- **Precision@K**: 推荐列表中相关项目的比例")
        report.append("- **Recall@K**: 相关项目被推荐的比例")
        report.append("- **NDCG@K**: 考虑排序位置的归一化折损累计增益")
        report.append("- **覆盖率**: 推荐系统能覆盖的物品比例")
        report.append("- **多样性**: 推荐列表中物品的差异化程度")
        report.append("- **新颖性**: 推荐物品的新颖程度")
        
        report_text = "\n".join(report)
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(report_text)
        
        return report_text


def generate_comparison_report(results: Dict[str, EvaluationMetrics],
                               output_path: str = None) -> str:
    """生成多模型对比报告"""
    report = []
    report.append("# 推荐算法性能对比报告")
    report.append(f"\n生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    
    # 创建对比表格
    report.append("## Precision@10 对比\n")
    report.append("| 算法 | Precision@10 | Recall@10 | NDCG@10 | 覆盖率 |")
    report.append("|------|-------------|-----------|---------|--------|")
    
    for algo_name, metrics in results.items():
        row = f"| {algo_name} |"
        row += f" {metrics.precision_at_k.get(10, 0):.4f} |"
        row += f" {metrics.recall_at_k.get(10, 0):.4f} |"
        row += f" {metrics.ndcg_at_k.get(10, 0):.4f} |"
        row += f" {metrics.coverage:.4f} |"
        report.append(row)
    
    report.append("\n## 综合评价\n")
    
    # 找出最佳算法
    best_precision = max(results.items(), 
                        key=lambda x: x[1].precision_at_k.get(10, 0))
    best_recall = max(results.items(), 
                     key=lambda x: x[1].recall_at_k.get(10, 0))
    best_ndcg = max(results.items(), 
                   key=lambda x: x[1].ndcg_at_k.get(10, 0))
    
    report.append(f"- **最佳精确率**: {best_precision[0]}")
    report.append(f"- **最佳召回率**: {best_recall[0]}")
    report.append(f"- **最佳NDCG**: {best_ndcg[0]}")
    
    report_text = "\n".join(report)
    
    if output_path:
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_text)
    
    return report_text


# 生成示例报告
if __name__ == "__main__":
    # 创建示例指标
    metrics = EvaluationMetrics(
        precision_at_k={5: 0.35, 10: 0.28, 20: 0.22},
        recall_at_k={5: 0.15, 10: 0.25, 20: 0.38},
        ndcg_at_k={5: 0.38, 10: 0.32, 20: 0.28},
        coverage=0.65,
        diversity=0.72,
        novelty=0.58
    )
    
    evaluator = PerformanceEvaluator()
    report = evaluator.generate_report(metrics, "performance_report.md")
    print(report)
