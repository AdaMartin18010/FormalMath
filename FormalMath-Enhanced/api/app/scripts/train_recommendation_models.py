"""
推荐模型训练脚本
训练协同过滤、知识图谱嵌入等模型
"""
import argparse
import os
import sys
import logging
import numpy as np
import torch
from datetime import datetime
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker

# 添加父目录到路径
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from core.config import settings
from core.database import Base
from models.models import User, KnowledgeGraphNode, KnowledgeGraphRelation, UserProgress
from recommendation.collaborative_filtering import CollaborativeFiltering
from recommendation.knowledge_embedding import KnowledgeGraphEmbedding

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def create_session():
    """创建数据库会话"""
    engine = create_engine(settings.DATABASE_URL)
    SessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=engine)
    return SessionLocal()


def train_collaborative_filtering(args):
    """训练协同过滤模型"""
    logger.info("=" * 50)
    logger.info("开始训练协同过滤模型")
    logger.info("=" * 50)
    
    db = create_session()
    
    try:
        cf = CollaborativeFiltering(db)
        
        # 构建用户-项目矩阵
        logger.info("构建用户-项目矩阵...")
        cf.build_user_item_matrix()
        
        if cf.user_item_matrix is None or cf.user_item_matrix.shape[0] == 0:
            logger.error("用户-项目矩阵为空，无法训练")
            return
        
        logger.info(f"矩阵形状: {cf.user_item_matrix.shape}")
        
        # 计算用户相似度
        logger.info("计算用户相似度...")
        cf.compute_user_similarity(k=args.cf_k_neighbors)
        
        # 训练矩阵分解
        logger.info(f"训练NMF模型 (n_components={args.cf_n_components})...")
        cf.train_matrix_factorization(
            n_components=args.cf_n_components,
            max_iter=args.cf_max_iter
        )
        
        # 评估模型
        logger.info("评估模型性能...")
        metrics = cf.evaluate_model(test_ratio=0.2)
        logger.info(f"评估结果: RMSE={metrics.get('rmse', 'N/A')}, MAE={metrics.get('mae', 'N/A')}")
        
        # 保存模型
        model_path = os.path.join(args.output_dir, "cf_model.pkl")
        import pickle
        with open(model_path, 'wb') as f:
            pickle.dump({
                'user_factors': cf.user_factors,
                'item_factors': cf.item_factors,
                'user_id_map': cf.user_id_map,
                'item_id_map': cf.item_id_map,
                'user_similarity_matrix': cf.user_similarity_matrix
            }, f)
        logger.info(f"协同过滤模型已保存到: {model_path}")
        
    finally:
        db.close()


def train_knowledge_graph_embedding(args):
    """训练知识图谱嵌入模型"""
    logger.info("=" * 50)
    logger.info("开始训练知识图谱嵌入模型")
    logger.info("=" * 50)
    
    db = create_session()
    
    try:
        # 初始化模型
        kg = KnowledgeGraphEmbedding(
            db, 
            model_type=args.kg_model_type,
            embedding_dim=args.kg_embedding_dim
        )
        
        # 加载知识图谱
        logger.info("加载知识图谱数据...")
        kg.load_knowledge_graph()
        
        # 构建模型
        logger.info(f"构建{args.kg_model_type}模型...")
        kg.build_model()
        
        # 训练模型
        device = "cuda" if torch.cuda.is_available() and args.use_gpu else "cpu"
        logger.info(f"使用设备: {device}")
        
        logger.info(f"开始训练 (epochs={args.kg_epochs}, batch_size={args.kg_batch_size})...")
        losses = kg.train(
            epochs=args.kg_epochs,
            batch_size=args.kg_batch_size,
            lr=args.kg_learning_rate,
            negative_samples=args.kg_negative_samples,
            device=device
        )
        
        # 保存训练曲线
        loss_path = os.path.join(args.output_dir, f"{args.kg_model_type}_losses.txt")
        with open(loss_path, 'w') as f:
            for i, loss in enumerate(losses):
                f.write(f"Epoch {i+1}: {loss:.6f}\n")
        
        # 保存模型
        model_path = os.path.join(args.output_dir, f"{args.kg_model_type}_model.pt")
        kg.save_model(model_path)
        
        # 测试相似度计算
        logger.info("测试语义相似度计算...")
        concepts = db.query(KnowledgeGraphNode).limit(5).all()
        if len(concepts) >= 2:
            sim = kg.compute_semantic_similarity(concepts[0].id, concepts[1].id)
            logger.info(f"{concepts[0].name} vs {concepts[1].name}: 相似度={sim:.4f}")
        
    finally:
        db.close()


def generate_training_report(args, start_time):
    """生成训练报告"""
    report_path = os.path.join(args.output_dir, "training_report.md")
    
    with open(report_path, 'w') as f:
        f.write("# 推荐模型训练报告\n\n")
        f.write(f"训练时间: {start_time.strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        f.write("## 协同过滤模型\n\n")
        f.write(f"- 算法: NMF矩阵分解\n")
        f.write(f"- 隐因子维度: {args.cf_n_components}\n")
        f.write(f"- 最近邻数量: {args.cf_k_neighbors}\n")
        f.write(f"- 最大迭代次数: {args.cf_max_iter}\n\n")
        
        f.write("## 知识图谱嵌入模型\n\n")
        f.write(f"- 模型类型: {args.kg_model_type.upper()}\n")
        f.write(f"- 嵌入维度: {args.kg_embedding_dim}\n")
        f.write(f"- 训练轮数: {args.kg_epochs}\n")
        f.write(f"- 批次大小: {args.kg_batch_size}\n")
        f.write(f"- 学习率: {args.kg_learning_rate}\n")
        f.write(f"- 负采样数: {args.kg_negative_samples}\n\n")
        
        f.write("## 输出文件\n\n")
        f.write("- `cf_model.pkl`: 协同过滤模型\n")
        f.write(f"- `{args.kg_model_type}_model.pt`: 知识图谱嵌入模型\n")
        f.write(f"- `{args.kg_model_type}_losses.txt`: 训练损失曲线\n")
    
    logger.info(f"训练报告已保存到: {report_path}")


def main():
    parser = argparse.ArgumentParser(description='训练推荐模型')
    
    # 通用参数
    parser.add_argument('--output-dir', type=str, default='./models',
                        help='模型输出目录')
    parser.add_argument('--use-gpu', action='store_true',
                        help='使用GPU训练')
    
    # 协同过滤参数
    parser.add_argument('--train-cf', action='store_true',
                        help='训练协同过滤模型')
    parser.add_argument('--cf-n-components', type=int, default=50,
                        help='NMF隐因子维度')
    parser.add_argument('--cf-k-neighbors', type=int, default=50,
                        help='K近邻数量')
    parser.add_argument('--cf-max-iter', type=int, default=500,
                        help='NMF最大迭代次数')
    
    # 知识图谱嵌入参数
    parser.add_argument('--train-kg', action='store_true',
                        help='训练知识图谱嵌入模型')
    parser.add_argument('--kg-model-type', type=str, default='rotate',
                        choices=['transe', 'rotate'],
                        help='知识图谱嵌入模型类型')
    parser.add_argument('--kg-embedding-dim', type=int, default=128,
                        help='嵌入维度')
    parser.add_argument('--kg-epochs', type=int, default=1000,
                        help='训练轮数')
    parser.add_argument('--kg-batch-size', type=int, default=256,
                        help='批次大小')
    parser.add_argument('--kg-learning-rate', type=float, default=0.001,
                        help='学习率')
    parser.add_argument('--kg-negative-samples', type=int, default=10,
                        help='负采样数量')
    
    # 默认训练所有
    parser.add_argument('--train-all', action='store_true',
                        help='训练所有模型')
    
    args = parser.parse_args()
    
    # 如果没有指定，默认训练所有
    if not args.train_cf and not args.train_kg and not args.train_all:
        args.train_all = True
    
    if args.train_all:
        args.train_cf = True
        args.train_kg = True
    
    # 创建输出目录
    os.makedirs(args.output_dir, exist_ok=True)
    
    start_time = datetime.now()
    
    # 训练协同过滤
    if args.train_cf:
        train_collaborative_filtering(args)
    
    # 训练知识图谱嵌入
    if args.train_kg:
        train_knowledge_graph_embedding(args)
    
    # 生成报告
    generate_training_report(args, start_time)
    
    logger.info("=" * 50)
    logger.info("所有训练任务完成!")
    logger.info("=" * 50)


if __name__ == "__main__":
    main()
