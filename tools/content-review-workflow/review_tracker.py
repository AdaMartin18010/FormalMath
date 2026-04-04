#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
审核状态追踪系统
Review Status Tracker

管理内容审核的全生命周期状态追踪。
"""

import json
import os
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, asdict, field
from datetime import datetime
from enum import Enum
import threading
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ReviewStatus(Enum):
    """审核状态枚举"""
    PENDING = "pending"
    IN_REVIEW = "in_review"
    NEEDS_REVISION = "needs_revision"
    APPROVED = "approved"
    PUBLISHED = "published"
    REJECTED = "rejected"


@dataclass
class ReviewEvent:
    """审核事件记录"""
    timestamp: str
    status: str
    reviewer: Optional[str]
    comment: Optional[str]
    action: str


@dataclass
class ReviewRecord:
    """审核记录"""
    document_id: str
    document_path: str
    submitter: str
    submit_time: str
    current_status: str
    assigned_reviewer: Optional[str] = None
    review_level: str = "level_1_auto"
    events: List[ReviewEvent] = field(default_factory=list)
    metadata: Dict = field(default_factory=dict)
    
    def to_dict(self) -> Dict:
        return {
            "document_id": self.document_id,
            "document_path": self.document_path,
            "submitter": self.submitter,
            "submit_time": self.submit_time,
            "current_status": self.current_status,
            "assigned_reviewer": self.assigned_reviewer,
            "review_level": self.review_level,
            "events": [asdict(e) for e in self.events],
            "metadata": self.metadata
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'ReviewRecord':
        events = [ReviewEvent(**e) for e in data.get('events', [])]
        return cls(
            document_id=data['document_id'],
            document_path=data['document_path'],
            submitter=data['submitter'],
            submit_time=data['submit_time'],
            current_status=data['current_status'],
            assigned_reviewer=data.get('assigned_reviewer'),
            review_level=data.get('review_level', 'level_1_auto'),
            events=events,
            metadata=data.get('metadata', {})
        )


class ReviewTracker:
    """审核状态追踪器"""
    
    def __init__(self, storage_path: Optional[str] = None):
        """
        初始化审核追踪器
        
        Args:
            storage_path: 审核记录存储路径
        """
        if storage_path is None:
            storage_path = Path(__file__).parent / "data" / "review_records.json"
        
        self.storage_path = Path(storage_path)
        self.storage_path.parent.mkdir(parents=True, exist_ok=True)
        
        self.records: Dict[str, ReviewRecord] = {}
        self.lock = threading.Lock()
        
        self._load_records()
    
    def _load_records(self):
        """加载审核记录"""
        if self.storage_path.exists():
            try:
                with open(self.storage_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    for doc_id, record_data in data.items():
                        self.records[doc_id] = ReviewRecord.from_dict(record_data)
                logger.info(f"已加载 {len(self.records)} 条审核记录")
            except Exception as e:
                logger.error(f"加载审核记录失败: {e}")
    
    def _save_records(self):
        """保存审核记录"""
        try:
            data = {doc_id: record.to_dict() for doc_id, record in self.records.items()}
            with open(self.storage_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            logger.error(f"保存审核记录失败: {e}")
    
    def create_record(self, document_path: str, submitter: str, 
                     review_level: str = "level_1_auto") -> ReviewRecord:
        """
        创建新的审核记录
        
        Args:
            document_path: 文档路径
            submitter: 提交者
            review_level: 审核级别
            
        Returns:
            ReviewRecord: 新创建的审核记录
        """
        doc_id = self._generate_doc_id(document_path)
        
        with self.lock:
            if doc_id in self.records:
                logger.warning(f"审核记录已存在: {doc_id}")
                return self.records[doc_id]
            
            now = datetime.now().isoformat()
            record = ReviewRecord(
                document_id=doc_id,
                document_path=document_path,
                submitter=submitter,
                submit_time=now,
                current_status=ReviewStatus.PENDING.value,
                review_level=review_level,
                events=[
                    ReviewEvent(
                        timestamp=now,
                        status=ReviewStatus.PENDING.value,
                        reviewer=None,
                        comment="文档提交，等待审核",
                        action="submit"
                    )
                ]
            )
            
            self.records[doc_id] = record
            self._save_records()
            logger.info(f"创建审核记录: {doc_id}")
            
            return record
    
    def update_status(self, document_id: str, new_status: ReviewStatus,
                     reviewer: Optional[str] = None, comment: Optional[str] = None) -> bool:
        """
        更新审核状态
        
        Args:
            document_id: 文档ID
            new_status: 新状态
            reviewer: 审核员
            comment: 备注
            
        Returns:
            bool: 是否成功更新
        """
        with self.lock:
            if document_id not in self.records:
                logger.error(f"审核记录不存在: {document_id}")
                return False
            
            record = self.records[document_id]
            old_status = record.current_status
            
            # 验证状态转换
            if not self._is_valid_transition(old_status, new_status.value):
                logger.error(f"无效的状态转换: {old_status} -> {new_status.value}")
                return False
            
            now = datetime.now().isoformat()
            record.current_status = new_status.value
            
            # 如果是审核中状态，记录审核员
            if new_status == ReviewStatus.IN_REVIEW:
                record.assigned_reviewer = reviewer
            
            record.events.append(ReviewEvent(
                timestamp=now,
                status=new_status.value,
                reviewer=reviewer,
                comment=comment,
                action="status_change"
            ))
            
            self._save_records()
            logger.info(f"状态更新: {document_id} {old_status} -> {new_status.value}")
            
            return True
    
    def get_record(self, document_id: str) -> Optional[ReviewRecord]:
        """
        获取审核记录
        
        Args:
            document_id: 文档ID
            
        Returns:
            Optional[ReviewRecord]: 审核记录
        """
        return self.records.get(document_id)
    
    def get_record_by_path(self, document_path: str) -> Optional[ReviewRecord]:
        """
        通过路径获取审核记录
        
        Args:
            document_path: 文档路径
            
        Returns:
            Optional[ReviewRecord]: 审核记录
        """
        doc_id = self._generate_doc_id(document_path)
        return self.get_record(doc_id)
    
    def query_records(self, status: Optional[ReviewStatus] = None,
                     reviewer: Optional[str] = None,
                     submitter: Optional[str] = None) -> List[ReviewRecord]:
        """
        查询审核记录
        
        Args:
            status: 状态筛选
            reviewer: 审核员筛选
            submitter: 提交者筛选
            
        Returns:
            List[ReviewRecord]: 审核记录列表
        """
        results = []
        
        for record in self.records.values():
            if status and record.current_status != status.value:
                continue
            if reviewer and record.assigned_reviewer != reviewer:
                continue
            if submitter and record.submitter != submitter:
                continue
            results.append(record)
        
        return results
    
    def get_statistics(self) -> Dict[str, Any]:
        """
        获取审核统计信息
        
        Returns:
            Dict: 统计信息
        """
        stats = {
            "total": len(self.records),
            "by_status": {},
            "by_reviewer": {},
            "pending_aging": []
        }
        
        now = datetime.now()
        
        for record in self.records.values():
            # 按状态统计
            status = record.current_status
            stats["by_status"][status] = stats["by_status"].get(status, 0) + 1
            
            # 按审核员统计
            if record.assigned_reviewer:
                reviewer = record.assigned_reviewer
                stats["by_reviewer"][reviewer] = stats["by_reviewer"].get(reviewer, 0) + 1
            
            # 计算待审核文档的等待时间
            if status == ReviewStatus.PENDING.value:
                submit_time = datetime.fromisoformat(record.submit_time)
                wait_hours = (now - submit_time).total_seconds() / 3600
                if wait_hours > 24:  # 超过24小时
                    stats["pending_aging"].append({
                        "document_id": record.document_id,
                        "wait_hours": round(wait_hours, 2)
                    })
        
        # 按等待时间排序
        stats["pending_aging"].sort(key=lambda x: x["wait_hours"], reverse=True)
        
        return stats
    
    def assign_reviewer(self, document_id: str, reviewer: str) -> bool:
        """
        分配审核员
        
        Args:
            document_id: 文档ID
            reviewer: 审核员
            
        Returns:
            bool: 是否成功分配
        """
        with self.lock:
            if document_id not in self.records:
                return False
            
            record = self.records[document_id]
            old_reviewer = record.assigned_reviewer
            record.assigned_reviewer = reviewer
            
            record.events.append(ReviewEvent(
                timestamp=datetime.now().isoformat(),
                status=record.current_status,
                reviewer=reviewer,
                comment=f"分配给审核员: {reviewer}",
                action="assign"
            ))
            
            self._save_records()
            logger.info(f"分配审核员: {document_id} {old_reviewer} -> {reviewer}")
            
            return True
    
    def add_comment(self, document_id: str, comment: str, 
                   reviewer: Optional[str] = None) -> bool:
        """
        添加审核评论
        
        Args:
            document_id: 文档ID
            comment: 评论内容
            reviewer: 评论者
            
        Returns:
            bool: 是否成功添加
        """
        with self.lock:
            if document_id not in self.records:
                return False
            
            record = self.records[document_id]
            record.events.append(ReviewEvent(
                timestamp=datetime.now().isoformat(),
                status=record.current_status,
                reviewer=reviewer,
                comment=comment,
                action="comment"
            ))
            
            self._save_records()
            return True
    
    def _generate_doc_id(self, document_path: str) -> str:
        """生成文档ID"""
        import hashlib
        # 使用路径的哈希作为ID
        return hashlib.md5(document_path.encode()).hexdigest()[:12]
    
    def _is_valid_transition(self, from_status: str, to_status: str) -> bool:
        """验证状态转换是否有效"""
        valid_transitions = {
            ReviewStatus.PENDING.value: [ReviewStatus.IN_REVIEW.value, ReviewStatus.REJECTED.value],
            ReviewStatus.IN_REVIEW.value: [ReviewStatus.APPROVED.value, ReviewStatus.NEEDS_REVISION.value, ReviewStatus.REJECTED.value],
            ReviewStatus.NEEDS_REVISION.value: [ReviewStatus.PENDING.value],
            ReviewStatus.APPROVED.value: [ReviewStatus.PUBLISHED.value],
            ReviewStatus.PUBLISHED.value: [],
            ReviewStatus.REJECTED.value: [ReviewStatus.PENDING.value]
        }
        
        return to_status in valid_transitions.get(from_status, [])
    
    def export_records(self, output_path: str, format: str = "json"):
        """
        导出审核记录
        
        Args:
            output_path: 输出路径
            format: 输出格式
        """
        data = [record.to_dict() for record in self.records.values()]
        
        if format == "json":
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        elif format == "csv":
            import csv
            with open(output_path, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow(["document_id", "document_path", "submitter", 
                               "submit_time", "current_status", "assigned_reviewer"])
                for record in self.records.values():
                    writer.writerow([
                        record.document_id,
                        record.document_path,
                        record.submitter,
                        record.submit_time,
                        record.current_status,
                        record.assigned_reviewer or ""
                    ])
        
        logger.info(f"审核记录已导出: {output_path}")


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(description='审核状态追踪系统')
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 创建记录
    create_parser = subparsers.add_parser('create', help='创建审核记录')
    create_parser.add_argument('document_path', help='文档路径')
    create_parser.add_argument('--submitter', '-s', required=True, help='提交者')
    create_parser.add_argument('--level', '-l', default='level_1_auto', help='审核级别')
    
    # 更新状态
    status_parser = subparsers.add_parser('status', help='更新审核状态')
    status_parser.add_argument('document_id', help='文档ID')
    status_parser.add_argument('new_status', choices=[s.value for s in ReviewStatus], help='新状态')
    status_parser.add_argument('--reviewer', '-r', help='审核员')
    status_parser.add_argument('--comment', '-c', help='备注')
    
    # 查询记录
    query_parser = subparsers.add_parser('query', help='查询审核记录')
    query_parser.add_argument('--status', choices=[s.value for s in ReviewStatus], help='状态筛选')
    query_parser.add_argument('--reviewer', '-r', help='审核员筛选')
    query_parser.add_argument('--submitter', '-s', help='提交者筛选')
    
    # 统计信息
    subparsers.add_parser('stats', help='显示统计信息')
    
    # 导出记录
    export_parser = subparsers.add_parser('export', help='导出审核记录')
    export_parser.add_argument('output', help='输出路径')
    export_parser.add_argument('--format', '-f', choices=['json', 'csv'], default='json', help='输出格式')
    
    args = parser.parse_args()
    
    tracker = ReviewTracker()
    
    if args.command == 'create':
        record = tracker.create_record(args.document_path, args.submitter, args.level)
        print(f"创建审核记录成功")
        print(f"文档ID: {record.document_id}")
        print(f"当前状态: {record.current_status}")
    
    elif args.command == 'status':
        success = tracker.update_status(
            args.document_id, 
            ReviewStatus(args.new_status),
            args.reviewer,
            args.comment
        )
        print(f"状态更新{'成功' if success else '失败'}")
    
    elif args.command == 'query':
        status = ReviewStatus(args.status) if args.status else None
        records = tracker.query_records(status, args.reviewer, args.submitter)
        print(f"找到 {len(records)} 条记录:")
        for r in records:
            print(f"  - {r.document_id}: {r.document_path} ({r.current_status})")
    
    elif args.command == 'stats':
        stats = tracker.get_statistics()
        print(json.dumps(stats, ensure_ascii=False, indent=2))
    
    elif args.command == 'export':
        tracker.export_records(args.output, args.format)
        print(f"导出完成: {args.output}")
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
