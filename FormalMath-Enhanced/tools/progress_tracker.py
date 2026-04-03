#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
学习进度追踪器 (Progress Tracker)

功能:
- 记录用户学习进度
- 生成学习报告
- 推荐下一步学习内容

使用示例:
    python progress_tracker.py --init
    python progress_tracker.py --complete "IMO 2023 P1" --domain algebra
    python progress_tracker.py --report weekly
    python progress_tracker.py --recommend --level intermediate

作者: FormalMath-Enhanced
版本: 1.0.0
"""

import argparse
import json
import os
from pathlib import Path
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, asdict, field
from enum import Enum
import math


class ProficiencyLevel(Enum):
    """熟练度等级"""
    BEGINNER = 1
    INTERMEDIATE = 2
    ADVANCED = 3
    EXPERT = 4


class TopicStatus(Enum):
    """主题状态"""
    NOT_STARTED = "not_started"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    MASTERED = "mastered"


@dataclass
class LearningEntry:
    """学习记录条目"""
    topic: str
    domain: str
    status: str
    started_at: Optional[str] = None
    completed_at: Optional[str] = None
    time_spent_minutes: int = 0
    attempts: int = 0
    success_count: int = 0
    difficulty: int = 3
    notes: str = ""
    tags: List[str] = field(default_factory=list)


@dataclass
class UserProfile:
    """用户学习档案"""
    user_id: str
    created_at: str
    last_active: str
    total_study_time: int = 0  # 分钟
    current_streak: int = 0
    longest_streak: int = 0
    level: str = "beginner"
    preferences: Dict = field(default_factory=dict)
    completed_topics: Set[str] = field(default_factory=set)
    in_progress_topics: Set[str] = field(default_factory=set)


@dataclass
class DailyActivity:
    """每日活动记录"""
    date: str
    study_minutes: int = 0
    topics_completed: List[str] = field(default_factory=list)
    topics_started: List[str] = field(default_factory=list)


class ProgressDatabase:
    """进度数据库"""

    def __init__(self, data_dir: Optional[Path] = None):
        self.data_dir = data_dir or Path.home() / ".formalmath"
        self.data_dir.mkdir(exist_ok=True)

        self.entries_file = self.data_dir / "learning_entries.json"
        self.profile_file = self.data_dir / "user_profile.json"
        self.activity_file = self.data_dir / "daily_activity.json"

        self.entries: List[LearningEntry] = []
        self.profile: Optional[UserProfile] = None
        self.activities: Dict[str, DailyActivity] = {}

        self._load_data()

    def _load_data(self) -> None:
        """加载数据"""
        # 加载学习记录
        if self.entries_file.exists():
            try:
                with open(self.entries_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    self.entries = [LearningEntry(**e) for e in data]
            except Exception as e:
                print(f"警告: 无法加载学习记录: {e}")

        # 加载用户档案
        if self.profile_file.exists():
            try:
                with open(self.profile_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    # 处理集合类型
                    data['completed_topics'] = set(data.get('completed_topics', []))
                    data['in_progress_topics'] = set(data.get('in_progress_topics', []))
                    self.profile = UserProfile(**data)
            except Exception as e:
                print(f"警告: 无法加载用户档案: {e}")

        # 加载活动记录
        if self.activity_file.exists():
            try:
                with open(self.activity_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    self.activities = {
                        k: DailyActivity(**v) for k, v in data.items()
                    }
            except Exception as e:
                print(f"警告: 无法加载活动记录: {e}")

    def _save_data(self) -> None:
        """保存数据"""
        # 保存学习记录
        with open(self.entries_file, 'w', encoding='utf-8') as f:
            json.dump([asdict(e) for e in self.entries], f, indent=2, ensure_ascii=False)

        # 保存用户档案
        if self.profile:
            profile_data = asdict(self.profile)
            profile_data['completed_topics'] = list(profile_data['completed_topics'])
            profile_data['in_progress_topics'] = list(profile_data['in_progress_topics'])
            with open(self.profile_file, 'w', encoding='utf-8') as f:
                json.dump(profile_data, f, indent=2, ensure_ascii=False)

        # 保存活动记录
        with open(self.activity_file, 'w', encoding='utf-8') as f:
            json.dump(
                {k: asdict(v) for k, v in self.activities.items()},
                f, indent=2, ensure_ascii=False
            )

    def init_profile(self, user_id: str = "default") -> UserProfile:
        """初始化用户档案"""
        now = datetime.now().isoformat()
        self.profile = UserProfile(
            user_id=user_id,
            created_at=now,
            last_active=now,
            preferences={
                'domains': ['algebra', 'geometry', 'number_theory', 'combinatorics'],
                'difficulty_preference': 'adaptive',
                'study_goal_minutes': 60
            }
        )
        self._save_data()
        return self.profile

    def add_entry(self, entry: LearningEntry) -> None:
        """添加学习记录"""
        # 检查是否已存在
        existing = next((e for e in self.entries if e.topic == entry.topic), None)

        if existing:
            # 更新现有记录
            existing.status = entry.status
            existing.time_spent_minutes += entry.time_spent_minutes
            existing.attempts += entry.attempts
            existing.success_count += entry.success_count
            if entry.completed_at:
                existing.completed_at = entry.completed_at
            if entry.notes:
                existing.notes = entry.notes
        else:
            self.entries.append(entry)

        # 更新用户档案
        if self.profile:
            if entry.status == "completed":
                self.profile.completed_topics.add(entry.topic)
                self.profile.in_progress_topics.discard(entry.topic)
            elif entry.status == "in_progress":
                self.profile.in_progress_topics.add(entry.topic)

            self.profile.total_study_time += entry.time_spent_minutes
            self.profile.last_active = datetime.now().isoformat()

        # 更新今日活动
        self._update_today_activity(entry)

        self._save_data()

    def _update_today_activity(self, entry: LearningEntry) -> None:
        """更新今日活动"""
        today = datetime.now().strftime('%Y-%m-%d')

        if today not in self.activities:
            self.activities[today] = DailyActivity(date=today)

        activity = self.activities[today]
        activity.study_minutes += entry.time_spent_minutes

        if entry.status == "completed" and entry.topic not in activity.topics_completed:
            activity.topics_completed.append(entry.topic)

        if entry.status == "in_progress" and entry.topic not in activity.topics_started:
            activity.topics_started.append(entry.topic)

    def get_entry(self, topic: str) -> Optional[LearningEntry]:
        """获取学习记录"""
        return next((e for e in self.entries if e.topic == entry.topic), None)

    def get_domain_stats(self) -> Dict[str, Dict]:
        """获取领域统计"""
        stats = {}

        for entry in self.entries:
            domain = entry.domain
            if domain not in stats:
                stats[domain] = {
                    'total': 0,
                    'completed': 0,
                    'in_progress': 0,
                    'total_time': 0
                }

            stats[domain]['total'] += 1
            stats[domain]['total_time'] += entry.time_spent_minutes

            if entry.status == "completed":
                stats[domain]['completed'] += 1
            elif entry.status == "in_progress":
                stats[domain]['in_progress'] += 1

        return stats

    def calculate_streak(self) -> int:
        """计算连续学习天数"""
        if not self.activities:
            return 0

        streak = 0
        today = datetime.now().date()

        for i in range(365):  # 检查最近一年
            date = today - timedelta(days=i)
            date_str = date.strftime('%Y-%m-%d')

            if date_str in self.activities:
                activity = self.activities[date_str]
                if activity.study_minutes > 0:
                    streak += 1
                else:
                    break
            elif i == 0:
                # 今天还没有记录
                continue
            else:
                break

        return streak


class ReportGenerator:
    """报告生成器"""

    def __init__(self, database: ProgressDatabase):
        self.db = database

    def generate_daily_report(self, date: Optional[str] = None) -> str:
        """生成日报"""
        date = date or datetime.now().strftime('%Y-%m-%d')

        if date not in self.db.activities:
            return f"# 学习日报 ({date})\n\n今天还没有学习记录。加油！"

        activity = self.db.activities[date]

        report = f"""# 学习日报 ({date})

## 今日统计

- 学习时长: {activity.study_minutes} 分钟
- 完成主题: {len(activity.topics_completed)} 个
- 开始主题: {len(activity.topics_started)} 个

"""

        if activity.topics_completed:
            report += "### 已完成\n\n"
            for topic in activity.topics_completed:
                report += f"- ✅ {topic}\n"
            report += "\n"

        if activity.topics_started:
            report += "### 新开始\n\n"
            for topic in activity.topics_started:
                report += f"- 📝 {topic}\n"

        return report

    def generate_weekly_report(self, week_start: Optional[str] = None) -> str:
        """生成周报"""
        if week_start:
            start_date = datetime.strptime(week_start, '%Y-%m-%d')
        else:
            today = datetime.now()
            start_date = today - timedelta(days=today.weekday())

        end_date = start_date + timedelta(days=6)

        # 收集本周数据
        total_minutes = 0
        total_completed = 0
        daily_data = []

        for i in range(7):
            date = (start_date + timedelta(days=i)).strftime('%Y-%m-%d')
            if date in self.db.activities:
                activity = self.db.activities[date]
                total_minutes += activity.study_minutes
                total_completed += len(activity.topics_completed)
                daily_data.append((date, activity.study_minutes))
            else:
                daily_data.append((date, 0))

        # 生成报告
        report = f"""# 学习周报 ({start_date.strftime('%Y-%m-%d')} ~ {end_date.strftime('%Y-%m-%d')})

## 本周统计

| 指标 | 数值 |
|------|------|
| 总学习时长 | {total_minutes} 分钟 ({total_minutes//60}小时{total_minutes%60}分钟) |
| 完成主题数 | {total_completed} 个 |
| 平均每日 | {total_minutes//7} 分钟 |
| 活跃天数 | {sum(1 for _, m in daily_data if m > 0)} 天 |

## 每日分布

"""

        # 简单的ASCII图表
        max_minutes = max(m for _, m in daily_data) if daily_data else 1
        for date, minutes in daily_data:
            bar_length = int((minutes / max(max_minutes, 1)) * 30)
            bar = '█' * bar_length
            report += f"{date}: {bar} {minutes}分钟\n"

        # 领域统计
        domain_stats = self.db.get_domain_stats()
        if domain_stats:
            report += "\n## 各领域进度\n\n"
            report += "| 领域 | 总数 | 已完成 | 进行中 | 完成率 |\n"
            report += "|------|------|--------|--------|--------|\n"

            for domain, stats in sorted(domain_stats.items()):
                completion_rate = stats['completed'] / max(stats['total'], 1) * 100
                report += f"| {domain} | {stats['total']} | {stats['completed']} | "
                report += f"{stats['in_progress']} | {completion_rate:.1f}% |\n"

        return report

    def generate_summary_report(self) -> str:
        """生成总览报告"""
        profile = self.db.profile

        if not profile:
            return "请先初始化用户档案: python progress_tracker.py --init"

        # 计算连续天数
        streak = self.db.calculate_streak()

        report = f"""# 学习进度总览

## 基本信息

- 用户ID: {profile.user_id}
- 加入时间: {profile.created_at[:10]}
- 当前等级: {profile.level.upper()}
- 当前连续: {'🔥' * min(streak, 10)} {streak} 天
- 最长连续: {profile.longest_streak} 天

## 学习统计

| 指标 | 数值 |
|------|------|
| 总学习时长 | {profile.total_study_time} 分钟 ({profile.total_study_time//60}小时) |
| 完成主题 | {len(profile.completed_topics)} 个 |
| 进行中 | {len(profile.in_progress_topics)} 个 |
| 学习记录 | {len(self.db.entries)} 条 |

## 进行中的主题

"""

        if profile.in_progress_topics:
            for topic in list(profile.in_progress_topics)[:10]:
                entry = next((e for e in self.db.entries if e.topic == topic), None)
                if entry:
                    progress = entry.success_count / max(entry.attempts, 1) * 100
                    report += f"- {topic} (进度: {progress:.0f}%)\n"
        else:
            report += "暂无进行中的主题\n"

        # 领域分布
        domain_stats = self.db.get_domain_stats()
        if domain_stats:
            report += "\n## 领域分布\n\n"
            for domain, stats in sorted(domain_stats.items(),
                                      key=lambda x: x[1]['completed'],
                                      reverse=True):
                report += f"- **{domain}**: {stats['completed']}/{stats['total']} 完成\n"

        return report


class RecommendationEngine:
    """推荐引擎"""

    def __init__(self, database: ProgressDatabase):
        self.db = database

    def recommend(self, level: Optional[str] = None, count: int = 5) -> List[Dict]:
        """
        推荐学习内容

        Args:
            level: 难度等级
            count: 推荐数量

        Returns:
            推荐列表
        """
        profile = self.db.profile
        if not profile:
            return []

        # 基于领域的推荐
        domain_stats = self.db.get_domain_stats()

        # 找出薄弱领域
        weak_domains = []
        for domain, stats in domain_stats.items():
            completion_rate = stats['completed'] / max(stats['total'], 1)
            if completion_rate < 0.5:
                weak_domains.append(domain)

        # 如果没有数据，推荐所有领域
        if not domain_stats:
            weak_domains = profile.preferences.get('domains', ['algebra'])

        recommendations = []

        # 推荐1: 继续未完成的内容
        in_progress = list(profile.in_progress_topics)[:2]
        for topic in in_progress:
            recommendations.append({
                'type': 'continue',
                'topic': topic,
                'reason': '继续您正在学习的内容',
                'priority': 'high'
            })

        # 推荐2: 薄弱领域的基础内容
        for domain in weak_domains[:2]:
            recommendations.append({
                'type': 'new',
                'topic': f'{domain}_fundamentals',
                'domain': domain,
                'reason': f'加强{domain}基础',
                'priority': 'medium'
            })

        # 推荐3: 挑战题目
        completed_count = len(profile.completed_topics)
        if completed_count > 10:
            recommendations.append({
                'type': 'challenge',
                'topic': 'advanced_problem_set',
                'reason': f'您已完成{completed_count}个主题，尝试挑战更高难度',
                'priority': 'low'
            })

        return recommendations[:count]

    def generate_study_plan(self, days: int = 7) -> str:
        """生成学习计划"""
        profile = self.db.profile
        if not profile:
            return "请先初始化用户档案"

        recommendations = self.recommend(count=7)

        plan = f"""# {days}天学习计划

根据您的学习进度生成的个性化计划：

"""

        for i, rec in enumerate(recommendations[:days], 1):
            emoji = {'high': '🔥', 'medium': '📚', 'low': '💡'}.get(rec['priority'], '📝')
            plan += f"## 第{i}天 {emoji}\n\n"
            plan += f"**内容**: {rec['topic']}\n\n"
            plan += f"**原因**: {rec['reason']}\n\n"
            plan += f"**建议时长**: {profile.preferences.get('study_goal_minutes', 60)} 分钟\n\n"
            plan += "---\n\n"

        return plan


def main():
    parser = argparse.ArgumentParser(
        description="学习进度追踪器",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s --init
  %(prog)s --complete "IMO 2023 P1" --domain algebra --time 90
  %(prog)s --start "Real Analysis Ch1" --domain analysis
  %(prog)s --report weekly
  %(prog)s --report summary
  %(prog)s --recommend --level intermediate
  %(prog)s --plan --days 7
        """
    )

    parser.add_argument('--init', action='store_true',
                       help='初始化用户档案')
    parser.add_argument('--complete', '-c', type=str,
                       help='标记主题为已完成')
    parser.add_argument('--start', '-s', type=str,
                       help='开始学习新主题')
    parser.add_argument('--domain', '-d', type=str,
                       help='主题领域')
    parser.add_argument('--time', '-t', type=int, default=0,
                       help='学习时长（分钟）')
    parser.add_argument('--notes', '-n', type=str,
                       help='学习笔记')
    parser.add_argument('--report', '-r', type=str,
                       choices=['daily', 'weekly', 'summary'],
                       help='生成报告')
    parser.add_argument('--recommend', action='store_true',
                       help='推荐学习内容')
    parser.add_argument('--level', '-l', type=str,
                       choices=['beginner', 'intermediate', 'advanced', 'expert'],
                       help='难度等级')
    parser.add_argument('--plan', '-p', action='store_true',
                       help='生成学习计划')
    parser.add_argument('--days', type=int, default=7,
                       help='计划天数')
    parser.add_argument('--output', '-o', type=Path,
                       help='输出文件路径')

    args = parser.parse_args()

    # 初始化数据库
    db = ProgressDatabase()

    # 初始化档案
    if args.init:
        profile = db.init_profile()
        print("✅ 用户档案已初始化")
        print(f"数据存储位置: {db.data_dir}")
        return 0

    # 检查是否已初始化
    if not db.profile:
        print("请先运行: python progress_tracker.py --init")
        return 1

    # 标记完成
    if args.complete:
        entry = LearningEntry(
            topic=args.complete,
            domain=args.domain or "general",
            status="completed",
            completed_at=datetime.now().isoformat(),
            time_spent_minutes=args.time,
            notes=args.notes or ""
        )
        db.add_entry(entry)
        print(f"✅ 已标记完成: {args.complete}")
        return 0

    # 开始新主题
    if args.start:
        entry = LearningEntry(
            topic=args.start,
            domain=args.domain or "general",
            status="in_progress",
            started_at=datetime.now().isoformat(),
            time_spent_minutes=args.time,
            notes=args.notes or ""
        )
        db.add_entry(entry)
        print(f"📝 开始学习: {args.start}")
        return 0

    # 生成报告
    if args.report:
        generator = ReportGenerator(db)

        if args.report == 'daily':
            report = generator.generate_daily_report()
        elif args.report == 'weekly':
            report = generator.generate_weekly_report()
        else:  # summary
            report = generator.generate_summary_report()

        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"报告已保存: {args.output}")
        else:
            print(report)
        return 0

    # 推荐
    if args.recommend:
        engine = RecommendationEngine(db)
        recommendations = engine.recommend(level=args.level, count=5)

        print("\n📚 为您推荐：\n")
        for i, rec in enumerate(recommendations, 1):
            priority_emoji = {'high': '🔥', 'medium': '📚', 'low': '💡'}.get(rec['priority'], '📝')
            print(f"{i}. {priority_emoji} {rec['topic']}")
            print(f"   原因: {rec['reason']}")
            print()
        return 0

    # 生成计划
    if args.plan:
        engine = RecommendationEngine(db)
        plan = engine.generate_study_plan(days=args.days)

        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(plan)
            print(f"学习计划已保存: {args.output}")
        else:
            print(plan)
        return 0

    # 默认显示摘要
    generator = ReportGenerator(db)
    print(generator.generate_summary_report())

    return 0


if __name__ == '__main__':
    exit(main())
